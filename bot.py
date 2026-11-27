import asyncio
import json
import logging
import os
import random
import tempfile
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlparse

from fpdf import FPDF
from telegram import Poll, PollAnswer, Update
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    PollAnswerHandler,
    filters,
)

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger("SanskariQuizBot")

DEFAULT_OWNER_ID = 8283878643
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
OWNER_ID = int(os.environ.get("OWNER_ID", str(DEFAULT_OWNER_ID)))
PORT = int(os.environ.get("PORT", "10000"))
WEBHOOK_URL = os.environ.get("WEBHOOK_URL", "").strip()


@dataclass
class QuestionItem:
    q_num: int
    question: str
    options: List[str]
    correct_idx: int
    explanation: str


@dataclass
class UserRecord:
    user_id: int
    name: str
    correct: int = 0
    wrong: int = 0
    score: float = 0.0
    mistakes: List[Tuple[int, str, str, str]] = field(default_factory=list)


@dataclass
class QuizSession:
    owner_id: int
    chat_id: int
    thread_id: Optional[int]
    questions: List[QuestionItem]
    delay_sec: int = 4
    timer_sec: int = 20
    neg_marking: float = 0.0
    shuffle_enabled: bool = False
    current_idx: int = 0
    paused: bool = False
    stopped: bool = False
    skip_current: bool = False
    active_poll_id: Optional[str] = None
    active_q_item: Optional[QuestionItem] = None
    poll_to_q: Dict[str, QuestionItem] = field(default_factory=dict)
    users: Dict[int, UserRecord] = field(default_factory=dict)
    runner_task: Optional[asyncio.Task] = None


class QuizManager:
    def __init__(self) -> None:
        self.default_delay: int = 4
        self.default_timer: int = 20
        self.default_neg: float = 0.0
        self.default_shuffle: bool = False
        self.default_target_chat: Optional[int] = None
        self.default_target_thread: Optional[int] = None
        self.session: Optional[QuizSession] = None
        self.last_pdf_path: Optional[str] = None
        self.last_pdf_caption: Optional[str] = None

    def cleanup_last_pdf(self) -> None:
        if self.last_pdf_path and os.path.exists(self.last_pdf_path):
            try:
                os.remove(self.last_pdf_path)
            except OSError:
                pass
        self.last_pdf_path = None
        self.last_pdf_caption = None


manager = QuizManager()


def is_owner(user_id: Optional[int]) -> bool:
    return user_id is not None and user_id == OWNER_ID


def safe_pdf_text(text: str) -> str:
    replacements = {
        "—": "-",
        "–": "-",
        "“": '"',
        "”": '"',
        "‘": "'",
        "’": "'",
        "•": "*",
        "→": "->",
        "✅": "[OK]",
        "❌": "[X]",
        "🏆": "[TOP]",
        "🥇": "[1st]",
        "🥈": "[2nd]",
        "🥉": "[3rd]",
        "📌": "*",
        "📄": "[PDF]",
    }
    for k, v in replacements.items():
        text = text.replace(k, v)
    return text.encode("latin-1", errors="replace").decode("latin-1")


def parse_questions_from_text(raw_text: str) -> List[QuestionItem]:
    items: List[QuestionItem] = []
    lines = [ln.strip() for ln in raw_text.splitlines() if ln.strip()]

    cur_q: Optional[str] = None
    cur_opts: List[str] = []
    cur_ans: Optional[int] = None
    cur_exp: str = ""

    def flush() -> None:
        nonlocal cur_q, cur_opts, cur_ans, cur_exp
        if cur_q and len(cur_opts) >= 2:
            ans_idx = cur_ans if cur_ans is not None and 0 <= cur_ans < len(cur_opts) else 0
            q_no = len(items) + 1
            exp_text = cur_exp.strip() or f"Sahi Uttar: {cur_opts[ans_idx]}"
            items.append(
                QuestionItem(
                    q_num=q_no,
                    question=cur_q.strip(),
                    options=cur_opts[:4],
                    correct_idx=ans_idx,
                    explanation=exp_text,
                )
            )
        cur_q = None
        cur_opts = []
        cur_ans = None
        cur_exp = ""

    opt_map = {"A": 0, "B": 1, "C": 2, "D": 3, "1": 0, "2": 1, "3": 2, "4": 3}

    for line in lines:
        low = line.lower()
        if low.startswith(("ans:", "answer:", "ans ", "answer ", "उत्तर:", "सही उत्तर:")):
            val = line.split(":", 1)[1].strip() if ":" in line else line.split(None, 1)[1].strip()
            first_ch = val[:1].upper()
            if first_ch in opt_map:
                cur_ans = opt_map[first_ch]
            continue

        if low.startswith(("exp:", "explanation:", "व्याख्या:", "नोट:")):
            cur_exp = line.split(":", 1)[1].strip() if ":" in line else line
            continue

        is_opt = False
        for prefix in ("a)", "b)", "c)", "d)", "a.", "b.", "c.", "d.", "(a)", "(b)", "(c)", "(d)"):
            if low.startswith(prefix):
                opt_text = line[len(prefix):].strip()
                if opt_text:
                    cur_opts.append(opt_text)
                    is_opt = True
                break
        if is_opt:
            continue

        if cur_opts:
            flush()
        if cur_q is None:
            cur_q = line
        else:
            cur_q = f"{cur_q} {line}"

    flush()
    return items


def parse_questions_from_json(raw_json: str) -> List[QuestionItem]:
    data = json.loads(raw_json)
    if isinstance(data, dict) and "questions" in data:
        data = data["questions"]
    if not isinstance(data, list):
        raise ValueError("JSON root must be a list of question objects.")

    items: List[QuestionItem] = []
    for idx, entry in enumerate(data, start=1):
        if not isinstance(entry, dict):
            continue
        q_text = str(entry.get("q") or entry.get("question") or "").strip()
        opts_raw = entry.get("options") or []
        if not q_text or not isinstance(opts_raw, list) or len(opts_raw) < 2:
            continue
        options = [str(o).strip() for o in opts_raw[:4] if str(o).strip()]
        if len(options) < 2:
            continue

        correct_val = entry.get("correct", entry.get("answer", 0))
        if isinstance(correct_val, int):
            correct_idx = correct_val if 0 <= correct_val < len(options) else 0
        else:
            s = str(correct_val).strip().upper()
            letter_map = {"A": 0, "B": 1, "C": 2, "D": 3, "0": 0, "1": 1, "2": 2, "3": 3}
            correct_idx = letter_map.get(s[:1], 0)
            if correct_idx >= len(options):
                correct_idx = 0

        exp_val = str(entry.get("explanation") or "").strip()
        if not exp_val:
            exp_val = f"Sahi Uttar: {options[correct_idx]}"

        items.append(
            QuestionItem(
                q_num=idx,
                question=q_text,
                options=options,
                correct_idx=correct_idx,
                explanation=exp_val,
            )
        )
    return items


def build_score_pdf(session: QuizSession) -> str:
    sorted_users = sorted(
        session.users.values(),
        key=lambda u: (-u.score, -u.correct, u.wrong, u.name.lower()),
    )
    total_q = len(session.questions)

    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=12)
    pdf.add_page()

    pdf.set_font("Helvetica", "B", 15)
    pdf.cell(0, 10, safe_pdf_text("SANSKARI QUIZ - COMPLETE SCORE REPORT"), ln=True, align="C")

    pdf.set_font("Helvetica", "", 10)
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    pdf.cell(
        0,
        7,
        safe_pdf_text(f"Total Questions: {total_q} | Participants: {len(sorted_users)} | Generated: {stamp}"),
        ln=True,
        align="C",
    )
    pdf.ln(3)

    pdf.set_font("Helvetica", "B", 9)
    pdf.set_fill_color(230, 232, 240)
    col_w = [12, 68, 22, 22, 24, 42]
    headers = ["Rank", "Name", "Sahi", "Galat", "Skipped", "Score"]
    for w, h in zip(col_w, headers):
        pdf.cell(w, 8, safe_pdf_text(h), border=1, align="C", fill=True)
    pdf.ln()

    pdf.set_font("Helvetica", "", 9)
    for rank, u in enumerate(sorted_users, start=1):
        skipped = max(0, total_q - (u.correct + u.wrong))
        score_str = f"{u.score:g}/{total_q}"
        row = [
            str(rank),
            u.name[:34],
            str(u.correct),
            str(u.wrong),
            str(skipped),
            score_str,
        ]
        for w, val in zip(col_w, row):
            align = "L" if w == 68 else "C"
            pdf.cell(w, 7, safe_pdf_text(val), border=1, align=align)
        pdf.ln()

    pdf.ln(5)
    pdf.set_font("Helvetica", "B", 11)
    pdf.cell(0, 8, safe_pdf_text("DETAILED BREAKDOWN & WRONG ANSWERS"), ln=True)

    for rank, u in enumerate(sorted_users, start=1):
        skipped = max(0, total_q - (u.correct + u.wrong))
        pdf.set_font("Helvetica", "B", 10)
        summary_line = (
            f"#{rank} {u.name}  |  Score: {u.score:g}/{total_q}  |  "
            f"Sahi: {u.correct}  |  Galat: {u.wrong}  |  Skipped: {skipped}"
        )
        pdf.multi_cell(0, 6, safe_pdf_text(summary_line))

        pdf.set_font("Helvetica", "", 9)
        if not u.mistakes:
            pdf.multi_cell(0, 5.5, safe_pdf_text("   - Koi question galat nahi hua."))
        else:
            for q_no, q_txt, chosen_opt, right_opt in u.mistakes:
                mistake_line = (
                    f"   - Q{q_no}: {q_txt}\n"
                    f"     Galat Uttar: {chosen_opt}  -->  Sahi Uttar: {right_opt}"
                )
                pdf.multi_cell(0, 5, safe_pdf_text(mistake_line))
        pdf.ln(2)

    fd, tmp_path = tempfile.mkstemp(prefix="sanskari_score_", suffix=".pdf")
    os.close(fd)
    pdf.output(tmp_path)
    return tmp_path


def format_top3_message(session: QuizSession) -> str:
    total_q = len(session.questions)
    sorted_users = sorted(
        session.users.values(),
        key=lambda u: (-u.score, -u.correct, u.wrong, u.name.lower()),
    )
    medals = [
        ("🥇", "गोल्ड मेडल"),
        ("🥈", "सिल्वर मेडल"),
        ("🥉", "ब्रॉन्ज़ मेडल"),
    ]

    lines = [
        "✨ 🏆 <b>संस्कारी क्विज़ — फ़ाइनल स्कोरबोर्ड</b> 🏆 ✨",
        f"📝 कुल प्रश्न: <b>{total_q}</b>  |  👥 कुल प्रतिभागी: <b>{len(sorted_users)}</b>",
        "",
    ]

    if not sorted_users:
        lines.append("<i>इस क्विज़ में किसी ने उत्तर दर्ज नहीं किया।</i>")
    else:
        for idx, u in enumerate(sorted_users[:3]):
            emoji, label = medals[idx]
            acc = (u.correct / total_q * 100.0) if total_q > 0 else 0.0
            lines.append(
                f"{emoji} <b>{label} — {u.name}</b>\n"
                f"    ⚡ स्कोर: <b>{u.score:g}/{total_q}</b>  |  "
                f"✅ <b>{u.correct}</b>  |  ❌ <b>{u.wrong}</b>  |  📊 <b>{acc:.1f}%</b>"
            )

    lines.extend(
        [
            "",
            "📌 <i>अपना स्कोर देखने के लिए <code>/myscore</code> कमांड का इस्तेमाल करें।</i>",
            "📄 <i>बाकी सभी प्रतिभागियों का पूरा स्कोर और ग़लत प्रश्नों की लिस्ट नीचे PDF में दी गई है।</i>",
        ]
    )
    return "\n".join(lines)


async def finish_session(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    top3_text = format_top3_message(session)
    send_kwargs = {"message_thread_id": session.thread_id} if session.thread_id else {}

    await context.bot.send_message(
        chat_id=session.chat_id,
        text=top3_text,
        parse_mode=ParseMode.HTML,
        **send_kwargs,
    )

    manager.cleanup_last_pdf()
    pdf_path = await asyncio.to_thread(build_score_pdf, session)
    caption = "📄 <b>संस्कारी क्विज़ — सम्पूर्ण स्कोर एवं ग़लत प्रश्नों की PDF</b>"

    try:
        with open(pdf_path, "rb") as f_doc:
            await context.bot.send_document(
                chat_id=session.chat_id,
                document=f_doc,
                filename="Sanskari_Quiz_Score_Report.pdf",
                caption=caption,
                parse_mode=ParseMode.HTML,
                **send_kwargs,
            )
    finally:
        if os.path.exists(pdf_path):
            try:
                os.remove(pdf_path)
            except OSError:
                pass


async def run_quiz_loop(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    total_q = len(session.questions)
    send_kwargs = {"message_thread_id": session.thread_id} if session.thread_id else {}

    try:
        while session.current_idx < total_q and not session.stopped:
            while session.paused and not session.stopped:
                await asyncio.sleep(0.5)
            if session.stopped:
                break

            item = session.questions[session.current_idx]
            display_no = session.current_idx + 1
            q_label = f"[{display_no}/{total_q}] {item.question}"[:300]
            opts = [opt[:100] for opt in item.options[:4]]

            exp_prefix = f"✅ Sahi Uttar: {item.options[item.correct_idx]}"
            exp_full = item.explanation if item.explanation else exp_prefix
            exp_text = f"{exp_full}"[:200]

            poll_msg = await context.bot.send_poll(
                chat_id=session.chat_id,
                question=q_label,
                options=opts,
                type=Poll.QUIZ,
                correct_option_id=item.correct_idx,
                explanation=exp_text,
                is_anonymous=False,
                open_period=session.timer_sec,
                **send_kwargs,
            )

            poll_id = poll_msg.poll.id
            session.active_poll_id = poll_id
            session.active_q_item = item
            session.poll_to_q[poll_id] = item

            elapsed = 0.0
            step = 0.25
            while elapsed < session.timer_sec and not session.stopped and not session.skip_current:
                if not session.paused:
                    elapsed += step
                await asyncio.sleep(step)

            if session.skip_current:
                session.skip_current = False

            session.current_idx += 1

            if session.stopped or session.current_idx >= total_q:
                break

            delay_elapsed = 0.0
            while delay_elapsed < session.delay_sec and not session.stopped:
                if not session.paused:
                    delay_elapsed += step
                await asyncio.sleep(step)

    except asyncio.CancelledError:
        session.stopped = True
    finally:
        session.stopped = True
        session.active_poll_id = None
        session.active_q_item = None
        await finish_session(session, context)
        if manager.session is session:
            manager.session = None


async def handle_poll_answer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    answer: PollAnswer = update.poll_answer
    if not answer or not manager.session:
        return

    session = manager.session
    item = session.poll_to_q.get(answer.poll_id)
    if not item or not answer.option_ids:
        return

    user = answer.user
    uid = user.id
    full_name = user.full_name or (f"@{user.username}" if user.username else f"User {uid}")

    if uid not in session.users:
        session.users[uid] = UserRecord(user_id=uid, name=full_name)
    else:
        session.users[uid].name = full_name

    rec = session.users[uid]
    chosen_idx = answer.option_ids[0]
    chosen_text = item.options[chosen_idx] if 0 <= chosen_idx < len(item.options) else "Unknown"
    right_text = item.options[item.correct_idx] if 0 <= item.correct_idx < len(item.options) else "Unknown"

    if chosen_idx == item.correct_idx:
        rec.correct += 1
        rec.score += 1.0
    else:
        rec.wrong += 1
        rec.score -= session.neg_marking
        rec.mistakes.append((item.q_num, item.question, chosen_text, right_text))


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return

    help_text = (
        "✨ 🛠️ <b>संस्कारी क्विज़ बॉट — ओनर कमांड मेन्यू</b> 🛠️ ✨\n\n"
        "🎯 <b>क्विज़ कंट्रोल कमांड्स:</b>\n"
        "• <code>/quiz</code> <i>(फ़ाइल के रिप्लाई में)</i> — क्विज़ फ़ाइल से एक-एक करके प्रश्न शुरू करना\n"
        "• <code>/pause</code> — चल रहे क्विज़ को अस्थायी रूप से रोकना\n"
        "• <code>/resume</code> — रुके हुए क्विज़ को वहीं से फिर शुरू करना\n"
        "• <code>/skip</code> — मौजूदा प्रश्न छोड़कर तुरंत अगला प्रश्न भेजना\n"
        "• <code>/stop</code> — क्विज़ समाप्त करना और फ़ाइनल टॉप-3 + स्कोर PDF भेजना\n"
        "• <code>/status</code> — मौजूदा प्रश्न नंबर, बचे प्रश्न और सेटिंग्स देखना\n\n"
        "⚙️ <b>स्पीड, रेंज और टारगेट कमांड्स:</b>\n"
        "• <code>/delay &lt;sec&gt;</code> — दो प्रश्नों के बीच का अंतर (सेकंड में) सेट करना\n"
        "• <code>/timer &lt;sec&gt;</code> — हर क्विज़ पोल का समय (सेकंड में) सेट करना\n"
        "• <code>/range &lt;start&gt;-&lt;end&gt;</code> — फ़ाइल से चुनिंदा प्रश्न चलाना (जैसे <code>/range 1-30</code>)\n"
        "• <code>/shuffle &lt;on|off&gt;</code> — प्रश्नों को शफ़ल या क्रम से चलाना\n"
        "• <code>/target &lt;chat_id&gt; [topic_id]</code> — किसी चैनल, ग्रुप या फ़ोरम टॉपिक में क्विज़ भेजना\n"
        "• <code>/neg &lt;marks&gt;</code> — नेगेटिव मार्किंग सेट करना (जैसे <code>/neg 0</code> या <code>/neg 0.25</code>)\n\n"
        "👥 <b>यूज़र कमांड:</b>\n"
        "• <code>/myscore</code> <i>(सभी यूज़र्स के लिए)</i> — अपना स्कोर और ग़लत प्रश्नों की लिस्ट देखना"
    )
    await update.effective_message.reply_text(help_text, parse_mode=ParseMode.HTML)


async def cmd_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return

    msg = update.effective_message
    reply = msg.reply_to_message if msg else None
    if not reply or not reply.document:
        await msg.reply_text(
            "⚠️ कृपया किसी <b>.json</b> या <b>.txt</b> क्विज़ फ़ाइल के <b>रिप्लाई</b> में <code>/quiz</code> लिखें।",
            parse_mode=ParseMode.HTML,
        )
        return

    if manager.session and not manager.session.stopped:
        await msg.reply_text(
            "⚠️ एक क्विज़ पहले से चल रहा है। पहले <code>/stop</code> करें।",
            parse_mode=ParseMode.HTML,
        )
        return

    doc = reply.document
    fname = (doc.file_name or "").lower()
    if not (fname.endswith(".json") or fname.endswith(".txt")):
        await msg.reply_text(
            "⚠️ कृपया केवल <b>.json</b> या <b>.txt</b> फ़ाइल के रिप्लाई में <code>/quiz</code> भेजें।",
            parse_mode=ParseMode.HTML,
        )
        return

    fd, temp_in = tempfile.mkstemp(prefix="sanskari_quiz_in_", suffix=".tmp")
    os.close(fd)

    try:
        tg_file = await context.bot.get_file(doc.file_id)
        await tg_file.download_to_drive(custom_path=temp_in)
        with open(temp_in, "r", encoding="utf-8", errors="replace") as f_in:
            raw_content = f_in.read()
    finally:
        if os.path.exists(temp_in):
            try:
                os.remove(temp_in)
            except OSError:
                pass

    try:
        if fname.endswith(".json"):
            questions = parse_questions_from_json(raw_content)
        else:
            questions = parse_questions_from_text(raw_content)
    except Exception as exc:
        await msg.reply_text(f"❌ फ़ाइल पढ़ने में त्रुटि: <code>{exc}</code>", parse_mode=ParseMode.HTML)
        return

    if not questions:
        await msg.reply_text("❌ इस फ़ाइल में कोई मान्य प्रश्न नहीं मिला।")
        return

    # Optional range argument on /quiz <start>-<end>
    start_idx = 0
    end_idx = len(questions)
    if context.args:
        arg_str = context.args[0].strip()
        if "-" in arg_str:
            parts = arg_str.split("-", 1)
            if parts[0].isdigit() and parts[1].isdigit():
                                s_val = max(1, int(parts[0]))
                e_val = min(len(questions), int(parts[1]))
                if s_val <= e_val:
                    start_idx = s_val - 1
                    end_idx = e_val

    selected_qs = [
        QuestionItem(
            q_num=i,
            question=q.question,
            options=list(q.options),
            correct_idx=q.correct_idx,
            explanation=q.explanation,
        )
        for i, q in enumerate(questions[start_idx:end_idx], start=1)
    ]

    if manager.default_shuffle:
        random.shuffle(selected_qs)
        for i, q in enumerate(selected_qs, start=1):
            q.q_num = i

    target_chat = manager.default_target_chat if manager.default_target_chat is not None else msg.chat_id
    target_thread = (
        manager.default_target_thread
        if manager.default_target_chat is not None
        else msg.message_thread_id
    )

    session = QuizSession(
        owner_id=OWNER_ID,
        chat_id=target_chat,
        thread_id=target_thread,
        questions=selected_qs,
        delay_sec=manager.default_delay,
        timer_sec=manager.default_timer,
        neg_marking=manager.default_neg,
        shuffle_enabled=manager.default_shuffle,
    )
    manager.session = session

    await msg.reply_text(
        f"✨ 🚀 <b>संस्कारी क्विज़ शुरू!</b>\n"
        f"📝 कुल प्रश्न: <b>{len(selected_qs)}</b>  |  ⏱ टाइमर: <b>{session.timer_sec}s</b>  |  ⏳ डिले: <b>{session.delay_sec}s</b>",
        parse_mode=ParseMode.HTML,
    )

    session.runner_task = asyncio.create_task(run_quiz_loop(session, context))


async def cmd_pause(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.paused = True
    await update.effective_message.reply_text("⏸ क्विज़ रोक दिया गया है। जारी रखने के लिए <code>/resume</code> लिखें।", parse_mode=ParseMode.HTML)


async def cmd_resume(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.paused = False
    await update.effective_message.reply_text("▶️ क्विज़ फिर से शुरू हो गया है।")


async def cmd_skip(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.skip_current = True
    await update.effective_message.reply_text("⏭ मौजूदा प्रश्न स्किप कर दिया गया है।")


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.stopped = True
    await update.effective_message.reply_text("🛑 क्विज़ समाप्त किया जा रहा है, फ़ाइनल स्कोर और PDF तैयार हो रही है...")


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return

    s = manager.session
    if s and not s.stopped:
        state = "Paused" if s.paused else "Running"
        txt = (
            f"📊 <b>क्विज़ स्टेटस</b>\n"
            f"• स्थिति: <b>{state}</b>\n"
            f"• प्रश्न: <b>{min(s.current_idx + 1, len(s.questions))}/{len(s.questions)}</b>\n"
            f"• प्रतिभागी: <b>{len(s.users)}</b>\n"
            f"• टाइमर: <b>{s.timer_sec}s</b>  |  डिले: <b>{s.delay_sec}s</b>\n"
            f"• नेगेटिव मार्किंग: <b>{s.neg_marking}</b>  |  शफ़ल: <b>{'ON' if s.shuffle_enabled else 'OFF'}</b>"
        )
    else:
        txt = (
            f"📊 <b>डिफ़ॉल्ट सेटिंग्स</b>\n"
            f"• टाइमर: <b>{manager.default_timer}s</b>  |  डिले: <b>{manager.default_delay}s</b>\n"
            f"• नेगेटिव मार्किंग: <b>{manager.default_neg}</b>  |  शफ़ल: <b>{'ON' if manager.default_shuffle else 'OFF'}</b>\n"
            f"• टारगेट चैट: <b>{manager.default_target_chat if manager.default_target_chat is not None else 'Current Chat'}</b>"
        )
    await update.effective_message.reply_text(txt, parse_mode=ParseMode.HTML)


async def cmd_delay(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args or not context.args[0].isdigit():
        await update.effective_message.reply_text("उपयोग: <code>/delay 5</code>", parse_mode=ParseMode.HTML)
        return
    val = max(0, min(300, int(context.args[0])))
    manager.default_delay = val
    if manager.session and not manager.session.stopped:
        manager.session.delay_sec = val
    await update.effective_message.reply_text(f"⏳ प्रश्नों के बीच डिले <b>{val} सेकंड</b> सेट किया गया।", parse_mode=ParseMode.HTML)


async def cmd_timer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args or not context.args[0].isdigit():
        await update.effective_message.reply_text("उपयोग: <code>/timer 20</code>", parse_mode=ParseMode.HTML)
        return
    val = max(5, min(600, int(context.args[0])))
    manager.default_timer = val
    if manager.session and not manager.session.stopped:
        manager.session.timer_sec = val
    await update.effective_message.reply_text(f"⏱ हर प्रश्न का टाइमर <b>{val} सेकंड</b> सेट किया गया।", parse_mode=ParseMode.HTML)


async def cmd_range(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "उपयोग: <code>/quiz 1-30</code> (फ़ाइल के रिप्लाई में)",
            parse_mode=ParseMode.HTML,
        )
        return
    await update.effective_message.reply_text(
        f"🎯 रेंज <code>{context.args[0]}</code> नोट कर ली गई है। फ़ाइल के रिप्लाई में <code>/quiz {context.args[0]}</code> भेजें।",
        parse_mode=ParseMode.HTML,
    )


async def cmd_shuffle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args or context.args[0].lower() not in ("on", "off"):
        await update.effective_message.reply_text("उपयोग: <code>/shuffle on</code> या <code>/shuffle off</code>", parse_mode=ParseMode.HTML)
        return
    enabled = context.args[0].lower() == "on"
    manager.default_shuffle = enabled
    if manager.session and not manager.session.stopped:
        manager.session.shuffle_enabled = enabled
    await update.effective_message.reply_text(f"🔀 शफ़ल मोड <b>{'ON' if enabled else 'OFF'}</b> किया गया।", parse_mode=ParseMode.HTML)


async def cmd_target(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args:
        manager.default_target_chat = None
        manager.default_target_thread = None
        await update.effective_message.reply_text("🎯 टारगेट रीसेट कर दिया गया है (वर्तमान चैट में क्विज़ चलेगा)।")
        return
    try:
        chat_id = int(context.args[0])
        thread_id = int(context.args[1]) if len(context.args) > 1 else None
    except ValueError:
        await update.effective_message.reply_text("उपयोग: <code>/target -1001234567890 [topic_id]</code>", parse_mode=ParseMode.HTML)
        return
    manager.default_target_chat = chat_id
    manager.default_target_thread = thread_id
    await update.effective_message.reply_text(
        f"🎯 टारगेट चैट सेट: <code>{chat_id}</code>" + (f" (Topic: <code>{thread_id}</code>)" if thread_id else ""),
        parse_mode=ParseMode.HTML,
    )


async def cmd_neg(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text("उपयोग: <code>/neg 0</code> या <code>/neg 0.25</code>", parse_mode=ParseMode.HTML)
        return
    try:
        val = max(0.0, float(context.args[0]))
    except ValueError:
        await update.effective_message.reply_text("कृपया वैध संख्या दें (जैसे <code>0</code> या <code>0.25</code>)।", parse_mode=ParseMode.HTML)
        return
    manager.default_neg = val
    if manager.session and not manager.session.stopped:
        manager.session.neg_marking = val
    await update.effective_message.reply_text(f"➖ नेगेटिव मार्किंग <b>{val}</b> सेट की गई।", parse_mode=ParseMode.HTML)


async def cmd_myscore(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    msg = update.effective_message
    if not user or not msg:
        return

    session = manager.session
    if not session or user.id not in session.users:
        await msg.reply_text(
            "📊 अभी आपका कोई क्विज़ स्कोर रिकॉर्ड नहीं मिला है। क्विज़ में उत्तर देने के बाद <code>/myscore</code> चलाएं।",
            parse_mode=ParseMode.HTML,
        )
        return

    rec = session.users[user.id]
    total_q = len(session.questions)
    skipped = max(0, total_q - (rec.correct + rec.wrong))
    acc = (rec.correct / total_q * 100.0) if total_q > 0 else 0.0

    lines = [
        f"✨ 📊 <b>आपका क्विज़ स्कोर — {rec.name}</b> ✨",
        f"• अंक (Score): <b>{rec.score:g}/{total_q}</b> ({acc:.1f}%)",
        f"• सही उत्तर: <b>{rec.correct}</b>  |  ग़लत उत्तर: <b>{rec.wrong}</b>  |  छोड़े गए: <b>{skipped}</b>",
        "",
    ]

    if rec.mistakes:
        lines.append("❌ <b>ग़लत हुए प्रश्न और सही उत्तर:</b>")
        for q_no, q_txt, chosen_opt, right_opt in rec.mistakes[:25]:
            lines.append(
                f"• <b>Q{q_no}:</b> {q_txt}\n"
                f"   ग़लत उत्तर: <i>{chosen_opt}</i>  |  ✅ सही उत्तर: <b>{right_opt}</b>"
            )
    else:
        lines.append("🎉 <b>बधाई हो! आपका कोई भी प्रश्न ग़लत नहीं हुआ।</b>")

    await msg.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


async def ignore_non_owner(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or is_owner(update.effective_user.id):
        return
    return


async def start_http_health_server() -> None:
    async def handle_client(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        try:
            await reader.read(1024)
            body = b"Sanskari Quiz Bot Running"
            headers = (
                b"HTTP/1.1 200 OK\r\n"
                b"Content-Type: text/plain; charset=utf-8\r\n"
                + f"Content-Length: {len(body)}\r\n".encode("ascii")
                + b"Connection: close\r\n\r\n"
            )
            writer.write(headers + body)
            await writer.drain()
        finally:
            writer.close()
            await writer.wait_closed()

    server = await asyncio.start_server(handle_client, "0.0.0.0", PORT)
    logger.info("Health server listening on 0.0.0.0:%s", PORT)
    async with server:
        await server.serve_forever()


async def post_init(application: Application) -> None:
    asyncio.create_task(start_http_health_server())


def main() -> None:
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN environment variable is required.")

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("quiz", cmd_quiz))
    app.add_handler(CommandHandler("pause", cmd_pause))
    app.add_handler(CommandHandler("resume", cmd_resume))
    app.add_handler(CommandHandler("skip", cmd_skip))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CommandHandler("delay", cmd_delay))
    app.add_handler(CommandHandler("timer", cmd_timer))
    app.add_handler(CommandHandler("range", cmd_range))
    app.add_handler(CommandHandler("shuffle", cmd_shuffle))
    app.add_handler(CommandHandler("target", cmd_target))
    app.add_handler(CommandHandler("neg", cmd_neg))
    app.add_handler(CommandHandler("myscore", cmd_myscore))

    app.add_handler(PollAnswerHandler(handle_poll_answer))
    app.add_handler(MessageHandler(filters.ALL, ignore_non_owner), group=99)

    if WEBHOOK_URL:
        parsed = urlparse(WEBHOOK_URL)
        path_part = parsed.path.strip("/") or "webhook"
        clean_base = f"{parsed.scheme}://{parsed.netloc}"
        app.run_webhook(
            listen="0.0.0.0",
            port=PORT,
            url_path=path_part,
            webhook_url=f"{clean_base}/{path_part}",
        )
    else:
        app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
