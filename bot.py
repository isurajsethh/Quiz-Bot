import asyncio
import html
import json
import logging
import os
import random
import re
import tempfile
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import urlparse

from fpdf import FPDF
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Poll,
    PollAnswer,
    Update,
)
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    CallbackQueryHandler,
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
ADMINS_FILE = "admins.json"


def load_admins() -> Set[int]:
    admins: Set[int] = {OWNER_ID}
    if os.path.exists(ADMINS_FILE):
        try:
            with open(ADMINS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                for item in data:
                    try:
                        admins.add(int(item))
                    except (ValueError, TypeError):
                        pass
        except Exception:
            pass
    return admins


def save_admins(admins: Set[int]) -> None:
    try:
        with open(ADMINS_FILE, "w", encoding="utf-8") as f:
            json.dump(sorted(list(admins)), f)
    except Exception:
        pass


ADMIN_IDS: Set[int] = load_admins()


def is_owner(user_id: Optional[int]) -> bool:
    return user_id is not None and user_id == OWNER_ID


def is_admin(user_id: Optional[int]) -> bool:
    return user_id is not None and (user_id == OWNER_ID or user_id in ADMIN_IDS)


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
class LiveQuestionState:
    q_num: int
    item: QuestionItem
    message_id: Optional[int] = None
    votes: Dict[int, int] = field(default_factory=dict)  # user_id -> option_idx
    revealed: bool = False
    has_wrong_click: bool = False


@dataclass
class QuizSession:
    owner_id: int
    chat_id: int
    thread_id: Optional[int]
    questions: List[QuestionItem]
    mode: str = "live"  # "live" (interactive buttons) or "poll" (classic poll)
    delay_sec: int = 0
    timer_sec: int = 20
    duration_sec: Optional[int] = None
    expires_at: Optional[float] = None
    neg_marking: float = 0.0
    shuffle_enabled: bool = False
    current_idx: int = 0
    paused: bool = False
    stopped: bool = False
    skip_current: bool = False
    active_poll_id: Optional[str] = None
    active_q_item: Optional[QuestionItem] = None
    poll_to_q: Dict[str, QuestionItem] = field(default_factory=dict)
    live_states: Dict[int, LiveQuestionState] = field(default_factory=dict)
    sent_message_ids: List[int] = field(default_factory=list)
    users: Dict[int, UserRecord] = field(default_factory=dict)
    runner_task: Optional[asyncio.Task] = None


class QuizManager:
    def __init__(self) -> None:
        self.default_delay: int = 0
        self.default_timer: int = 20
        self.default_neg: float = 0.0
        self.default_shuffle: bool = False
        self.default_target_chat: Optional[int] = None
        self.default_target_thread: Optional[int] = None
        self.session: Optional[QuizSession] = None
        self.last_session: Optional[QuizSession] = None
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


def parse_duration_arg(raw: str) -> Optional[int]:
    m = re.fullmatch(r"(\d+)\s*([smhSMH]?)", raw.strip())
    if not m:
        return None
    val = int(m.group(1))
    unit = (m.group(2) or "s").lower()
    if val <= 0:
        return None
    if unit == "m":
        return val * 60
    if unit == "h":
        return val * 3600
    return val


def find_unicode_font() -> Optional[str]:
    candidates = [
        "/usr/share/fonts/truetype/noto/NotoSansDevanagari-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/freefont/FreeSans.ttf",
        "/usr/share/fonts/TTF/DejaVuSans.ttf",
    ]
    for path in candidates:
        if os.path.exists(path):
            return path
    return None


def safe_pdf_text(text: str, unicode_ready: bool = False) -> str:
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
    if unicode_ready:
        return text
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
            exp_text = cur_exp.strip() or f"सही उत्तर: {cur_opts[ans_idx]}"
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
            exp_val = f"सही उत्तर: {options[correct_idx]}"

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

    unicode_font = find_unicode_font()
    font_family = "Helvetica"
    unicode_ready = False
    if unicode_font:
        try:
            pdf.add_font("UniFont", "", unicode_font, uni=True)
            pdf.add_font("UniFont", "B", unicode_font, uni=True)
            font_family = "UniFont"
            unicode_ready = True
        except Exception:
            font_family = "Helvetica"
            unicode_ready = False

    pdf.set_font(font_family, "B", 14)
    pdf.cell(0, 10, safe_pdf_text("SANSKARI QUIZ - SCORE & WRONG ANSWERS REPORT", unicode_ready), ln=True, align="C")

    pdf.set_font(font_family, "", 10)
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    pdf.cell(
        0,
        7,
        safe_pdf_text(f"Total Questions: {total_q} | Participants: {len(sorted_users)} | Generated: {stamp}", unicode_ready),
        ln=True,
        align="C",
    )
    pdf.ln(3)

    pdf.set_font(font_family, "B", 9)
    pdf.set_fill_color(230, 232, 240)
    col_w = [12, 68, 22, 22, 24, 42]
    headers = ["Rank", "Name", "Sahi", "Galat", "Skipped", "Score"]
    for w, h in zip(col_w, headers):
        pdf.cell(w, 8, safe_pdf_text(h, unicode_ready), border=1, align="C", fill=True)
    pdf.ln()

    pdf.set_font(font_family, "", 9)
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
            pdf.cell(w, 7, safe_pdf_text(val, unicode_ready), border=1, align=align)
        pdf.ln()

    pdf.ln(5)
    pdf.set_font(font_family, "B", 11)
    pdf.cell(0, 8, safe_pdf_text("गलत प्रश्नों का विवरण (WRONG ANSWERS ONLY)", unicode_ready), ln=True)

    for rank, u in enumerate(sorted_users, start=1):
        skipped = max(0, total_q - (u.correct + u.wrong))
        pdf.set_font(font_family, "B", 10)
        summary_line = (
            f"#{rank} {u.name}  |  Score: {u.score:g}/{total_q}  |  "
            f"सही: {u.correct}  |  गलत: {u.wrong}  |  छोड़े: {skipped}"
        )
        pdf.multi_cell(0, 6, safe_pdf_text(summary_line, unicode_ready))

        pdf.set_font(font_family, "", 9)
        if not u.mistakes:
            pdf.multi_cell(0, 5.5, safe_pdf_text("   - कोई प्रश्न गलत नहीं हुआ।", unicode_ready))
        else:
            for q_no, q_txt, chosen_opt, right_opt in u.mistakes:
                mistake_line = (
                    f"   {q_no}. {q_txt}\n"
                    f"      आपका जवाब: {chosen_opt}  |  सही जवाब: {right_opt}"
                )
                pdf.multi_cell(0, 5.5, safe_pdf_text(mistake_line, unicode_ready))
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
            safe_name = html.escape(u.name)
            lines.append(
                f"{emoji} <b>{label} — {safe_name}</b>\n"
                f"    ⚡ स्कोर: <b>{u.score:g}/{total_q}</b>  |  "
                f"✅ <b>{u.correct}</b>  |  ❌ <b>{u.wrong}</b>  |  📊 <b>{acc:.1f}%</b>"
            )

    lines.extend(
        [
            "",
            "📌 <i>अपना स्कोर देखने के लिए <code>/myscore</code> कमांड का इस्तेमाल करें।</i>",
            "📄 <i>सभी प्रतिभागियों का स्कोर और गलत प्रश्नों की लिस्ट नीचे PDF में दी गई है।</i>",
        ]
    )
    return "\n".join(lines)


def build_live_question_text(
    session: QuizSession,
    q_state: LiveQuestionState,
    show_results: bool = False,
) -> str:
    total_q = len(session.questions)
    item = q_state.item
    letters = ["A", "B", "C", "D"]
    total_votes = len(q_state.votes)

    counts = [0] * len(item.options)
    for opt_i in q_state.votes.values():
        if 0 <= opt_i < len(counts):
            counts[opt_i] += 1

    header = f"📝 <b>Q {q_state.q_num}/{total_q}</b>"
    if session.expires_at is not None and not session.stopped:
        rem = max(0, int(session.expires_at - asyncio.get_running_loop().time()))
        mins, secs = divmod(rem, 60)
        header += f"  •  ⏳ <b>{mins}m {secs:02d}s</b>"

    lines = [
        header,
        f"<b>{html.escape(item.question)}</b>",
        "",
    ]

    for idx, opt_text in enumerate(item.options):
        ltr = letters[idx] if idx < len(letters) else str(idx + 1)
        safe_opt = html.escape(opt_text)
        if show_results:
            pct = round((counts[idx] / total_votes) * 100) if total_votes > 0 else 0
            tick = " ✅" if idx == item.correct_idx else ""
            lines.append(f"<b>{ltr}.</b> {safe_opt} — <b>[{pct}%]</b>{tick}")
        else:
            lines.append(f"<b>{ltr}.</b> {safe_opt}")

    if q_state.has_wrong_click and item.explanation:
        lines.extend(
            [
                "",
                f"📖 <b>Explanation:</b> {html.escape(item.explanation)}",
            ]
        )

    return "\n".join(lines)


def build_live_keyboard(
    session: QuizSession,
    q_state: LiveQuestionState,
    locked: bool = False,
) -> Optional[InlineKeyboardMarkup]:
    if locked:
        return None
    letters = ["A", "B", "C", "D"]
    total_votes = len(q_state.votes)
    counts = [0] * len(q_state.item.options)
    for opt_i in q_state.votes.values():
        if 0 <= opt_i < len(counts):
            counts[opt_i] += 1

    rows: List[List[InlineKeyboardButton]] = []
    for idx, opt_text in enumerate(q_state.item.options):
        ltr = letters[idx] if idx < len(letters) else str(idx + 1)
        short_opt = opt_text[:28]
        if q_state.revealed:
            pct = round((counts[idx] / total_votes) * 100) if total_votes > 0 else 0
            tick = " ✅" if idx == q_state.item.correct_idx else ""
            label = f"{ltr}. {short_opt} [{pct}%]{tick}"
        else:
            label = f"{ltr}. {short_opt}"
        rows.append(
            [
                InlineKeyboardButton(
                    text=label,
                    callback_data=f"lq:{q_state.q_num}:{idx}",
                )
            ]
        )
    return InlineKeyboardMarkup(rows)


async def reveal_all_live_questions(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    for q_state in session.live_states.values():
        if not q_state.message_id:
            continue
        q_state.revealed = True
        text = build_live_question_text(session, q_state, show_results=True)
        try:
            await context.bot.edit_message_text(
                chat_id=session.chat_id,
                message_id=q_state.message_id,
                text=text,
                parse_mode=ParseMode.HTML,
                reply_markup=None,
            )
        except Exception:
            pass


async def finish_session(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    if session.mode == "live":
        await reveal_all_live_questions(session, context)

    top3_text = format_top3_message(session)
    send_kwargs = {"message_thread_id": session.thread_id} if session.thread_id else {}

    res_msg = await context.bot.send_message(
        chat_id=session.chat_id,
        text=top3_text,
        parse_mode=ParseMode.HTML,
        **send_kwargs,
    )
    session.sent_message_ids.append(res_msg.message_id)

    manager.cleanup_last_pdf()
    pdf_path = await asyncio.to_thread(build_score_pdf, session)
    caption = "📄 <b>संस्कारी क्विज़ — स्कोर एवं गलत प्रश्नों की PDF रिपोर्ट</b>"

    try:
        with open(pdf_path, "rb") as f_doc:
            pdf_msg = await context.bot.send_document(
                chat_id=session.chat_id,
                document=f_doc,
                filename="Sanskari_Quiz_Score_Report.pdf",
                caption=caption,
                parse_mode=ParseMode.HTML,
                **send_kwargs,
            )
            session.sent_message_ids.append(pdf_msg.message_id)
    finally:
        if os.path.exists(pdf_path):
            try:
                os.remove(pdf_path)
            except OSError:
                pass


async def run_quiz_loop(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    total_q = len(session.questions)
    send_kwargs = {"message_thread_id": session.thread_id} if session.thread_id else {}
    loop_obj = asyncio.get_running_loop()

    try:
        while session.current_idx < total_q and not session.stopped:
            if session.expires_at is not None and loop_obj.time() >= session.expires_at:
                session.stopped = True
                break

            while session.paused and not session.stopped:
                if session.expires_at is not None:
                    session.expires_at += 0.25
                await asyncio.sleep(0.25)
            if session.stopped:
                break

            item = session.questions[session.current_idx]
            display_no = session.current_idx + 1

            if session.mode == "live":
                q_state = LiveQuestionState(q_num=display_no, item=item)
                session.live_states[display_no] = q_state
                q_text = build_live_question_text(session, q_state, show_results=False)
                kb = build_live_keyboard(session, q_state, locked=False)
                sent = await context.bot.send_message(
                    chat_id=session.chat_id,
                    text=q_text,
                    parse_mode=ParseMode.HTML,
                    reply_markup=kb,
                    **send_kwargs,
                )
                q_state.message_id = sent.message_id
                session.sent_message_ids.append(sent.message_id)
            else:
                q_label = f"[{display_no}/{total_q}] {item.question}"[:300]
                opts = [opt[:100] for opt in item.options[:4]]
                exp_text = f"{item.explanation}"[:200]
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
                session.sent_message_ids.append(poll_msg.message_id)

            session.current_idx += 1

            if session.stopped:
                break

            if session.current_idx >= total_q:
                if session.mode == "live" and session.expires_at is not None:
                    while loop_obj.time() < session.expires_at and not session.stopped:
                        await asyncio.sleep(0.5)
                elif session.mode == "poll":
                    end_wait = 0.0
                    while end_wait < session.timer_sec and not session.stopped and not session.skip_current:
                        if not session.paused:
                            end_wait += 0.25
                        await asyncio.sleep(0.25)
                break

            delay_elapsed = 0.0
            while delay_elapsed < session.delay_sec and not session.stopped and not session.skip_current:
                if session.expires_at is not None and loop_obj.time() >= session.expires_at:
                    session.stopped = True
                    break
                if not session.paused:
                    delay_elapsed += 0.25
                await asyncio.sleep(0.25)

            if session.skip_current:
                session.skip_current = False

    except asyncio.CancelledError:
        session.stopped = True
    finally:
        session.stopped = True
        session.active_poll_id = None
        session.active_q_item = None
        await finish_session(session, context)
        manager.last_session = session
        if manager.session is session:
            manager.session = None


async def handle_live_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.data or not query.data.startswith("lq:"):
        return

    session = manager.session
    if not session or session.stopped or session.mode != "live":
        await query.answer("यह लाइव टेस्ट समाप्त हो चुका है।", show_alert=False)
        return

    if session.expires_at is not None and asyncio.get_running_loop().time() >= session.expires_at:
        session.stopped = True
        await query.answer("समय समाप्त! अब उत्तर स्वीकार नहीं किए जाएंगे।", show_alert=False)
        return

    parts = query.data.split(":")
    if len(parts) != 3:
        await query.answer()
        return

    try:
        q_num = int(parts[1])
        chosen_idx = int(parts[2])
    except ValueError:
        await query.answer()
        return

    q_state = session.live_states.get(q_num)
    if not q_state or q_state.revealed:
        await query.answer("इस प्रश्न के उत्तर लॉक हो चुके हैं।", show_alert=False)
        return

    user = query.from_user
    uid = user.id
    if uid in q_state.votes:
        await query.answer("आप इस प्रश्न का उत्तर पहले ही दे चुके हैं।", show_alert=False)
        return

    item = q_state.item
    if not (0 <= chosen_idx < len(item.options)):
        await query.answer()
        return

    q_state.votes[uid] = chosen_idx
    full_name = user.full_name or (f"@{user.username}" if user.username else f"User {uid}")
    if uid not in session.users:
        session.users[uid] = UserRecord(user_id=uid, name=full_name)
    else:
        session.users[uid].name = full_name

    rec = session.users[uid]
    chosen_text = item.options[chosen_idx]
    right_text = item.options[item.correct_idx]
    is_correct = chosen_idx == item.correct_idx

    if is_correct:
        rec.correct += 1
        rec.score += 1.0
        await query.answer("✅ सही उत्तर!", show_alert=False)
    else:
        rec.wrong += 1
        rec.score -= session.neg_marking
        rec.mistakes.append((item.q_num, item.question, chosen_text, right_text))
        q_state.has_wrong_click = True
        await query.answer("❌ गलत उत्तर!", show_alert=False)
        # Update message text so explanation appears directly below the 4 options
        new_text = build_live_question_text(session, q_state, show_results=q_state.revealed)
        kb = build_live_keyboard(session, q_state, locked=False)
        try:
            await query.edit_message_text(
                text=new_text,
                parse_mode=ParseMode.HTML,
                reply_markup=kb,
            )
        except Exception:
            pass

    # If all active participants in this session have voted on this question, reveal percentages + tick
    if len(session.users) > 0 and len(q_state.votes) >= len(session.users) and len(session.users) >= 2:
        q_state.revealed = True
        rev_text = build_live_question_text(session, q_state, show_results=True)
        try:
            await context.bot.edit_message_text(
                chat_id=session.chat_id,
                message_id=q_state.message_id,
                text=rev_text,
                parse_mode=ParseMode.HTML,
                reply_markup=None,
            )
        except Exception:
            pass


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


async def extract_questions_from_reply(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> Optional[List[QuestionItem]]:
    msg = update.effective_message
    reply = msg.reply_to_message if msg else None
    if not reply:
        await msg.reply_text(
            "⚠️ कृपया किसी <b>.json / .txt फ़ाइल</b> या <b>प्रश्नों वाले टेक्स्ट मैसेज</b> पर <b>Reply</b> करके कमांड भेजें।",
            parse_mode=ParseMode.HTML,
        )
        return None

    if reply.document:
        doc = reply.document
        fname = (doc.file_name or "").lower()
        if not (fname.endswith(".json") or fname.endswith(".txt")):
            await msg.reply_text(
                "⚠️ कृपया केवल <b>.json</b> या <b>.txt</b> फ़ाइल के रिप्लाई में कमांड भेजें।",
                parse_mode=ParseMode.HTML,
            )
            return None

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
            await msg.reply_text(f"❌ फ़ाइल पढ़ने में त्रुटि: <code>{html.escape(str(exc))}</code>", parse_mode=ParseMode.HTML)
            return None
    else:
        raw_text = (reply.text or reply.caption or "").strip()
        if not raw_text:
            await msg.reply_text("⚠️ रिप्लाई किए गए मैसेज में कोई प्रश्न या फ़ाइल नहीं मिली।")
            return None
        try:
            if raw_text.lstrip().startswith(("[", "{")):
                questions = parse_questions_from_json(raw_text)
            else:
                questions = parse_questions_from_text(raw_text)
        except Exception as exc:
            await msg.reply_text(f"❌ टेक्स्ट पढ़ने में त्रुटि: <code>{html.escape(str(exc))}</code>", parse_mode=ParseMode.HTML)
            return None

    if not questions:
        await msg.reply_text("❌ इसमें कोई मान्य प्रश्न और विकल्प नहीं मिले।")
        return None
    return questions


async def start_quiz_common(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    mode: str,
) -> None:
    msg = update.effective_message
    if manager.session and not manager.session.stopped:
        await msg.reply_text(
            "⚠️ एक क्विज़ पहले से चल रहा है। पहले <code>/stop</code> करें।",
            parse_mode=ParseMode.HTML,
        )
        return

    questions = await extract_questions_from_reply(update, context)
    if not questions:
        return

    start_idx = 0
    end_idx = len(questions)
    duration_sec: Optional[int] = None

    for arg in context.args:
        a = arg.strip()
        if "-" in a:
            parts = a.split("-", 1)
            if parts[0].isdigit() and parts[1].isdigit():
                s_val = max(1, int(parts[0]))
                e_val = min(len(questions), int(parts[1]))
                if s_val <= e_val:
                    start_idx = s_val - 1
                    end_idx = e_val
        else:
            dur = parse_duration_arg(a)
            if dur is not None:
                duration_sec = dur

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

    expires_at = (asyncio.get_running_loop().time() + duration_sec) if duration_sec else None

    session = QuizSession(
        owner_id=OWNER_ID,
        chat_id=target_chat,
        thread_id=target_thread,
        questions=selected_qs,
        mode=mode,
        delay_sec=manager.default_delay,
        timer_sec=manager.default_timer,
        duration_sec=duration_sec,
        expires_at=expires_at,
        neg_marking=manager.default_neg,
        shuffle_enabled=manager.default_shuffle,
    )
    manager.session = session

    mode_label = "Live Interactive Quiz" if mode == "live" else "Classic Poll Quiz"
    speed_label = "तुरंत-तुरंत (0s)" if session.delay_sec == 0 else f"{session.delay_sec}s"
    dur_label = f" | ⏱ कुल समय: <b>{duration_sec // 60}m {duration_sec % 60}s</b>" if duration_sec else ""

    info_msg = await msg.reply_text(
        f"✨ 🚀 <b>संस्कारी क्विज़ शुरू ({mode_label})</b>\n"
        f"📝 कुल प्रश्न: <b>{len(selected_qs)}</b>  |  ⏳ गैप: <b>{speed_label}</b>{dur_label}",
        parse_mode=ParseMode.HTML,
    )
    session.sent_message_ids.append(info_msg.message_id)

    session.runner_task = asyncio.create_task(run_quiz_loop(session, context))


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return

    help_text = (
        "✨ 🛠️ <b>संस्कारी क्विज़ बॉट — सम्पूर्ण कमांड मेन्यू</b> 🛠️ ✨\n\n"
        "🎯 <b>क्विज़ शुरू करने के कमांड्स (फ़ाइल या टेक्स्ट के Reply में):</b>\n"
        "• <code>/livequiz</code> — लाइव इंटरैक्टिव बटन क्विज़ शुरू करना (प्रतिशत + गलत पर नीचे Explanation)\n"
        "• <code>/livequiz 30m</code> — समय सीमा के साथ लाइव टेस्ट (जैसे <code>30m</code> बाद लॉक व रिज़ल्ट)\n"
        "• <code>/livequiz 1-30</code> — फ़ाइल/टेक्स्ट से चुनिंदा प्रश्न चलाना\n"
        "• <code>/quiz</code> — क्लासिक टेलीग्राम क्विज़ पोल मोड में प्रश्न चलाना\n\n"
        "⏯️ <b>क्विज़ कंट्रोल कमांड्स:</b>\n"
        "• <code>/pause</code> — चल रहे क्विज़ को अस्थायी रूप से रोकना\n"
        "• <code>/resume</code> — रुके हुए क्विज़ को वहीं से फिर शुरू करना\n"
        "• <code>/skip</code> — मौजूदा प्रतीक्षा छोड़कर तुरंत अगला प्रश्न भेजना\n"
        "• <code>/reveal</code> — लाइव प्रश्नों के प्रतिशत व सही उत्तर तुरंत दिखाना\n"
        "• <code>/stop</code> — क्विज़ समाप्त करना और फ़ाइनल टॉप-3 + स्कोर PDF भेजना\n"
        "• <code>/delquiz</code> — टेस्ट खत्म होने के बाद भेजे गए सभी प्रश्नों को चैट से डिलीट करना\n"
        "• <code>/status</code> — मौजूदा प्रश्न संख्या, प्रतिभागी और सेटिंग्स देखना\n\n"
        "⚙️ <b>स्पीड, टारगेट और मार्किंग सेटिंग्स:</b>\n"
        "• <code>/delay &lt;sec&gt;</code> — हर प्रश्न के बीच का गैप (<code>0</code> = तुरंत-तुरंत, <code>5</code> = 5 सेकंड बाद)\n"
        "• <code>/timer &lt;sec&gt;</code> — क्लासिक पोल टाइमर सेट करना\n"
        "• <code>/shuffle &lt;on|off&gt;</code> — प्रश्नों को शफ़ल या क्रम से चलाना\n"
        "• <code>/target &lt;chat_id&gt; [topic_id]</code> — किसी दूसरे ग्रुप, चैनल या टॉपिक में क्विज़ भेजना\n"
        "• <code>/neg &lt;marks&gt;</code> — नेगेटिव मार्किंग सेट करना (जैसे <code>/neg 0</code> या <code>/neg 0.25</code>)\n\n"
        "👑 <b>एडमिन व ID कमांड्स:</b>\n"
        "• <code>/id</code> — अपनी, ग्रुप/चैनल की या किसी के मैसेज पर Reply करके उसकी Numerical ID निकालना\n"
        "• <code>/addadmin &lt;user_id&gt;</code> — किसी यूज़र को बॉट का एडमिन बनाना (सिर्फ़ Owner)\n"
        "• <code>/removeadmin &lt;user_id&gt;</code> — एडमिन को हटाना (सिर्फ़ Owner)\n\n"
        "👥 <b>स्टूडेंट्स के लिए कमांड:</b>\n"
        "• <code>/myscore</code> — अपना स्कोर और गलत प्रश्नों की लिस्ट देखना"
    )
    await update.effective_message.reply_text(help_text, parse_mode=ParseMode.HTML)


async def cmd_livequiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    await start_quiz_common(update, context, mode="live")


async def cmd_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    await start_quiz_common(update, context, mode="poll")


async def cmd_reveal(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped or manager.session.mode != "live":
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय लाइव क्विज़ नहीं चल रहा है।")
        return
    await reveal_all_live_questions(manager.session, context)
    await update.effective_message.reply_text("✅ सभी लाइव प्रश्नों के प्रतिशत और सही उत्तर दिखा दिए गए हैं।")


async def cmd_delquiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    target_session = manager.session or manager.last_session
    if not target_session or not target_session.sent_message_ids:
        await update.effective_message.reply_text("ℹ️ डिलीट करने के लिए कोई पिछला क्विज़ मैसेज रिकॉर्ड नहीं मिला।")
        return

    deleted_count = 0
    for mid in list(target_session.sent_message_ids):
        try:
            await context.bot.delete_message(chat_id=target_session.chat_id, message_id=mid)
            deleted_count += 1
        except Exception:
            pass
    target_session.sent_message_ids.clear()
    await update.effective_message.reply_text(f"🗑️ क्विज़ के <b>{deleted_count}</b> मैसेज/प्रश्न डिलीट कर दिए गए हैं।", parse_mode=ParseMode.HTML)


async def cmd_pause(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.paused = True
    await update.effective_message.reply_text("⏸ क्विज़ रोक दिया गया है। जारी रखने के लिए <code>/resume</code> लिखें।", parse_mode=ParseMode.HTML)


async def cmd_resume(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.paused = False
    await update.effective_message.reply_text("▶️ क्विज़ फिर से शुरू हो गया है।")


async def cmd_skip(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.skip_current = True
    await update.effective_message.reply_text("⏭ प्रतीक्षा स्किप कर दी गई है।")


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not manager.session or manager.session.stopped:
        await update.effective_message.reply_text("ℹ️ अभी कोई सक्रिय क्विज़ नहीं चल रहा है।")
        return
    manager.session.stopped = True
    await update.effective_message.reply_text("🛑 क्विज़ समाप्त किया जा रहा है, फ़ाइनल स्कोर और PDF तैयार हो रही है...")


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return

    s = manager.session
    if s and not s.stopped:
        state = "Paused" if s.paused else "Running"
        delay_txt = "तुरंत (0s)" if s.delay_sec == 0 else f"{s.delay_sec}s"
        txt = (
            f"📊 <b>क्विज़ स्टेटस ({s.mode.upper()})</b>\n"
            f"• स्थिति: <b>{state}</b>\n"
            f"• भेजे गए प्रश्न: <b>{min(s.current_idx, len(s.questions))}/{len(s.questions)}</b>\n"
            f"• प्रतिभागी: <b>{len(s.users)}</b>\n"
            f"• प्रश्नों के बीच गैप (Delay): <b>{delay_txt}</b>\n"
            f"• नेगेटिव मार्किंग: <b>{s.neg_marking}</b>  |  शफ़ल: <b>{'ON' if s.shuffle_enabled else 'OFF'}</b>"
        )
    else:
        delay_txt = "तुरंत (0s)" if manager.default_delay == 0 else f"{manager.default_delay}s"
        txt = (
            f"📊 <b>डिफ़ॉल्ट सेटिंग्स</b>\n"
            f"• प्रश्नों के बीच गैप (Delay): <b>{delay_txt}</b>  |  पोल टाइमर: <b>{manager.default_timer}s</b>\n"
            f"• नेगेटिव मार्किंग: <b>{manager.default_neg}</b>  |  शफ़ल: <b>{'ON' if manager.default_shuffle else 'OFF'}</b>\n"
            f"• टारगेट चैट: <b>{manager.default_target_chat if manager.default_target_chat is not None else 'Current Chat'}</b>\n"
            f"• कुल एडमिन: <b>{len(ADMIN_IDS)}</b>"
        )
    await update.effective_message.reply_text(txt, parse_mode=ParseMode.HTML)


async def cmd_delay(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args or not context.args[0].isdigit():
        await update.effective_message.reply_text(
            "उपयोग: <code>/delay 0</code> (तुरंत-तुरंत) या <code>/delay 5</code> (5 सेकंड बाद)",
            parse_mode=ParseMode.HTML,
        )
        return
    val = max(0, min(600, int(context.args[0])))
    manager.default_delay = val
    if manager.session and not manager.session.stopped:
        manager.session.delay_sec = val
    if val == 0:
        await update.effective_message.reply_text("⚡ डिले हटा दिया गया है (<b>0 सेकंड</b>) — अब सारे प्रश्न तुरंत-तुरंत आएंगे।", parse_mode=ParseMode.HTML)
    else:
        await update.effective_message.reply_text(f"⏳ हर प्रश्न के बीच गैप <b>{val} सेकंड</b> सेट किया गया।", parse_mode=ParseMode.HTML)


async def cmd_timer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args or not context.args[0].isdigit():
        await update.effective_message.reply_text("उपयोग: <code>/timer 20</code>", parse_mode=ParseMode.HTML)
        return
    val = max(5, min(600, int(context.args[0])))
    manager.default_timer = val
    if manager.session and not manager.session.stopped:
        manager.session.timer_sec = val
    await update.effective_message.reply_text(f"⏱ क्लासिक पोल टाइमर <b>{val} सेकंड</b> सेट किया गया।", parse_mode=ParseMode.HTML)


async def cmd_range(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "उपयोग: फ़ाइल/टेक्स्ट के रिप्लाई में <code>/livequiz 1-30</code> या <code>/quiz 1-30</code> लिखें।",
            parse_mode=ParseMode.HTML,
        )
        return
    await update.effective_message.reply_text(
        f"🎯 रेंज <code>{html.escape(context.args[0])}</code> के लिए फ़ाइल/टेक्स्ट के रिप्लाई में <code>/livequiz {html.escape(context.args[0])}</code> भेजें।",
        parse_mode=ParseMode.HTML,
    )


async def cmd_shuffle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
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
    if not update.effective_user or not is_admin(update.effective_user.id):
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
    if not update.effective_user or not is_admin(update.effective_user.id):
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


async def cmd_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not msg or not user or not chat:
        return

    lines = [
        "🆔 <b>ID जानकारी</b>",
        f"• आपकी User ID: <code>{user.id}</code>",
        f"• इस चैट/ग्रुप/चैनल की ID: <code>{chat.id}</code>",
    ]
    if msg.message_thread_id:
        lines.append(f"• Topic / Thread ID: <code>{msg.message_thread_id}</code>")

    reply = msg.reply_to_message
    if reply:
        if reply.from_user:
            r_name = html.escape(reply.from_user.full_name or "User")
            lines.append(f"• रिप्लाई किए गए यूज़र ({r_name}) की ID: <code>{reply.from_user.id}</code>")
        if reply.forward_origin:
            origin = reply.forward_origin
            sender_user = getattr(origin, "sender_user", None)
            sender_chat = getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
            if sender_user:
                lines.append(f"• Forwarded User ID: <code>{sender_user.id}</code>")
            if sender_chat:
                lines.append(f"• Forwarded Channel/Chat ID: <code>{sender_chat.id}</code>")

    await msg.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


async def cmd_addadmin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text("उपयोग: <code>/addadmin 123456789</code>", parse_mode=ParseMode.HTML)
        return
    try:
        new_id = int(context.args[0])
    except ValueError:
        await update.effective_message.reply_text("⚠️ कृपया सही Numerical User ID डालें।")
        return
    ADMIN_IDS.add(new_id)
    save_admins(ADMIN_IDS)
    await update.effective_message.reply_text(
        f"✅ यूज़र <code>{new_id}</code> को बॉट का <b>Admin</b> बना दिया गया है।",
        parse_mode=ParseMode.HTML,
    )


async def cmd_removeadmin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_owner(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text("उपयोग: <code>/removeadmin 123456789</code>", parse_mode=ParseMode.HTML)
        return
    try:
        rem_id = int(context.args[0])
    except ValueError:
        await update.effective_message.reply_text("⚠️ कृपया सही Numerical User ID डालें।")
        return
    if rem_id == OWNER_ID:
        await update.effective_message.reply_text("⚠️ मुख्य Owner को हटाया नहीं जा सकता।")
        return
    if rem_id in ADMIN_IDS:
        ADMIN_IDS.remove(rem_id)
        save_admins(ADMIN_IDS)
        await update.effective_message.reply_text(
            f"🚫 यूज़र <code>{rem_id}</code> को Admin लिस्ट से हटा दिया गया है।",
            parse_mode=ParseMode.HTML,
        )
    else:
        await update.effective_message.reply_text(f"ℹ️ यूज़र <code>{rem_id}</code> Admin लिस्ट में नहीं है।", parse_mode=ParseMode.HTML)


async def cmd_myscore(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    msg = update.effective_message
    if not user or not msg:
        return

    session = manager.session or manager.last_session
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
        f"✨ 📊 <b>आपका क्विज़ स्कोर — {html.escape(rec.name)}</b> ✨",
        f"• अंक (Score): <b>{rec.score:g}/{total_q}</b> ({acc:.1f}%)",
        f"• सही उत्तर: <b>{rec.correct}</b>  |  गलत उत्तर: <b>{rec.wrong}</b>  |  छोड़े गए: <b>{skipped}</b>",
        "",
    ]

    if rec.mistakes:
        lines.append("❌ <b>गलत हुए प्रश्न और सही उत्तर:</b>")
        for q_no, q_txt, chosen_opt, right_opt in rec.mistakes[:25]:
            lines.append(
                f"• <b>{q_no}. {html.escape(q_txt)}</b>\n"
                f"   आपका जवाब: <i>{html.escape(chosen_opt)}</i>  |  ✅ सही जवाब: <b>{html.escape(right_opt)}</b>"
            )
    else:
        lines.append("🎉 <b>बधाई हो! आपका कोई भी प्रश्न गलत नहीं हुआ।</b>")

    await msg.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


async def ignore_non_owner(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
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
    try:
        asyncio.get_event_loop()
    except RuntimeError:
        asyncio.set_event_loop(asyncio.new_event_loop())

    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN environment variable is required.")

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("livequiz", cmd_livequiz))
    app.add_handler(CommandHandler("quiz", cmd_quiz))
    app.add_handler(CommandHandler("reveal", cmd_reveal))
    app.add_handler(CommandHandler("delquiz", cmd_delquiz))
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
    app.add_handler(CommandHandler("id", cmd_id))
    app.add_handler(CommandHandler("addadmin", cmd_addadmin))
    app.add_handler(CommandHandler("removeadmin", cmd_removeadmin))
    app.add_handler(CommandHandler("myscore", cmd_myscore))

    app.add_handler(CallbackQueryHandler(handle_live_callback, pattern=r"^lq:"))
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
