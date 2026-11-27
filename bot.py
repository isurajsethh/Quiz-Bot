import asyncio
import html
import json
import logging
import os
import random
import re
import tempfile
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import urlparse
from zoneinfo import ZoneInfo

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

IST = ZoneInfo("Asia/Kolkata")
DEFAULT_OWNER_ID = 8283878643
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
OWNER_ID = int(os.environ.get("OWNER_ID", str(DEFAULT_OWNER_ID)))
PORT = int(os.environ.get("PORT", "10000"))
WEBHOOK_URL = os.environ.get("WEBHOOK_URL", "").strip()
ADMINS_FILE = "admins.json"
SAVES_FILE = "saved_quizzes.json"
STATE_FILE = "quiz_state.json"


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


def default_save_tree() -> Dict[str, Any]:
    return {"folders": {}, "tests": {}}


def load_save_tree() -> Dict[str, Any]:
    if os.path.exists(SAVES_FILE):
        try:
            with open(SAVES_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                data.setdefault("folders", {})
                data.setdefault("tests", {})
                return data
        except Exception:
            pass
    return default_save_tree()


def persist_save_tree(tree: Dict[str, Any]) -> None:
    try:
        with open(SAVES_FILE, "w", encoding="utf-8") as f:
            json.dump(tree, f, ensure_ascii=False, indent=2)
    except Exception as exc:
        logger.error("Failed to save quiz tree: %s", exc)


SAVE_TREE: Dict[str, Any] = load_save_tree()
PATH_TOKENS: Dict[str, List[str]] = {}
PENDING_EDIT_BY_USER: Dict[int, List[str]] = {}


def register_path(path: List[str]) -> str:
    key = "|".join(path)
    for tok, p in PATH_TOKENS.items():
        if "|".join(p) == key:
            return tok
    tok = uuid.uuid4().hex[:10]
    PATH_TOKENS[tok] = list(path)
    return tok


def resolve_path(tok: str) -> Optional[List[str]]:
    if tok == "root":
        return []
    return PATH_TOKENS.get(tok)


def get_folder_node(tree: Dict[str, Any], path: List[str], create: bool = False) -> Optional[Dict[str, Any]]:
    node = tree
    for part in path:
        folders = node.setdefault("folders", {})
        if part not in folders:
            if create:
                folders[part] = default_save_tree()
            else:
                return None
        node = folders[part]
    node.setdefault("folders", {})
    node.setdefault("tests", {})
    return node


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
    votes: Dict[int, int] = field(default_factory=dict)
    revealed: bool = False
    has_wrong_click: bool = False


@dataclass
class QuizSession:
    owner_id: int
    chat_id: int
    thread_id: Optional[int]
    questions: List[QuestionItem]
    mode: str = "live"
    delay_sec: int = 0
    timer_sec: int = 20
    duration_sec: Optional[int] = None
    expires_at: Optional[float] = None
    neg_marking: float = 0.0
    shuffle_enabled: bool = False
    current_idx: int = 0
    paused: bool = False
    stopped: bool = False
    completed_naturally: bool = False
    skip_current: bool = False
    active_poll_id: Optional[str] = None
    active_q_item: Optional[QuestionItem] = None
    poll_to_q: Dict[str, QuestionItem] = field(default_factory=dict)
    live_states: Dict[int, LiveQuestionState] = field(default_factory=dict)
    sent_message_ids: List[int] = field(default_factory=list)
    temp_files: List[str] = field(default_factory=list)
    users: Dict[int, UserRecord] = field(default_factory=dict)
    runner_task: Optional[asyncio.Task] = None


@dataclass
class ScheduledQuizJob:
    job_id: str
    chat_id: int
    thread_id: Optional[int]
    run_at: datetime
    questions: List[QuestionItem]
    mode: str
    task: Optional[asyncio.Task] = None


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
        self.scheduled_jobs: Dict[str, ScheduledQuizJob] = {}
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

    def cleanup_session_storage(self, sess: Optional[QuizSession]) -> None:
        if not sess:
            return
        for fp in list(sess.temp_files):
            if fp and os.path.exists(fp):
                try:
                    os.remove(fp)
                except OSError:
                    pass
        sess.temp_files.clear()
        self.cleanup_last_pdf()

    def reset_runtime_settings(self) -> None:
        if self.session and self.session.runner_task and not self.session.runner_task.done():
            self.session.stopped = True
            self.session.completed_naturally = False
            self.session.runner_task.cancel()
        self.cleanup_session_storage(self.session)
        self.session = None

        for job in list(self.scheduled_jobs.values()):
            if job.task and not job.task.done():
                job.task.cancel()
        self.scheduled_jobs.clear()

        self.default_delay = 0
        self.default_timer = 20
        self.default_neg = 0.0
        self.default_shuffle = False
        self.default_target_chat = None
        self.default_target_thread = None
        PENDING_EDIT_BY_USER.clear()
        self.save_snapshot()

    def save_snapshot(self) -> None:
        try:
            payload = {
                "default_delay": self.default_delay,
                "default_timer": self.default_timer,
                "default_neg": self.default_neg,
                "default_shuffle": self.default_shuffle,
                "default_target_chat": self.default_target_chat,
                "default_target_thread": self.default_target_thread,
            }
            with open(STATE_FILE, "w", encoding="utf-8") as f:
                json.dump(payload, f)
        except Exception:
            pass

    def load_snapshot(self) -> None:
        if not os.path.exists(STATE_FILE):
            return
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                self.default_delay = int(data.get("default_delay", 0))
                self.default_timer = int(data.get("default_timer", 20))
                self.default_neg = float(data.get("default_neg", 0.0))
                self.default_shuffle = bool(data.get("default_shuffle", False))
                self.default_target_chat = data.get("default_target_chat")
                self.default_target_thread = data.get("default_target_thread")
        except Exception:
            pass


manager = QuizManager()
manager.load_snapshot()


def parse_seconds_input(raw: str, min_val: int = 0, max_val: int = 3600) -> Optional[int]:
    m = re.fullmatch(r"(\d+)\s*([smhSMH]?)", raw.strip())
    if not m:
        return None
    val = int(m.group(1))
    unit = (m.group(2) or "s").lower()
    if unit == "m":
        secs = val * 60
    elif unit == "h":
        secs = val * 3600
    else:
        secs = val
    if secs < min_val:
        return None
    return min(max_val, secs)


def parse_duration_arg(raw: str) -> Optional[int]:
    return parse_seconds_input(raw, min_val=1, max_val=14400)


def parse_clock_time_ist(args: List[str]) -> Optional[datetime]:
    if not args:
        return None
    joined = " ".join(args).strip().lower()
    m = re.fullmatch(r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)?", joined)
    if not m:
        return None
    hour = int(m.group(1))
    minute = int(m.group(2) or "0")
    ampm = m.group(3)

    if minute < 0 or minute > 59:
        return None

    if ampm == "am":
        if hour < 1 or hour > 12:
            return None
        hour = 0 if hour == 12 else hour
    elif ampm == "pm":
        if hour < 1 or hour > 12:
            return None
        hour = 12 if hour == 12 else hour + 12
    else:
        if hour < 0 or hour > 23:
            return None

    now = datetime.now(IST)
    target = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if target <= now:
        target = target + timedelta(days=1)
    return target


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


def serialize_questions(items: List[QuestionItem]) -> List[Dict[str, Any]]:
    return [
        {
            "q": q.question,
            "options": list(q.options),
            "correct": q.correct_idx,
            "explanation": q.explanation,
        }
        for q in items
    ]


def deserialize_questions(raw_list: List[Dict[str, Any]]) -> List[QuestionItem]:
    out: List[QuestionItem] = []
    for idx, d in enumerate(raw_list, start=1):
        out.append(
            QuestionItem(
                q_num=idx,
                question=str(d.get("q", "")),
                options=list(d.get("options", [])),
                correct_idx=int(d.get("correct", 0)),
                explanation=str(d.get("explanation", "")),
            )
        )
    return out


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
    stamp = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S")
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

    header = f"📝 <b>[{q_state.q_num}/{total_q}]</b>"
    if session.expires_at is not None and not session.stopped:
        rem = max(0, int(session.expires_at - asyncio.get_running_loop().time()))
        mins, secs = divmod(rem, 60)
        header += f"  ⏳ <b>{mins}m {secs:02d}s</b>"

    lines = [
        f"{header} <b>{html.escape(item.question)}</b>",
        "",
    ]

    for idx, opt_text in enumerate(item.options):
        ltr = letters[idx] if idx < len(letters) else str(idx + 1)
        safe_opt = html.escape(opt_text)
        if show_results:
            pct = round((counts[idx] / total_votes) * 100) if total_votes > 0 else 0
            tick = " ✅" if idx == item.correct_idx else ""
            lines.append(f"<b>{ltr}.</b> {safe_opt}  <b>[{pct}%]</b>{tick}")
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
        short_opt = opt_text[:32]
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
    manager.last_pdf_path = pdf_path
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
        manager.cleanup_session_storage(session)


async def run_quiz_loop(session: QuizSession, context: ContextTypes.DEFAULT_TYPE) -> None:
    total_q = len(session.questions)
    send_kwargs = {"message_thread_id": session.thread_id} if session.thread_id else {}
    loop_obj = asyncio.get_running_loop()

    try:
        while session.current_idx < total_q and not session.stopped:
            if session.expires_at is not None and loop_obj.time() >= session.expires_at:
                session.stopped = True
                session.completed_naturally = True
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
                session.completed_naturally = True
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
                    session.completed_naturally = True
                    break
                if not session.paused:
                    delay_elapsed += 0.25
                await asyncio.sleep(0.25)

            if session.skip_current:
                session.skip_current = False

    except asyncio.CancelledError:
        session.stopped = True
        manager.cleanup_session_storage(session)
        return
    finally:
        session.stopped = True
        session.active_poll_id = None
        session.active_q_item = None
        if session.completed_naturally:
            await finish_session(session, context)
            manager.last_session = session
        else:
            manager.cleanup_session_storage(session)
        if manager.session is session:
            manager.session = None


async def launch_session_from_questions(
    chat_id: int,
    thread_id: Optional[int],
    questions: List[QuestionItem],
    context: ContextTypes.DEFAULT_TYPE,
    mode: str = "live",
    duration_sec: Optional[int] = None,
    title_note: str = "",
    temp_files: Optional[List[str]] = None,
) -> None:
    if manager.session and not manager.session.stopped:
        await context.bot.send_message(
            chat_id=chat_id,
            message_thread_id=thread_id,
            text="⚠️ एक क्विज़ पहले से चल रहा है। पहले <code>/stop</code> करें।",
            parse_mode=ParseMode.HTML,
        )
        return

    selected_qs = [
        QuestionItem(
            q_num=i,
            question=q.question,
            options=list(q.options),
            correct_idx=q.correct_idx,
            explanation=q.explanation,
        )
        for i, q in enumerate(questions, start=1)
    ]

    if manager.default_shuffle:
        random.shuffle(selected_qs)
        for i, q in enumerate(selected_qs, start=1):
            q.q_num = i

    target_chat = manager.default_target_chat if manager.default_target_chat is not None else chat_id
    target_thread = (
        manager.default_target_thread
        if manager.default_target_chat is not None
        else thread_id
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
        temp_files=list(temp_files or []),
    )
    manager.session = session

    mode_label = "Live Quiz" if mode == "live" else "Classic Poll Quiz"
    speed_label = "तुरंत-तुरंत (0s)" if session.delay_sec == 0 else f"{session.delay_sec}s"
    dur_label = f" | ⏱ समय: <b>{duration_sec // 60}m {duration_sec % 60}s</b>" if duration_sec else ""
    extra_title = f" — <b>{html.escape(title_note)}</b>" if title_note else ""

    send_kwargs = {"message_thread_id": thread_id} if thread_id else {}
    info_msg = await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"✨ 🚀 <b>संस्कारी क्विज़ शुरू ({mode_label})</b>{extra_title}\n"
            f"📝 कुल प्रश्न: <b>{len(selected_qs)}</b>  |  ⏳ गैप: <b>{speed_label}</b>{dur_label}"
        ),
        parse_mode=ParseMode.HTML,
        **send_kwargs,
    )
    session.sent_message_ids.append(info_msg.message_id)

    session.runner_task = asyncio.create_task(run_quiz_loop(session, context))


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
        session.completed_naturally = True
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


async def extract_questions_from_message(
    target_msg: Any,
    context: ContextTypes.DEFAULT_TYPE,
) -> Tuple[Optional[List[QuestionItem]], Optional[str], List[str]]:
    temp_paths: List[str] = []
    if not target_msg:
        return None, "कोई मैसेज नहीं मिला।", temp_paths

    if target_msg.document:
        doc = target_msg.document
        fname = (doc.file_name or "").lower()
        if not (fname.endswith(".json") or fname.endswith(".txt")):
            return None, "कृपया केवल .json या .txt फ़ाइल भेजें।", temp_paths

        fd, temp_in = tempfile.mkstemp(prefix="sanskari_quiz_in_", suffix=".tmp")
        os.close(fd)
        temp_paths.append(temp_in)
        try:
            tg_file = await context.bot.get_file(doc.file_id)
            await tg_file.download_to_drive(custom_path=temp_in)
            with open(temp_in, "r", encoding="utf-8", errors="replace") as f_in:
                raw_content = f_in.read()

            if fname.endswith(".json"):
                questions = parse_questions_from_json(raw_content)
            else:
                questions = parse_questions_from_text(raw_content)
        except Exception as exc:
            for fp in temp_paths:
                if os.path.exists(fp):
                    try:
                        os.remove(fp)
                    except OSError:
                        pass
            return None, f"फ़ाइल पढ़ने में त्रुटि: {exc}", []
    else:
        raw_text = (target_msg.text or target_msg.caption or "").strip()
        if not raw_text:
            return None, "मैसेज में कोई प्रश्न या फ़ाइल नहीं मिली।", temp_paths
        try:
            if raw_text.lstrip().startswith(("[", "{")):
                questions = parse_questions_from_json(raw_text)
            else:
                questions = parse_questions_from_text(raw_text)
        except Exception as exc:
            return None, f"टेक्स्ट पढ़ने में त्रुटि: {exc}", temp_paths

    if not questions:
        for fp in temp_paths:
            if os.path.exists(fp):
                try:
                    os.remove(fp)
                except OSError:
                    pass
        return None, "इसमें कोई मान्य प्रश्न और विकल्प नहीं मिले।", []
    return questions, None, temp_paths


async def extract_questions_from_reply(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
) -> Tuple[Optional[List[QuestionItem]], List[str]]:
    msg = update.effective_message
    reply = msg.reply_to_message if msg else None
    if not reply:
        await msg.reply_text(
            "⚠️ कृपया किसी <b>.json / .txt फ़ाइल</b> या <b>प्रश्नों वाले टेक्स्ट मैसेज</b> पर <b>Reply</b> करके कमांड भेजें।",
            parse_mode=ParseMode.HTML,
        )
        return None, []

    questions, err, temp_paths = await extract_questions_from_message(reply, context)
    if err or not questions:
        await msg.reply_text(f"❌ {html.escape(err or 'कोई प्रश्न नहीं मिला।')}", parse_mode=ParseMode.HTML)
        return None, []
    return questions, temp_paths


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

    questions, temp_paths = await extract_questions_from_reply(update, context)
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

    await launch_session_from_questions(
        chat_id=msg.chat_id,
        thread_id=msg.message_thread_id,
        questions=questions[start_idx:end_idx],
        context=context,
        mode=mode,
        duration_sec=duration_sec,
        temp_files=temp_paths,
    )


async def run_scheduled_quiz(job: ScheduledQuizJob, context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        now = datetime.now(IST)
        wait_sec = max(0.0, (job.run_at - now).total_seconds())
        if wait_sec > 0:
            await asyncio.sleep(wait_sec)
        await launch_session_from_questions(
            chat_id=job.chat_id,
            thread_id=job.thread_id,
            questions=job.questions,
            context=context,
            mode=job.mode,
            title_note=f"Scheduled ({job.run_at.strftime('%I:%M %p')})",
        )
    except asyncio.CancelledError:
        return
    finally:
        manager.scheduled_jobs.pop(job.job_id, None)


async def cmd_time(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    msg = update.effective_message
    reply = msg.reply_to_message if msg else None
    if not msg or not reply:
        await msg.reply_text(
            "⚠️ कृपया किसी क्विज़ फ़ाइल या प्रश्नों वाले मैसेज पर <b>Reply</b> करके लिखें:\n"
            "उदाहरण: <code>/time 3:00 pm</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    run_at = parse_clock_time_ist(context.args)
    if not run_at:
        await msg.reply_text(
            "⚠️ कृपया सही समय डालें, जैसे: <code>/time 3:00 pm</code> या <code>/time 15:00</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    questions, err, temp_paths = await extract_questions_from_message(reply, context)
    for fp in temp_paths:
        if os.path.exists(fp):
            try:
                os.remove(fp)
            except OSError:
                pass

    if err or not questions:
        await msg.reply_text(f"❌ {html.escape(err or 'कोई प्रश्न नहीं मिला।')}", parse_mode=ParseMode.HTML)
        return

    # Delete the replied file/message from chat if permitted
    try:
        await context.bot.delete_message(chat_id=reply.chat_id, message_id=reply.message_id)
    except Exception:
        pass

    job_id = uuid.uuid4().hex[:8]
    job = ScheduledQuizJob(
        job_id=job_id,
        chat_id=msg.chat_id,
        thread_id=msg.message_thread_id,
        run_at=run_at,
        questions=questions,
        mode="live",
    )
    manager.scheduled_jobs[job_id] = job
    job.task = asyncio.create_task(run_scheduled_quiz(job, context))

    await msg.reply_text(
        f"⏰ <b>क्विज़ शेड्यूल सेट हो गया!</b>\n"
        f"🕒 समय: <b>{run_at.strftime('%I:%M %p')} IST</b>\n"
        f"📝 कुल प्रश्न: <b>{len(questions)}</b>\n"
        f"⏳ वर्तमान Delay: <b>{manager.default_delay}s</b>",
        parse_mode=ParseMode.HTML,
    )


async def cmd_restart(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    manager.reset_runtime_settings()
    await update.effective_message.reply_text(
        "🔄 <b>सिस्टम रिफ़्रेश हो गया!</b>\n"
        "• सभी सेटिंग्स (Delay, Timer, Shuffle, Target, Neg) और चल रहे/शेड्यूल क्विज़ रीसेट कर दिए गए हैं।\n"
        "• आपके <b>Folders और Saved Tests (/save)</b> पूरी तरह सुरक्षित हैं।",
        parse_mode=ParseMode.HTML,
    )


# ==================== /save FOLDER & TEST BROWSER ====================

def build_save_browser_view(path: List[str]) -> Tuple[str, InlineKeyboardMarkup]:
    node = get_folder_node(SAVE_TREE, path, create=False) or default_save_tree()
    folders = sorted(node.get("folders", {}).keys(), key=str.lower)
    tests = sorted(node.get("tests", {}).keys(), key=str.lower)

    breadcrumb = " / ".join(["🏠 Home"] + [html.escape(p) for p in path])
    text_lines = [
        "📁 <b>संस्कारी क्विज़ लाइब्रेरी (/save)</b>",
        f"📍 स्थान: <b>{breadcrumb}</b>",
        "",
    ]

    if not folders and not tests:
        text_lines.append("<i>इस फ़ोल्डर में अभी कोई सब-फ़ोल्डर या सेव किया गया टेस्ट नहीं है।</i>")
    else:
        text_lines.append("👇 नीचे दिए गए बटन पर क्लिक करें:")

    rows: List[List[InlineKeyboardButton]] = []
    for f_name in folders:
        child_path = path + [f_name]
        tok = register_path(child_path)
        sub_node = node["folders"][f_name]
        sub_f_cnt = len(sub_node.get("folders", {}))
        sub_t_cnt = len(sub_node.get("tests", {}))
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"📁 {f_name} ({sub_f_cnt}📁, {sub_t_cnt}📝)",
                    callback_data=f"sv:dir:{tok}",
                )
            ]
        )

    for t_name in tests:
        test_path = path + [t_name]
        tok = register_path(test_path)
        q_cnt = len(node["tests"][t_name])
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"📝 {t_name} ({q_cnt} Qs)",
                    callback_data=f"sv:tst:{tok}",
                )
            ]
        )

    nav_row: List[InlineKeyboardButton] = []
    if path:
        parent_tok = "root" if len(path) == 1 else register_path(path[:-1])
        nav_row.append(InlineKeyboardButton(text="⬅️ Back", callback_data=f"sv:dir:{parent_tok}"))
        nav_row.append(InlineKeyboardButton(text="🏠 Home", callback_data="sv:dir:root"))
    if nav_row:
        rows.append(nav_row)

    return "\n".join(text_lines), InlineKeyboardMarkup(rows)


def build_test_actions_view(path: List[str]) -> Tuple[str, InlineKeyboardMarkup]:
    folder_path = path[:-1]
    test_name = path[-1]
    node = get_folder_node(SAVE_TREE, folder_path, create=False)
    q_list = (node or {}).get("tests", {}).get(test_name, [])
    tok = register_path(path)
    parent_tok = "root" if not folder_path else register_path(folder_path)

    breadcrumb = " / ".join(["🏠 Home"] + [html.escape(p) for p in path])
    text = (
        f"📝 <b>सेव्ड टेस्ट: {html.escape(test_name)}</b>\n"
        f"📍 स्थान: <b>{breadcrumb}</b>\n"
        f"📊 कुल प्रश्न: <b>{len(q_list)}</b>\n\n"
        "👇 नीचे से विकल्प चुनें:"
    )

    kb = InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(text="▶️ Play Quiz", callback_data=f"sv:play:{tok}")],
            [
                InlineKeyboardButton(text="✏️ Edit Quiz", callback_data=f"sv:edit:{tok}"),
                InlineKeyboardButton(text="🗑️ Remove Quiz", callback_data=f"sv:del:{tok}"),
            ],
            [
                InlineKeyboardButton(text="⬅️ Back", callback_data=f"sv:dir:{parent_tok}"),
                InlineKeyboardButton(text="🏠 Home", callback_data="sv:dir:root"),
            ],
        ]
    )
    return text, kb


async def cmd_save(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    msg = update.effective_message
    if not msg:
        return

    reply = msg.reply_to_message
    args = [a.strip() for a in context.args if a.strip()]

    if not args and not reply:
        text, kb = build_save_browser_view([])
        await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    if reply:
        if not args:
            await msg.reply_text(
                "⚠️ टेस्ट सेव करने के लिए रिप्लाई में नाम भी लिखें:\n"
                "उदाहरण: <code>/save hindi gadhykhand chapter1</code>",
                parse_mode=ParseMode.HTML,
            )
            return

        questions, err, temp_paths = await extract_questions_from_message(reply, context)
        for fp in temp_paths:
            if os.path.exists(fp):
                try:
                    os.remove(fp)
                except OSError:
                    pass

        if err or not questions:
            await msg.reply_text(f"❌ {html.escape(err or 'कोई प्रश्न नहीं मिला।')}", parse_mode=ParseMode.HTML)
            return

        folder_path = args[:-1]
        test_name = args[-1]
        node = get_folder_node(SAVE_TREE, folder_path, create=True)
        assert node is not None
        node["tests"][test_name] = serialize_questions(questions)
        persist_save_tree(SAVE_TREE)

        loc = " / ".join(["Home"] + folder_path + [test_name])
        await msg.reply_text(
            f"✅ टेस्ट सेव हो गया!\n"
            f"📍 स्थान: <b>{html.escape(loc)}</b>\n"
            f"📝 कुल प्रश्न: <b>{len(questions)}</b>\n"
            f"खोलने के लिए <code>/save</code> भेजें।",
            parse_mode=ParseMode.HTML,
        )
        return

    node = get_folder_node(SAVE_TREE, args, create=True)
    assert node is not None
    persist_save_tree(SAVE_TREE)
    loc = " / ".join(["Home"] + args)
    await msg.reply_text(
        f"📁 फ़ोल्डर तैयार हो गया: <b>{html.escape(loc)}</b>\n"
        f"इसके अंदर टेस्ट सेव करने के लिए किसी क्विज़ फ़ाइल/मैसेज पर Reply करके लिखें:\n"
        f"<code>/save {' '.join(args)} test_name</code>",
        parse_mode=ParseMode.HTML,
    )


async def cmd_folderdelete(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    msg = update.effective_message
    if not msg:
        return

    folders = sorted(SAVE_TREE.get("folders", {}).keys(), key=str.lower)
    if not folders:
        await msg.reply_text("ℹ️ डिलीट करने के लिए अभी कोई मुख्य फ़ोल्डर नहीं है।")
        return

    rows: List[List[InlineKeyboardButton]] = []
    for f_name in folders:
        tok = register_path([f_name])
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"🗑️ {f_name}",
                    callback_data=f"fd:del:{tok}",
                )
            ]
        )
    rows.append([InlineKeyboardButton(text="❌ Cancel", callback_data="fd:cancel")])

    await msg.reply_text(
        "🗑️ <b>फ़ोल्डर डिलीट करें</b>\n👇 जिस फ़ोल्डर को सीधे डिलीट करना है उस पर क्लिक करें:",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def cmd_subfolder(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    msg = update.effective_message
    if not msg:
        return

    folders = sorted(SAVE_TREE.get("folders", {}).keys(), key=str.lower)
    if not folders:
        await msg.reply_text("ℹ️ अभी कोई फ़ोल्डर नहीं बना है। पहले <code>/save hindi</code> से फ़ोल्डर बनाएं।", parse_mode=ParseMode.HTML)
        return

    rows: List[List[InlineKeyboardButton]] = []
    for f_name in folders:
        tok = register_path([f_name])
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"📁 {f_name}",
                    callback_data=f"sf:open:{tok}",
                )
            ]
        )
    rows.append([InlineKeyboardButton(text="❌ Cancel", callback_data="sf:cancel")])

    await msg.reply_text(
        "📂 <b>सब-फ़ोल्डर मैनेजर (/subfolder)</b>\n👇 पहले मुख्य फ़ोल्डर चुनें:",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def handle_save_and_folder_callbacks(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.data:
        return
    user = query.from_user
    if not user or not is_admin(user.id):
        await query.answer("केवल Admin/Owner ही इसका उपयोग कर सकते हैं।", show_alert=False)
        return

    data = query.data

    if data.startswith("sv:"):
        parts = data.split(":", 2)
        action = parts[1]
        tok = parts[2] if len(parts) > 2 else "root"
        path = resolve_path(tok)
        if path is None:
            await query.answer("यह बटन पुराना हो गया है, कृपया /save दोबारा भेजें।", show_alert=False)
            return

        if action == "dir":
            text, kb = build_save_browser_view(path)
            await query.answer()
            await query.edit_message_text(text=text, parse_mode=ParseMode.HTML, reply_markup=kb)
            return

        if action == "tst":
            if not path:
                await query.answer()
                return
            text, kb = build_test_actions_view(path)
            await query.answer()
            await query.edit_message_text(text=text, parse_mode=ParseMode.HTML, reply_markup=kb)
            return

        if action == "play":
            if not path:
                await query.answer()
                return
            folder_path = path[:-1]
            test_name = path[-1]
            node = get_folder_node(SAVE_TREE, folder_path, create=False)
            raw_qs = (node or {}).get("tests", {}).get(test_name)
            if not raw_qs:
                await query.answer("यह टेस्ट नहीं मिला।", show_alert=False)
                return
            await query.answer("क्विज़ शुरू हो रहा है...")
            q_items = deserialize_questions(raw_qs)
            chat_id = query.message.chat_id if query.message else user.id
            thread_id = query.message.message_thread_id if query.message else None
            await launch_session_from_questions(
                chat_id=chat_id,
                thread_id=thread_id,
                questions=q_items,
                context=context,
                mode="live",
                title_note=test_name,
            )
            return

        if action == "edit":
            if not path:
                await query.answer()
                return
            PENDING_EDIT_BY_USER[user.id] = list(path)
            loc = " / ".join(["Home"] + path)
            await query.answer()
            await query.edit_message_text(
                text=(
                    f"✏️ <b>टेस्ट एडिट मोड</b>\n"
                    f"📍 स्थान: <b>{html.escape(loc)}</b>\n\n"
                    "अब इस टेस्ट की जगह नई <b>.json / .txt फ़ाइल</b> या <b>प्रश्नों वाला टेक्स्ट मैसेज</b> इसी चैट में भेजें।"
                ),
                parse_mode=ParseMode.HTML,
            )
            return

        if action == "del":
            if not path:
                await query.answer()
                return
            folder_path = path[:-1]
            test_name = path[-1]
            node = get_folder_node(SAVE_TREE, folder_path, create=False)
            if node and test_name in node.get("tests", {}):
                del node["tests"][test_name]
                persist_save_tree(SAVE_TREE)
            await query.answer("🗑️ टेस्ट डिलीट कर दिया गया।", show_alert=False)
            text, kb = build_save_browser_view(folder_path)
            await query.edit_message_text(text=text, parse_mode=ParseMode.HTML, reply_markup=kb)
            return

    if data.startswith("fd:"):
        if data == "fd:cancel":
            await query.answer("रद्द किया गया।")
            await query.edit_message_text("❌ फ़ोल्डर डिलीट रद्द कर दिया गया।")
            return
        parts = data.split(":", 2)
        if len(parts) == 3 and parts[1] == "del":
            path = resolve_path(parts[2])
            if not path:
                await query.answer("कृपया /folderdelete दोबारा भेजें।", show_alert=False)
                return
            f_name = path[0]
            if f_name in SAVE_TREE.get("folders", {}):
                del SAVE_TREE["folders"][f_name]
                persist_save_tree(SAVE_TREE)
                await query.answer("फ़ोल्डर डिलीट हो गया!")
                await query.edit_message_text(
                    f"🗑️ फ़ोल्डर <b>{html.escape(f_name)}</b> को डिलीट कर दिया गया है।",
                    parse_mode=ParseMode.HTML,
                )
            else:
                await query.answer("यह फ़ोल्डर पहले ही डिलीट हो चुका है।", show_alert=False)
            return

    if data.startswith("sf:"):
        if data == "sf:cancel":
            await query.answer("रद्द किया गया।")
            await query.edit_message_text("❌ रद्द कर दिया गया।")
            return
        parts = data.split(":", 2)
        action = parts[1]
        tok = parts[2] if len(parts) > 2 else "root"
        path = resolve_path(tok)
        if path is None:
            await query.answer("कृपया /subfolder दोबारा भेजें।", show_alert=False)
            return

        if action == "open":
            node = get_folder_node(SAVE_TREE, path, create=False)
            subfolders = sorted((node or {}).get("folders", {}).keys(), key=str.lower)
            if not subfolders:
                await query.answer("इसके अंदर कोई सब-फ़ोल्डर नहीं है।", show_alert=False)
                return
            rows: List[List[InlineKeyboardButton]] = []
            for sf_name in subfolders:
                sf_path = path + [sf_name]
                sf_tok = register_path(sf_path)
                rows.append(
                    [
                        InlineKeyboardButton(
                            text=f"📁 {sf_name}",
                            callback_data=f"sf:ask:{sf_tok}",
                        )
                    ]
                )
            rows.append([InlineKeyboardButton(text="❌ Cancel", callback_data="sf:cancel")])
            loc = " / ".join(["Home"] + [html.escape(p) for p in path])
            await query.answer()
            await query.edit_message_text(
                text=f"📂 <b>{loc}</b> के अंदर के सब-फ़ोल्डर:\n👇 डिलीट करने के लिए किसी सब-फ़ोल्डर पर क्लिक करें:",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup(rows),
            )
            return

        if action == "ask":
            if len(path) < 2:
                await query.answer()
                return
            loc = " / ".join(["Home"] + [html.escape(p) for p in path])
            kb = InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            text="⚠️ हाँ, Permanent Delete करें",
                            callback_data=f"sf:confirm:{tok}",
                        )
                    ],
                    [InlineKeyboardButton(text="❌ नहीं, Cancel करें", callback_data="sf:cancel")],
                ]
            )
            await query.answer()
            await query.edit_message_text(
                text=(
                    f"⚠️ <b>Permanent Delete Confirmation</b>\n\n"
                    f"क्या आप वाकई सब-फ़ोल्डर <b>{loc}</b> और इसके अंदर के सभी टेस्ट हमेशा के लिए डिलीट करना चाहते हैं?"
                ),
                parse_mode=ParseMode.HTML,
                reply_markup=kb,
            )
            return

        if action == "confirm":
            if len(path) < 2:
                await query.answer()
                return
            parent_node = get_folder_node(SAVE_TREE, path[:-1], create=False)
            target_sf = path[-1]
            if parent_node and target_sf in parent_node.get("folders", {}):
                del parent_node["folders"][target_sf]
                persist_save_tree(SAVE_TREE)
                loc = " / ".join(["Home"] + [html.escape(p) for p in path])
                await query.answer("Permanent Delete हो गया!")
                await query.edit_message_text(
                    text=f"🗑️ सब-फ़ोल्डर <b>{loc}</b> हमेशा के लिए डिलीट कर दिया गया है।",
                    parse_mode=ParseMode.HTML,
                )
            else:
                await query.answer("सब-फ़ोल्डर नहीं मिला।", show_alert=False)
            return


# ==================== OTHER COMMANDS ====================

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return

    help_text = (
        "✨ 🛠️ <b>संस्कारी क्विज़ बॉट — सम्पूर्ण कमांड मेन्यू</b> 🛠️ ✨\n\n"
        "🎯 <b>क्विज़ शुरू करने के कमांड्स (फ़ाइल या टेक्स्ट के Reply में):</b>\n"
        "• <code>/livequiz</code> — लाइव क्विज़ शुरू करना (प्रतिशत + गलत पर नीचे Explanation)\n"
        "• <code>/livequiz 30m</code> — समय सीमा के साथ लाइव टेस्ट (जैसे <code>30m</code> बाद लॉक व रिज़ल्ट)\n"
        "• <code>/livequiz 1-30</code> — फ़ाइल/टेक्स्ट से चुनिंदा प्रश्न चलाना\n"
        "• <code>/quiz</code> — क्लासिक टेलीग्राम क्विज़ पोल मोड में प्रश्न चलाना\n"
        "• <code>/time 3:00 pm</code> — फ़ाइल/मैसेज के Reply में समय सेट करना (चैट से फ़ाइल हट जाएगी और तय समय पर क्विज़ शुरू होगा)\n\n"
        "📁 <b>फ़ोल्डर व सेव्ड टेस्ट लाइब्रेरी कमांड्स:</b>\n"
        "• <code>/save</code> — सेव किए गए फ़ोल्डर्स और टेस्ट बटन के रूप में खोलना (Play / Edit / Remove)\n"
        "• <code>/save hindi</code> — नया मुख्य फ़ोल्डर बनाना\n"
        "• <code>/save hindi gadhykhand</code> — फ़ोल्डर के अंदर सब-फ़ोल्डर बनाना\n"
        "• <code>/save hindi gadhykhand chapter1</code> <i>(फ़ाइल/टेक्स्ट के Reply में)</i> — टेस्ट सेव करना\n"
        "• <code>/folderdelete</code> — मुख्य फ़ोल्डर चुनकर डिलीट करना\n"
        "• <code>/subfolder</code> — किसी फ़ोल्डर के सब-फ़ोल्डर खोलना और कन्फ़र्म करके परमानेंट डिलीट करना\n\n"
        "⏯️ <b>क्विज़ कंट्रोल कमांड्स:</b>\n"
        "• <code>/pause</code> — चल रहे क्विज़ को अस्थायी रूप से रोकना\n"
        "• <code>/resume</code> — रुके हुए क्विज़ को वहीं से फिर शुरू करना\n"
        "• <code>/skip</code> — मौजूदा प्रतीक्षा छोड़कर तुरंत अगला प्रश्न भेजना\n"
        "• <code>/reveal</code> — लाइव प्रश्नों के प्रतिशत व सही उत्तर तुरंत दिखाना\n"
        "• <code>/stop</code> — क्विज़ समाप्त करना और फ़ाइनल टॉप-3 + स्कोर PDF भेजना\n"
        "• <code>/delquiz</code> — टेस्ट खत्म होने के बाद भेजे गए सभी प्रश्नों को चैट से डिलीट करना\n"
        "• <code>/restart</code> — सभी सेटिंग्स और चल रहे/शेड्यूल क्विज़ रीसेट करना (Folders व Saved Tests सुरक्षित रहेंगे)\n"
        "• <code>/status</code> — मौजूदा प्रश्न संख्या, प्रतिभागी और सेटिंग्स देखना\n\n"
        "⚙️ <b>स्पीड, टारगेट और मार्किंग सेटिंग्स:</b>\n"
        "• <code>/delay &lt;sec&gt;</code> — हर प्रश्न के बीच का गैप (<code>0</code> = तुरंत, <code>10</code> या <code>10s</code> = 10 सेकंड बाद)\n"
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
    manager.session.completed_naturally = True
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
            f"• शेड्यूल क्विज़: <b>{len(manager.scheduled_jobs)}</b>  |  कुल एडमिन: <b>{len(ADMIN_IDS)}</b>"
        )
    await update.effective_message.reply_text(txt, parse_mode=ParseMode.HTML)


async def cmd_delay(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text(
            "उपयोग: <code>/delay 0</code> (तुरंत) या <code>/delay 10</code> या <code>/delay 10s</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    val = parse_seconds_input(context.args[0], min_val=0, max_val=3600)
    if val is None:
        await update.effective_message.reply_text(
            "उपयोग: <code>/delay 0</code> (तुरंत) या <code>/delay 10</code> या <code>/delay 10s</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    manager.default_delay = val
    manager.save_snapshot()
    if manager.session and not manager.session.stopped:
        manager.session.delay_sec = val
    if val == 0:
        await update.effective_message.reply_text("⚡ डिले हटा दिया गया है (<b>0 सेकंड</b>) — अब प्रश्न तुरंत-तुरंत आएंगे।", parse_mode=ParseMode.HTML)
    else:
        await update.effective_message.reply_text(f"⏳ हर प्रश्न के बीच गैप <b>{val} सेकंड</b> सेट किया गया।", parse_mode=ParseMode.HTML)


async def cmd_timer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args:
        await update.effective_message.reply_text("उपयोग: <code>/timer 20</code>", parse_mode=ParseMode.HTML)
        return
    val = parse_seconds_input(context.args[0], min_val=5, max_val=600)
    if val is None:
        await update.effective_message.reply_text("उपयोग: <code>/timer 20</code> (5 से 600 सेकंड)", parse_mode=ParseMode.HTML)
        return
    manager.default_timer = val
    manager.save_snapshot()
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
    manager.save_snapshot()
    if manager.session and not manager.session.stopped:
        manager.session.shuffle_enabled = enabled
    await update.effective_message.reply_text(f"🔀 शफ़ल मोड <b>{'ON' if enabled else 'OFF'}</b> किया गया।", parse_mode=ParseMode.HTML)


async def cmd_target(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if not context.args:
        manager.default_target_chat = None
        manager.default_target_thread = None
        manager.save_snapshot()
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
    manager.save_snapshot()
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
    manager.save_snapshot()
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


async def handle_incoming_messages(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    msg = update.effective_message
    if not user or not msg:
        return

    if is_admin(user.id) and user.id in PENDING_EDIT_BY_USER:
        target_path = PENDING_EDIT_BY_USER.pop(user.id)
        questions, err, temp_paths = await extract_questions_from_message(msg, context)
        for fp in temp_paths:
            if os.path.exists(fp):
                try:
                    os.remove(fp)
                except OSError:
                    pass

        if err or not questions:
            await msg.reply_text(
                f"❌ एडिट विफल: {html.escape(err or 'कोई प्रश्न नहीं मिला।')}\n"
                "दोबारा एडिट करने के लिए <code>/save</code> से Edit Quiz चुनें।",
                parse_mode=ParseMode.HTML,
            )
            return

        folder_path = target_path[:-1]
        test_name = target_path[-1]
        node = get_folder_node(SAVE_TREE, folder_path, create=True)
        assert node is not None
        node["tests"][test_name] = serialize_questions(questions)
        persist_save_tree(SAVE_TREE)

        loc = " / ".join(["Home"] + target_path)
        await msg.reply_text(
            f"✅ टेस्ट अपडेट हो गया!\n"
            f"📍 स्थान: <b>{html.escape(loc)}</b>\n"
            f"📝 नए प्रश्नों की संख्या: <b>{len(questions)}</b>",
            parse_mode=ParseMode.HTML,
        )
        return

    if is_admin(user.id) and msg.text and msg.text.strip().lower().startswith("/folder delete"):
        await cmd_folderdelete(update, context)
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
    app.add_handler(CommandHandler("time", cmd_time))
    app.add_handler(CommandHandler("restart", cmd_restart))
    app.add_handler(CommandHandler("save", cmd_save))
    app.add_handler(CommandHandler("folderdelete", cmd_folderdelete))
    app.add_handler(CommandHandler("subfolder", cmd_subfolder))
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
    app.add_handler(CallbackQueryHandler(handle_save_and_folder_callbacks, pattern=r"^(sv|fd|sf):"))
    app.add_handler(PollAnswerHandler(handle_poll_answer))
    app.add_handler(MessageHandler(filters.ALL, handle_incoming_messages), group=99)

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
