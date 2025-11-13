# semantic_validator.py
# -*- coding: utf-8 -*-
"""
输入：题目名 problem_name、待判定的 Lean4 代码目录 lean_dir、参考翻译目录 ori_dir
功能：
  1) 读取 lean_dir/<problem_name>.lean
  2) 去除所有注释（支持嵌套）
  3) 用 LLM 翻译为固定四段格式的英文说明
  4) 读取 ori_dir/<problem_name>.txt
  5) 计算 embedding 相似度（整体 + 分段）
  6) 输出 True/False，并附带理由与改进建议

用法（CLI）：
  # 假设从项目根目录运行
  python src/semantic_validator.py --name "AMC12B_2019_P12" ^
      --lean_dir "data/lean_test_set" ^
      --ori_dir "results/txt_reference_translations"

Agent 内调用（Python）：
  from semantic_validator import validate_semantics
  ok, report = validate_semantics(problem_name, ori_dir, lean_dir)
"""

import os
import re
import json
import argparse
from typing import Dict, Tuple, List
import numpy as np

try:
    from openai import OpenAI
except ImportError:
    raise RuntimeError("请先安装 openai 包：pip install openai")

API_BASE = os.environ.get("OPENAI_API_BASE", "https://api.openai.com/v1")
API_KEY = os.environ.get("OPENAI_API_KEY")
CHAT_MODEL = os.environ.get("CHAT_MODEL", "gpt-4-turbo")
EMB_MODEL = os.environ.get("EMB_MODEL", "text-embedding-3-large")

if not API_KEY:
    raise ValueError("请设置 OPENAI_API_KEY 环境变量")

THRESHOLD = float(os.environ.get("SEMANTIC_THRESHOLD", "0.76"))

_client = OpenAI(base_url=API_BASE, api_key=API_KEY)

def remove_line_comments(s: str) -> str:
    # 移除形如 "-- ..." 的行注释
    return re.sub(r"--.*", "", s)


def remove_block_comments_nested(s: str) -> str:
    """
    移除 Lean 的 /- -/ 块注释（支持嵌套）
    简单栈机实现，避免正则无法处理嵌套的问题
    """
    i, n = 0, len(s)
    out = []
    depth = 0
    while i < n:
        if i + 1 < n and s[i] == '/' and s[i + 1] == '-' and (i == 0 or s[i - 1] != '\\'):
            # 进入块注释
            depth += 1
            i += 2
            continue
        if depth > 0 and i + 1 < n and s[i] == '-' and s[i + 1] == '/':
            # 退出块注释
            depth = max(0, depth - 1)
            i += 2
            continue
        if depth == 0:
            out.append(s[i])
        i += 1
    return "".join(out)


def strip_comments(lean_code: str) -> str:
    # 先移除块注释，再移除行注释，最后清理空行
    no_block = remove_block_comments_nested(lean_code)
    no_line = remove_line_comments(no_block)
    # 压缩多余空白
    no_line = re.sub(r"[ \t]+$", "", no_line, flags=re.MULTILINE)
    no_line = re.sub(r"\n{3,}", "\n\n", no_line)
    return no_line.strip()


def normalize_text(text: str) -> str:
    if not text:
        return ""
    text = re.sub(r"\s+", " ", text).strip()
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    text = re.sub(r"\b0+(\d+)\b", r"\1", text)
    text = text.replace("×", "*").replace("÷", "/")
    text = text.replace("（", "(").replace("）", ")")
    text = text.replace("⇒", "=>").replace("→", "=>")
    return text.strip()


def embed(texts: List[str]) -> List[np.ndarray]:
    if not texts: return []
    resp = _client.embeddings.create(model=EMB_MODEL, input=texts)
    out: List[np.ndarray] = []
    for item in resp.data:
        out.append(np.array(item.embedding, dtype=np.float32))
    return out


def cosine_sim(a: np.ndarray, b: np.ndarray) -> float:
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    if na == 0 or nb == 0:
        return 0.0
    return float((a @ b) / (na * nb))


_TRANSLATE_SYSTEM = (
    "You are a Lean4 proof translator. Translate Lean4 proofs into clear English explanations. "
    "Output ONLY the following template. No extra commentary."
)

_TRANSLATE_TEMPLATE = """Translate the following Lean4 code into English explanations.
Strictly follow this exact format:

-- Proof content:
-- 1. [Problem Restatement] ...
-- 2. [Key Idea] ...
-- 3. [Proof] ...
-- 4. [Conclusion] ...

Code:
{code}
"""


def translate_lean_to_fixed_text(lean_code_no_comments: str) -> str:
    msg = _TRANSLATE_TEMPLATE.format(code=lean_code_no_comments)
    resp = _client.chat.completions.create(
        model=CHAT_MODEL,
        messages=[
            {"role": "system", "content": _TRANSLATE_SYSTEM},
            {"role": "user", "content": msg}
        ],
        temperature=1,
    )
    return resp.choices[0].message.content.strip()


_SECTION_KEYS = ["[Problem Restatement]", "[Key Idea]", "[Proof]", "[Conclusion]"]


def split_into_sections(fixed_text: str) -> Dict[str, str]:
    fixed_text = normalize_text(fixed_text)
    sections = {k: "" for k in _SECTION_KEYS}
    pattern = r"--\s*\d+\.\s*(\[.*?\])\s*(.*?)(?=--\s*\d+\.|\Z)"
    for m in re.finditer(pattern, fixed_text, flags=re.DOTALL | re.IGNORECASE):
        key_raw = m.group(1).strip()
        val = m.group(2).strip()
        for k in _SECTION_KEYS:
            if k.lower() in key_raw.lower():
                sections[k] = val
                break
    return sections


# ... [此处再次省略未修改的函数定义，直到 _main] ...

def best_match_section(candidate_text: str, ori_text: str) -> Tuple[str, float, Dict[str, float], float]:
    cand_norm = normalize_text(candidate_text)
    ori_norm = normalize_text(ori_text)

    cand_emb, ori_full_emb = embed([cand_norm, ori_norm])

    full_sim = cosine_sim(cand_emb, ori_full_emb)

    ori_secs = split_into_sections(ori_text)
    sec_sims: Dict[str, float] = {}

    for key in _SECTION_KEYS:
        sec = ori_secs.get(key, "")
        if sec:
            sec_emb = embed([normalize_text(sec)])[0]
            sec_sims[key] = cosine_sim(cand_emb, sec_emb)
        else:
            sec_sims[key] = 0.0

    best_sec, best_sec_sim = "N/A", 0.0
    if sec_sims:
        best_sec = max(sec_sims, key=sec_sims.get)
        best_sec_sim = sec_sims[best_sec]

    return best_sec, best_sec_sim, sec_sims, full_sim


def detect_simple_issues(lean_code_no_comments: str) -> List[str]:
    tips = []
    if re.search(r"\bsorry\b|\badmit\b", lean_code_no_comments):
        tips.append("检测到 `sorry/admit`，应提供完整证明并移除占位。")
    if re.search(r"\baxiom\b", lean_code_no_comments, flags=re.IGNORECASE):
        tips.append("请勿引入 `axiom` 公理，改用已知引理或可证明的引理。")
    return tips


SECTION_THRESHOLD = 0.76
CRITICAL_SECTIONS = ["[Problem Restatement]"]


def validate_semantics(problem_name: str, ori_dir: str, lean_dir: str) -> Tuple[bool, Dict]:
    lean_path = os.path.join(lean_dir, f"{problem_name}.lean")
    if not os.path.exists(lean_path):
        raise FileNotFoundError(f"未找到 Lean 文件：{lean_path}")

    with open(lean_path, "r", encoding="utf-8", errors="ignore") as f:
        lean_code = f.read()

    cleaned = strip_comments(lean_code)
    translated = translate_lean_to_fixed_text(cleaned)

    ori_path = os.path.join(ori_dir, f"{problem_name}.txt")
    if not os.path.exists(ori_path):
        raise FileNotFoundError(f"未找到对照文件：{ori_path}")

    with open(ori_path, "r", encoding="utf-8", errors="ignore") as f:
        ori_text = f.read()

    best_sec, best_sec_sim, sec_sims, full_sim = best_match_section(translated, ori_text)

    critical_ok = all(sec_sims.get(sec, 0.0) >= SECTION_THRESHOLD for sec in CRITICAL_SECTIONS)

    simple_issues = detect_simple_issues(cleaned)
    ok = critical_ok and not simple_issues

    similarity_report = (
            "Section similarities:\n" +
            "\n".join([f"{k}: {v:.3f}" for k, v in sec_sims.items()]) +
            f"\nFull similarity: {full_sim:.3f}, Best section: {best_sec} ({best_sec_sim:.3f})"
    )

    improve_prompt = f"""
You are a Lean4 code reviewer.
Here is the Lean4 code (comments removed):
{cleaned}

Its English explanation (four-section format):
{translated}

The reference original explanation:
{ori_text}

Similarity analysis:
{similarity_report}

Task:
1. Identify weaknesses or mismatches compared to the reference.
2. Suggest **concrete improvements** in natural language.
3. Provide an **improved Lean4 code snippet** (only modified parts if small).
4. Keep your output concise, and within 500 words total.
"""

    try:
        resp = _client.chat.completions.create(
            model=CHAT_MODEL,
            messages=[{"role": "system", "content": "You are an expert Lean4 code proof reviewer."},
                      {"role": "user", "content": improve_prompt}],
            temperature=0.5,
        )
        gpt_advice = resp.choices[0].message.content.strip()
    except Exception as e:
        gpt_advice = f"(GPT 改进建议生成失败: {e})"

    advice = simple_issues + [gpt_advice]

    report = {
        "reason": (
                f"关键段落相似度: " +
                ", ".join([f"{sec}={sec_sims.get(sec, 0.0):.3f}" for sec in CRITICAL_SECTIONS]) +
                f"，阈值={SECTION_THRESHOLD:.3f}。 " + ("存在 'sorry' 或 'axiom'" if simple_issues else "")
        ),
        "threshold": THRESHOLD,
        "full_similarity": round(float(full_sim), 6),
        "best_section": best_sec,
        "best_section_similarity": round(float(best_sec_sim), 6),
        "section_similarities": {k: round(float(v), 6) for k, v in sec_sims.items()},
        "advice": advice,
        "translated_text": translated,
    }
    return ok, report


def _main():
    parser = argparse.ArgumentParser(description="Lean 语义一致性判定")
    parser.add_argument("--name", required=True, help="题目名 (不带 .lean 后缀)")
    parser.add_argument("--ori_dir", required=True, help="参考翻译文本目录 (相对路径)")
    parser.add_argument("--lean_dir", required=True, help="Lean4 代码目录 (相对路径)")
    parser.add_argument("--json", action="store_true", help="以 JSON 格式输出报告")
    args = parser.parse_args()

    try:
        ok, report = validate_semantics(args.name, args.ori_dir, args.lean_dir)
        if args.json:
            print(json.dumps({"ok": ok, **report}, ensure_ascii=False, indent=2))
        else:
            print(f"OK: {ok}")
            print(f"Reason: {report['reason']}")
            print("\n—— 分段相似度 ——")
            for k, v in report["section_similarities"].items():
                print(f"{k:>22}: {v:.3f}")
            if report["advice"]:
                print("\n—— 改进建议 ——")
                for i, tip in enumerate(report["advice"], 1):
                    print(f"{i}. {tip}")
    except FileNotFoundError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")


if __name__ == "__main__":
    _main()

