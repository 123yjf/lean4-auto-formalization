import os
import json
import re
import numpy as np
from typing import List, Dict
from openai import OpenAI

API_KEY = os.getenv("OPENAI_API_KEY")
API_BASE = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

if not API_KEY:
    raise ValueError("请设置 OPENAI_API_KEY 环境变量")

client = OpenAI(base_url=API_BASE, api_key=API_KEY)

DIR_TEST = "results/txt_test_translations"      # 测试集的翻译文本
DIR_REF = "results/txt_reference_translations" # 参考集的翻译文本
OUTPUT_DIR = "results/similarity_reports"      # 相似度报告输出目录

# 模型与参数
MODEL = "text-embedding-3-large"
BATCH_SIZE = 16
THRESHOLD = 0.8  # 相似度阈值
# ===========================================

os.makedirs(OUTPUT_DIR, exist_ok=True)

def normalize_text(text: str) -> str:
    if not text: return ""
    text = re.sub(r"\s+", " ", text).strip()
    return text

def read_text_file(path: str) -> str:
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        raw = f.read()
    return normalize_text(raw)

def chunked(iterable: List, size: int):
    for i in range(0, len(iterable), size):
        yield iterable[i:i+size]

def get_embeddings_batch(texts: List[str]) -> List[List[float]]:
    embeddings = []
    if not texts: return embeddings
    for batch in chunked(texts, BATCH_SIZE):
        resp = client.embeddings.create(model=MODEL, input=batch)
        embeddings.extend([item.embedding for item in resp.data])
    return embeddings

def cosine_sim(a: np.ndarray, b: np.ndarray) -> float:
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    if na == 0 or nb == 0: return 0.0
    return float((a @ b) / (na * nb))

def main():
    test_files = {os.path.splitext(f)[0]: os.path.join(DIR_TEST, f)
                  for f in os.listdir(DIR_TEST) if f.lower().endswith(".txt")}
    ref_files = {os.path.splitext(f)[0]: os.path.join(DIR_REF, f)
                 for f in os.listdir(DIR_REF) if f.lower().endswith(".txt")}

    common_basenames = sorted(list(test_files.keys() & ref_files.keys()))
    if not common_basenames:
        print("[WARN] 两个目录中没有找到任何同名 .txt 文件。")
        return

    print(f"[Info] 找到 {len(common_basenames)} 个共同文件进行比较。")

    texts_test = [read_text_file(test_files[bn]) for bn in common_basenames]
    texts_ref = [read_text_file(ref_files[bn]) for bn in common_basenames]

    print("[Info] 获取测试集文本的 embeddings...")
    emb_test = get_embeddings_batch(texts_test)
    print("[Info] 获取参考集文本的 embeddings...")
    emb_ref = get_embeddings_batch(texts_ref)

    results: Dict[str, float] = {}
    for i, bn in enumerate(common_basenames):
        sim = cosine_sim(np.array(emb_test[i]), np.array(emb_ref[i]))
        results[bn] = sim

    ge_threshold = {k: v for k, v in results.items() if v >= THRESHOLD}
    lt_threshold = {k: v for k, v in results.items() if v < THRESHOLD}

    threshold_str = str(int(THRESHOLD * 100))
    out_all = os.path.join(OUTPUT_DIR, "all_similarities.json")
    out_ge = os.path.join(OUTPUT_DIR, f"similar_ge{threshold_str}.json")
    out_lt = os.path.join(OUTPUT_DIR, f"similar_lt{threshold_str}.json")

    def round_dict(d: Dict[str, float]) -> Dict[str, float]:
        return {k: round(v, 6) for k, v in d.items()}

    with open(out_all, "w", encoding="utf-8") as f: json.dump(round_dict(results), f, indent=2)
    with open(out_ge, "w", encoding="utf-8") as f: json.dump(round_dict(ge_threshold), f, indent=2)
    with open(out_lt, "w", encoding="utf-8") as f: json.dump(round_dict(lt_threshold), f, indent=2)

    print(f"[Done] 总比较数: {len(results)}")
    print(f"[Done] >= {THRESHOLD*100:.0f}%: {len(ge_threshold)}")
    print(f"[Done] <  {THRESHOLD*100:.0f}%: {len(lt_threshold)}")
    print(f"[Saved] {out_all}")
    print(f"[Saved] {out_ge}")
    print(f"[Saved] {out_lt}")

if __name__ == "__main__":
    main()

