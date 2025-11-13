import os
import concurrent.futures
from openai import OpenAI

API_KEY = os.getenv("OPENAI_API_KEY")
API_BASE = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

if not API_KEY:
    raise ValueError("请设置 OPENAI_API_KEY 环境变量")

client = OpenAI(base_url=API_BASE, api_key=API_KEY)


INPUT_DIR = "data/lean_test_set"
OUTPUT_DIR = "results/txt_test_translations"
MODEL = "gpt-4-turbo"  # 建议使用更新的模型
MAX_WORKERS = 10

os.makedirs(OUTPUT_DIR, exist_ok=True)


def process_file(file_path):
    try:
        filename = os.path.basename(file_path)
        txt_filename = os.path.splitext(filename)[0] + ".txt"
        output_path = os.path.join(OUTPUT_DIR, txt_filename)

        if os.path.exists(output_path):
            print(f"跳过已处理文件: {filename}")
            return filename

        with open(file_path, "r", encoding="utf-8") as f:
            lean_code = f.read()

        response = client.chat.completions.create(
            model=MODEL,
            messages=[
                {"role": "system",
                 "content": "You are a Lean4 proof translator. Translate Lean4 proofs into clear English explanations."},
                {"role": "user", "content": f"""Translate the following Lean4 code into English explanations. 
Strictly follow this format:

-- Proof content:
-- 1. [Problem Restatement] ...
-- 2. [Key Idea] ...
-- 3. [Proof] ...
-- 4. [Conclusion] ...

Code:
{lean_code}
"""}
            ]
        )

        translated_text = response.choices[0].message.content

        with open(output_path, "w", encoding="utf-8") as f:
            f.write(translated_text)

        print(f"处理完成: {filename} → {txt_filename}")
        return filename

    except Exception as e:
        print(f"处理 {file_path} 时出错: {e}")
        return None


def main():
    if not os.path.isdir(INPUT_DIR):
        print(f"错误：输入目录不存在 {INPUT_DIR}")
        return

    lean_files = [os.path.join(INPUT_DIR, f) for f in os.listdir(INPUT_DIR) if f.endswith(".lean")]

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = [executor.submit(process_file, f) for f in lean_files]
        for future in concurrent.futures.as_completed(futures):
            future.result()


if __name__ == "__main__":
    main()

