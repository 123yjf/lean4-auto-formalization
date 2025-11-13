import os
import re

def remove_comments(file_path):
    try:
        with open(file_path, 'r', encoding='utf-8') as file:
            content = file.read()
        content = re.sub(r'/-\s*.*?\s*-/', '', content, flags=re.DOTALL)
        content = re.sub(r'--.*', '', content)

        with open(file_path, 'w', encoding='utf-8') as file:
            file.write(content.strip())
        print(f"清理注释完成: {file_path}")
    except Exception as e:
        print(f"处理 {file_path} 时出错: {e}")

def process_folder(folder_path):
    if not os.path.isdir(folder_path):
        print(f"错误：输入目录不存在 {folder_path}")
        return

    for root, _, files in os.walk(folder_path):
        for file in files:
            if file.endswith('.lean'):
                file_path = os.path.join(root, file)
                remove_comments(file_path)

if __name__ == "__main__":
    folder_path = 'data/lean_test_set'
    print(f"开始清理目录 '{folder_path}' 中的 Lean 文件注释...")
    process_folder(folder_path)
    print("所有文件处理完毕。")

