# FirstTheoryForBH

硼氢化物综述部分论证的 Rust / Verus 形式化验证。

- [中文说明与模型边界](formal-verification/README.md)
- [证明源码](formal-verification/material_proofs.rs)
- [验证结果](formal-verification/logs/verification-summary.json)
- [错误命题的具体反例](formal-verification/negative-controls/COUNTEREXAMPLES.txt)

保存的验证记录：32 个验证项通过，0 个错误；5 个错误命题均被拒绝。32 包括辅助引理，不代表 32 条独立材料学定理。

本项目验证指定数学模型中的逻辑关系，不包含 DFT 或实验验证。

## 复现准备

仓库不包含本地二进制工具链。当前 verify.py 使用 macOS ARM64 的固定目录布局。运行前需按 [Verus 官方安装说明](https://github.com/verus-lang/verus/blob/main/INSTALL.md) 准备以下文件：

- `formal-verification/tooling/verus-arm64-macos/`：Verus 0.2026.11.02.8bf68ee 发行包及附带的 Z3 4.16.0。
- `formal-verification/tooling/cargo/bin/`：rustup / cargo 入口。
- `formal-verification/tooling/rustup/`：Rust 1.99.1-aarch64-apple-darwin 工具链。

准备完成后运行 `python3 formal-verification/verify.py`。其他平台需调整脚本中的工具路径。日志是原执行记录，公开副本中的工作区绝对路径已替换为 `<workspace>`；源码保持原样。
