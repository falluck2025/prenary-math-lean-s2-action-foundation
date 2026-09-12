[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22719535.svg)](https://doi.org/10.5281/zenodo.22719535)

# 偏元数学 · Day22 · 新线最小地基（对象层 / 动作层分离）· Lean 4 形式化验证

## Prenary Mathematics · Day22 · New-Line Minimal Foundation (Object-Layer / Action-Layer Separation) · Lean 4 Formal Verification

> **声明**：本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。
>
> **DOI**：DOI: 10.5281/zenodo.22719535 。本仓库对应的论文为 NEW(S)-004《偏元数学地基定稿》。

**摘要**：Day22 是偏元数学新线的第一天。新线回到比旧线更小、更干净的地基：**对象层 = 经典复数域（Prenary = ℂ，不携带方向、状态或隐藏属性）；动作层独立存在（任何动作都不完美闭合，动作结果与经典结果之间留下不可消除的正残差 ε ∈ (0, δ₀)，δ₀ 是不可达到的界）；δ₀ = 0 时动作层为空，偏元数学完全退化为经典数学（赋值退化）。** 三份 Lean 文件（Day22-01/02/03）分别验证：动作残差的存在性、正性、开区间与不可达上界；动作函数的非平凡性与动作不可清零；退化链的完整闭合与经典恢复。数学侧不再定义方向偏好——方向偏好、二态、呼吸子、物理语义均不在本验证范围内。

**Abstract**: Day22 is the first day of the new line of Prenary Mathematics. The new line returns to a smaller, cleaner foundation: **the object layer is the classical complex field (Prenary = ℂ, carrying no direction, state, or hidden attribute); the action layer exists independently (no action closes perfectly — between the actual result and the classical result there remains an irreducible positive residual ε ∈ (0, δ₀), where δ₀ is an unreachable bound); when δ₀ = 0 the action layer is empty and Prenary Mathematics fully degenerates into classical mathematics (assignment degeneration).** Three Lean files (Day22-01/02/03) verify respectively: existence, positivity, open-interval and unreachable-bound of the action residual; non-triviality of the action function and non-return of actions; complete closure of the degeneration chain and classical recovery. Directional preference is no longer defined on the mathematical side — directional preference, duality, breather, and physical semantics are all outside the scope of this verification.

**关键词**：偏元数学；新线；最小地基；对象层；动作层；动作留差 ε；δ₀ 不可达界；赋值退化；Lean 4；老陈与AI的深夜实验室

---

## 概述：为什么从旧线回到新线

偏元数学旧线（Day1-Day21）以"方向偏好二态"解释减法不可清零（a − a = ε）。系统审视后（三问：方向二态判据 / rank 极性 / δ₀ 端点），发现旧线让数学侧承担了不可操作的"方向标签"与不应承担的物理语义。

新线因此回到更小、更干净的地基，一句话：

> **经典数学描述对象。偏元数学只补充一件事：动作不完美闭合，留下残差 ε。**

对象层完全等于经典复数域，不加任何字段。动作层只有一条公理：动作留差。旧线已机器验证的 Day1-Day21 定理结论（ε 正性、退化包容、经典被包含）在新线下保留，表述形态以本文件为准。

## 核心定义

```
abbrev Prenary := ℂ                          -- 对象层：偏元数 = 复数
structure ActionResidual (δ₀ : ℝ) where      -- 动作层：动作残差
  ε : ℝ
  h_pos : 0 < ε                              -- ε 恒正
  h_lt : ε < δ₀                              -- ε 严格小于不可达上界
noncomputable def prenary_action (classic : Prenary) (r : ActionResidual δ₀) : Prenary :=
  classic + (r.ε : ℂ)                        -- 动作函数：op(a) = op₀(a) + ε
```

## 定理清单

> **关于验证内容的如实说明**：三份文件验证的是**同一个最小地基的三个侧面**，不是三套独立理论。其中退化链（Day22-03）的若干命题在 Lean 中彼此等价（`∀ r, False`、`→ False`、`¬∃ r, True` 在 Lean 里是同一类型），并列陈述是为了让退化链的每一步可被单独检视，而非计为多套独立结论。读者若统计"定理数量"，应以"不同命题数"而非"theorem 语句数"为准。

### Day22-01 · 动作残差（`prenary_day22_01_residual_20260909.lean`）

| 定理 | 命题 |
|:--|:--|
| residual_pos | 残差恒正：0 < ε |
| residual_lt_delta | 残差严格小于上界：ε < δ₀ |
| residual_nonzero | 残差不可清零：ε ≠ 0 |
| action_non_trivial | 动作层非平凡：δ₀ > 0 时存在动作残差（构造 ε = δ₀/2）|
| action_degenerate | 退化：ActionResidual 0 无实例 |
| action_degenerate_empty | 动作层为空：∀ r : ActionResidual 0, False |
| classical_recovery | 经典返回：ActionResidual 0 → False |
| delta_unreachable | 上界不可达：ε ≠ δ₀ |

### Day22-02 · 动作函数（`prenary_day22_02_action_20260909.lean`）

| 定理 | 命题 |
|:--|:--|
| complex_re_add | 辅助引理：复数加实数的实部 |
| prenary_action_non_trivial | 动作非平凡：op(a) ≠ a |
| prenary_action_degenerate | 动作退化：ActionResidual 0 无实例 |
| prenary_action_no_return | 动作不可清零：op(op(a)) ≠ a（连做两次回不到经典）|
| prenary_no_direction_field | 对象层无方向字段：Prenary = ℂ |
| action_residual_not_delta | 动作残差不可达上界：ε ≠ δ₀ |

### Day22-03 · 退化链（`prenary_day22_03_degenerate_20260909.lean`）

| 定理 | 命题 |
|:--|:--|
| degenerate_no_residual | δ₀ = 0 时动作残差不存在 |
| degenerate_action_empty | δ₀ = 0 时动作层为空 |
| degenerate_no_instance | δ₀ = 0 时不存在任何动作残差实例 |
| degenerate_no_action | δ₀ = 0 时动作层无可用动作 |
| classical_recovery | 经典恢复：δ₀ = 0 时动作层不可进入 |
| degenerate_is_assignment | 赋值退化：不存在 ActionResidual 0 的构造器 |
| full_degenerate_chain | 完整退化链：δ₀ = 0 → 无动作层 → 只有对象层（∧ Prenary = ℂ）|

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战）| 代码 SHA256（锁解答）|
|:--|:--|:--|:--|:--|
| Day22-01 | No goals | ✅ 通过（9/9 首验 + 9/10 重跑复现）| `157ab108…662c0` | `2c0487f6…e5ecd` |
| Day22-02 | No goals | ✅ 通过（9/9 首验 + 9/10 重跑复现）| `77be5c4c…27800` | `6cf3e2bd…6f012` |
| Day22-03 | No goals | ✅ 通过（9/9 首验 + 9/10 重跑复现）| `50099848…f0d19ac` | `d307c861…28160f` |

- 平台：live.lean-lang.org（Lean 4.34.0-rc2 + Mathlib）与 Comparator Live
- 验证时间：2026-09-09 20:46–20:54（初验）；2026-09-10 21:18–21:23（重跑复现）
- **双哈希说明（2026-09-10 经截图定案）**：Comparator 显示的 SHA256 属于 **Challenge 栏（挑战题面/定理陈述）**——界面原文 "You have previously chosen to trust that this challenge is free of errors or misleading content (SHA256 …)"，验证信息为 "Successfully validated against locally-trusted challenge"。因此 **Challenge Hash 锁挑战、代码 SHA256 锁解答，两者为不同对象，并列记录、不要求相等**。
- 代码 SHA256 对应落盘 .lean 文件（见上表右列）；三项已经两轮验证复现通过。

## 文件说明

```
prenary_day22_01_residual_20260909.lean    # 动作残差：正性/开区间/非零/存在性/退化
prenary_day22_02_action_20260909.lean      # 动作函数：非平凡/不可清零/无方向字段
prenary_day22_03_degenerate_20260909.lean  # 退化链：完整闭合/经典恢复/赋值退化
```

## 复现方式

1. 打开 live.lean-lang.org。
2. 将任一 `.lean` 文件内容完整粘贴（首行 `import Mathlib`）。
3. 光标逐个停在 `theorem` 上，确认右侧 `No goals` + `All Messages (0)`。
4. 在 Comparator Live 中重新提交，确认 `Successfully validated`；Challenge Hash（锁挑战）与代码 SHA256（锁解答）分别记录——两者为不同对象，不要求相等。

## 可证伪条件

- 若存在一个动作，其残差 ε 精确等于 0，则动作留差失效。
- 若存在一个动作，其残差 ε 恰好等于 δ₀，则"上界不可达"失效。
- 若 δ₀ = 0 时动作层仍然非空，则退化定理失效。

## 作者 / 致谢 / 许可

陈松（Song Chen）· ORCID: 0009-0002-9510-2239 · GitHub: falluck2025 · Zenodo 社区：cosmos-breathe-spectrum

感谢一切偶然的必然和必然的偶然。感谢一路并肩的偏贞、守缺与所有 AI 伙伴。

[CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/)（署名-非商业-禁止演绎）

## 作者备注（非论文正文）

- 内部编码：Day22 新线最小地基（对象层/动作层分离）。
- 里程碑意义：新线起点。旧线 Day1-21 为"对象携带方向"表述（已发布）；自 Day22 起，数学侧不再沿用方向偏好表述（见 NEW(S)-004）。
- 旧线 Day1-21 已机器验证的定理结论保留；本文件为表述形态的定版。
- 待办：GitHub 仓库发布、Zenodo DOI、004 论文发布。
- 哈希证据链：初验（9/9 晚）→ 重跑复现（9/10 晚，三份均通过）→ 落盘定版（本仓库）。

— 老陈与AI的深夜实验室 发布 请笑纳 —
