import Mathlib

/- ================================================================
Day22 · 偏元数学新线 · 最小可出门验证
对象层：Prenary = ℂ
动作层：ActionResidual δ₀
核心：动作留差 ε 不可清零，δ₀=0 退化
================================================================ -/

-- ① 对象层：偏元数就是复数
abbrev Prenary := ℂ

-- ② 动作层：动作残差
structure ActionResidual (δ₀ : ℝ) where
  ε : ℝ
  h_pos : 0 < ε
  h_lt : ε < δ₀

-- ③ 残差正性：动作残差恒正
theorem residual_pos {δ₀ : ℝ} (r : ActionResidual δ₀) :
    0 < ActionResidual.ε r :=
  ActionResidual.h_pos r

-- ④ 残差严格小于上界 δ₀
theorem residual_lt_delta {δ₀ : ℝ} (r : ActionResidual δ₀) :
    ActionResidual.ε r < δ₀ :=
  ActionResidual.h_lt r

-- ⑤ 残差非零：动作留差不可清零
theorem residual_nonzero {δ₀ : ℝ} (r : ActionResidual δ₀) :
    ActionResidual.ε r ≠ 0 := by
  have hpos : 0 < ActionResidual.ε r := ActionResidual.h_pos r
  linarith

-- ⑥ 动作层非平凡：δ₀ > 0 时存在动作残差
theorem action_non_trivial {δ₀ : ℝ} (hδ : δ₀ > 0) :
    ∃ (_r : ActionResidual δ₀), True := by
  let ε : ℝ := δ₀ / 2
  have hpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hlt : ε < δ₀ := by
    dsimp [ε]
    linarith
  exact ⟨{ ε := ε, h_pos := hpos, h_lt := hlt }, trivial⟩

-- ⑦ 退化：δ₀ = 0 时，动作残差不存在
theorem action_degenerate (_r : ActionResidual 0) :
    False := by
  have hpos : 0 < ActionResidual.ε _r := ActionResidual.h_pos _r
  have hlt : ActionResidual.ε _r < 0 := ActionResidual.h_lt _r
  linarith

-- ⑧ 退化等价：δ₀ = 0 时动作层为空
theorem action_degenerate_empty :
    (∀ _r : ActionResidual 0, False) := by
  intro _r
  exact action_degenerate _r

-- ⑨ 经典返回：δ₀ = 0 时无动作残差，只有经典对象
theorem classical_recovery :
    (ActionResidual 0 → False) := by
  intro _r
  exact action_degenerate _r

-- ⑩ 上界不可达：任何动作残差都严格小于 δ₀
theorem delta_unreachable {δ₀ : ℝ} (r : ActionResidual δ₀) :
    ActionResidual.ε r ≠ δ₀ := by
  intro h
  have hlt : ActionResidual.ε r < δ₀ := ActionResidual.h_lt r
  rw [h] at hlt
  linarith
