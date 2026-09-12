import Mathlib

/- ================================================================
Day22-02 · 动作函数与动作留差
对象层：Prenary = ℂ
动作层：ActionResidual δ₀
动作函数：op(a) = op₀(a) + ε
核心：动作非平凡、动作不可清零
================================================================ -/

-- ① 对象层：偏元数就是复数
abbrev Prenary := ℂ

-- ② 动作层：动作残差
structure ActionResidual (δ₀ : ℝ) where
  ε : ℝ
  h_pos : 0 < ε
  h_lt : ε < δ₀

-- ③ 动作函数：经典结果 + 动作留差
noncomputable def prenary_action (classic : Prenary) (r : ActionResidual δ₀) : Prenary :=
  classic + (r.ε : ℂ)

-- 辅助引理：复数加实部等于实部加实数
lemma complex_re_add (c : ℂ) (x : ℝ) :
    ((c + (x : ℂ)).re) = c.re + x := by
  simp

-- ④ 动作非平凡
theorem prenary_action_non_trivial {δ₀ : ℝ}
    (classic : Prenary) (r : ActionResidual δ₀) :
    prenary_action classic r ≠ classic := by
  intro h
  have hε : r.ε = 0 := by
    have hre := congrArg Complex.re h
    have hre' : ((classic + (r.ε : ℂ)).re) = classic.re := by
      simpa [prenary_action] using hre
    have hre'' : classic.re + r.ε = classic.re := by
      simpa [complex_re_add] using hre'
    linarith
  have hpos : 0 < r.ε := r.h_pos
  linarith

-- ⑤ 动作退化
theorem prenary_action_degenerate (_r : ActionResidual 0) :
    False := by
  have hpos : 0 < ActionResidual.ε _r := ActionResidual.h_pos _r
  have hlt : ActionResidual.ε _r < 0 := ActionResidual.h_lt _r
  linarith

-- ⑥ 动作不可清零
theorem prenary_action_no_return {δ₀ : ℝ}
    (classic : Prenary) (r : ActionResidual δ₀) :
    prenary_action (prenary_action classic r) r ≠ classic := by
  intro h
  have hsum : r.ε + r.ε = 0 := by
    have hre := congrArg Complex.re h
    have hre' : ((classic + (r.ε : ℂ) + (r.ε : ℂ)).re) = classic.re := by
      simpa [prenary_action] using hre
    have hre'' : classic.re + r.ε + r.ε = classic.re := by
      simpa [complex_re_add] using hre'
    linarith
  have hpos : 0 < r.ε := r.h_pos
  linarith

-- ⑦ 对象层无方向字段
theorem prenary_no_direction_field :
    (Prenary = ℂ) := by
  rfl

-- ⑧ 动作残差不可达上界
theorem action_residual_not_delta {δ₀ : ℝ}
    (r : ActionResidual δ₀) :
    ActionResidual.ε r ≠ δ₀ := by
  intro h
  have hlt : ActionResidual.ε r < δ₀ := ActionResidual.h_lt r
  rw [h] at hlt
  linarith
