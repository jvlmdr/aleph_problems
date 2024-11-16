import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic

-- https://aleph0.substack.com/p/a-cute-problem-about-reciprocals

namespace AlephProblems.Challenge_2024_11_11

theorem exists_distinct_inv_add_inv_eq_inv {n : ℕ} (hn : 1 < n) :
    ∃ x y : ℕ, ¬x = y ∧ (x⁻¹ : ℝ) + (y⁻¹ : ℝ) = (n⁻¹ : ℝ) := by
  refine ⟨n + 1, n * (n + 1), And.intro ?_ ?_⟩
  · rw [← ne_eq]
    conv => lhs; rw [← Nat.one_mul (n + 1)]
    rw [Nat.mul_ne_mul_left n.succ_ne_zero]
    exact Nat.ne_of_lt hn
  · rw [inv_add_inv]
    · rw [← one_div]
      rw [div_eq_div_iff]
      · norm_cast
        rw [one_mul]
        rw [mul_rotate']
        rw [add_comm (n + 1)]
        rw [← Nat.add_one_mul]
        exact Nat.mul_comm _ _
      · norm_cast
        simp [Nat.not_eq_zero_of_lt hn]
      · norm_cast
        exact Nat.not_eq_zero_of_lt hn
    · norm_cast
    · norm_cast
      rw [← ne_eq]
      refine Nat.mul_ne_zero ?_ ?_
      · exact Nat.not_eq_zero_of_lt hn
      · exact n.succ_ne_zero

end AlephProblems.Challenge_2024_11_11
