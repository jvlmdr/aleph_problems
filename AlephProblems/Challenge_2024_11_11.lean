import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

-- https://aleph0.substack.com/p/how-to-self-study-real-analysis-a

namespace AlephProblems
namespace Challenge_2024_11_11

theorem sum_inv_pow_two_lt_two (n : ℕ) : ∑ k in .range n, (2 ^ k : ℝ)⁻¹ < 2 := by
  simp only [← inv_pow]
  rw [geom_sum_eq (x := (2⁻¹ : ℝ))]
  · rw [div_lt_iff_of_neg]
    · rw [mul_sub, ← div_eq_mul_inv, div_self two_ne_zero, mul_one]
      rw [lt_tsub_iff_left, add_sub, one_add_one_eq_two]
      simp
    · rw [sub_neg]
      exact inv_lt_one_of_one_lt₀ one_lt_two
  · simp

theorem pow_two_le_factorial_succ : 2 ^ k ≤ k.succ.factorial := by
  have := Nat.factorial_mul_pow_le_factorial (m := 1) (n := k)
  simpa [add_comm 1] using this

-- Main theorem
theorem sum_inv_factorial_lt_three (n : ℕ) : ∑ k in .range n, (k.factorial : ℝ)⁻¹ < 3 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    rw [Nat.factorial_zero, Nat.cast_one, inv_one]
    rw [← two_add_one_eq_three]
    rw [add_lt_add_iff_right]
    refine lt_of_le_of_lt ?_ (sum_inv_pow_two_lt_two n)
    refine Finset.sum_le_sum ?_
    intro k hk
    rw [inv_le_inv₀]
    · rw [← Nat.cast_ofNat, ← Nat.cast_pow]
      norm_cast
      exact pow_two_le_factorial_succ
    · simp [Nat.factorial_pos]
    · simp

end Challenge_2024_11_11
end AlephProblems
