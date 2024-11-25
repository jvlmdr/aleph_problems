import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped Nat

lemma Finset.sum_range_add_one (n : ℕ) :
    ∑ i in range n, (i + 1) = n * (n + 1) / 2 := by
  suffices ∑ i in range n, (i + 1) = ∑ i in range (n + 1), i by
    simp [this, Finset.sum_range_id, mul_comm n]
  simp [Finset.sum_range_succ']

lemma Nat.two_dvd_mul_add_one (n : ℕ) : 2 ∣ n * (n + 1) := by
  cases n.even_or_odd with
  | inl h =>
    rw [even_iff_two_dvd] at h
    exact dvd_mul_of_dvd_left h (n + 1)
  | inr h =>
    refine dvd_mul_of_dvd_right ?_ _
    rw [odd_iff_exists_bit1] at h
    rcases h with ⟨m, hm⟩
    rw [hm]
    rw [add_assoc _ 1 1]
    rw [← mul_add 2 m 1]
    exact Nat.dvd_mul_right 2 (m + 1)

theorem factorial_lt_add_one_div_two_pow_n {n : ℕ} (hn : 1 < n) :
    n ! < ((n + 1) / 2 : ℝ) ^ n := by
  have hn_pos := Nat.zero_lt_of_lt hn

  rw [← Real.strictMonoOn_log.lt_iff_lt]
  rotate_left
  · simp [Nat.factorial_pos]
  · rw [Set.mem_Ioi]
    refine pow_pos ?_ _
    rw [div_pos_iff_of_pos_right zero_lt_two]
    norm_cast
    exact Nat.add_one_pos _
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rw [Real.log_prod _ _ (fun _ _ ↦ by norm_cast)]
  rw [Real.log_pow]

  have h := strictConcaveOn_log_Ioi.lt_map_sum
    (t := Finset.range n)
    (w := fun _ ↦ (n⁻¹ : ℝ))
    (p := fun i : ℕ ↦ (i + 1 : ℝ))
    (fun _ _ ↦ by simp [hn_pos])
    (by simp [hn_pos.ne'])
    (fun i _ ↦ by
      simp only [Set.mem_Ioi]
      norm_cast
      simp)
    ⟨0, by simp [hn_pos], 1, by simp [hn], by simp⟩

  simp only [smul_eq_mul] at h
  simp only [← Finset.mul_sum] at h
  rw [inv_mul_lt_iff₀ (by norm_cast)] at h

  refine lt_of_lt_of_eq h ?_
  rw [mul_right_inj' (M₀ := ℝ) (by norm_cast; exact hn_pos.ne')]
  refine congrArg _ ?_
  norm_cast
  rw [Finset.sum_range_add_one]

  rw [Nat.cast_div_charZero n.two_dvd_mul_add_one]
  rw [mul_div]
  push_cast
  refine congrArg₂ _ ?_ rfl
  rw [← mul_assoc]
  rw [inv_mul_cancel₀ (by norm_cast; exact hn_pos.ne')]
  simp
