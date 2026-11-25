import Mathlib

theorem PEqualNP.Outside.L_goldbach_cell_lp_dual_certificate : ∀ (C K : ℕ) (M s t : ℕ → ℝ) (y B : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (U : ℝ), (∀ c ∈ Finset.range C, 0 ≤ M c) → (∀ c ∈ Finset.range C, (∑ k ∈ Finset.range K, y k * A k c) - s c ≤ t c) → (∀ k ∈ Finset.range K, B k ≤ y k * ∑ c ∈ Finset.range C, M c * A k c) → (∑ c ∈ Finset.range C, M c * s c ≤ U) → ∑ k ∈ Finset.range K, B k - U ≤ ∑ c ∈ Finset.range C, M c * t c := by
  intro C K M s t y B A U hM hdual hB hs
  have h1 : (∑ c ∈ Finset.range C, M c * ((∑ k ∈ Finset.range K, y k * A k c) - s c)) ≤
      ∑ c ∈ Finset.range C, M c * t c :=
    Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hdual c hc) (hM c hc)
  have h2 : (∑ c ∈ Finset.range C, M c * ((∑ k ∈ Finset.range K, y k * A k c) - s c)) =
      (∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c) -
        ∑ c ∈ Finset.range C, M c * s c := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => by ring
  have h3 : ∑ k ∈ Finset.range K, B k ≤ ∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c :=
    Finset.sum_le_sum fun k hk => hB k hk
  linarith
