import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_cutoff_freeze_budget : ∀ (I : Finset ℕ) (K : ℕ) (b : ℕ → ℕ) (f : ℕ → ℂ) (r y : ℕ → ℝ) (G : ℕ → ℝ → ℂ), (∀ m ∈ I, b m < K) → (∀ m ∈ I, ‖f m‖ ≤ 1) → let B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j); ‖∑ m ∈ I, f m * G m (r m)‖ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ j ∈ Finset.range K, ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖ ∧ (∑ j ∈ Finset.range K, Real.sqrt ((B j).card : ℝ)) ≤ Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ) := by
  intro I K b f r y G hb hf
  dsimp only
  set B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j)
  constructor
  · have hsplit : ∑ m ∈ I, f m * G m (r m) = ∑ j ∈ Finset.range K, ∑ m ∈ B j, f m * G m (r m) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro m hm
      exact Finset.mem_range.mpr (hb m hm)
    rw [hsplit]
    calc ‖∑ j ∈ Finset.range K, ∑ m ∈ B j, f m * G m (r m)‖
      _ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (r m)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range K,
          (‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have heq : ∑ m ∈ B j, f m * G m (r m) =
            (∑ m ∈ B j, f m * G m (y j)) + ∑ m ∈ B j, f m * (G m (r m) - G m (y j)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => by ring
        rw [heq]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        have hmI : m ∈ I := (Finset.mem_filter.mp hm).1
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hf m hmI)
      _ = _ := Finset.sum_add_distrib
  · have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range K) (fun _ => (1 : ℝ))
      (fun j => Real.sqrt ((B j).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    have hsq : ∑ j ∈ Finset.range K, (Real.sqrt ((B j).card : ℝ)) ^ 2 = (I.card : ℝ) := by
      have hcard : I.card = ∑ j ∈ Finset.range K, (B j).card :=
        Finset.card_eq_sum_card_fiberwise fun m hm => Finset.mem_range.mpr (hb m hm)
      rw [hcard, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => Real.sq_sqrt (Nat.cast_nonneg _)
    rwa [hsq] at hcs
