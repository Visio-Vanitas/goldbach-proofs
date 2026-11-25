import Mathlib

theorem PEqualNP.Outside.L_goldbach_separable_kernel_phase_barrier : ∀ (m : ℕ) (L : ℝ) (γ : ℕ → ℝ) (W₁ W₂ : ℕ → ℂ), let E : ℕ → ℂ := fun j => Complex.exp (((γ j * L : ℝ) : ℂ) * Complex.I); let cross : (ℕ → ℂ) → ℝ := fun W => ∑ j ∈ Finset.range m, ∑ l ∈ (Finset.range m).erase j, (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re; cross W₁ + cross W₂ = ‖∑ j ∈ Finset.range m, W₁ j * E j‖ ^ 2 + ‖∑ j ∈ Finset.range m, W₂ j * E j‖ ^ 2 - ∑ j ∈ Finset.range m, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2) ∧ -(∑ j ∈ Finset.range m, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2)) ≤ cross W₁ + cross W₂ := by
  intro m L γ W₁ W₂
  dsimp only
  set E : ℕ → ℂ := fun j => Complex.exp (((γ j * L : ℝ) : ℂ) * Complex.I)
  have hcross : ∀ W : ℕ → ℂ,
      (∑ j ∈ Finset.range m, ∑ l ∈ (Finset.range m).erase j,
        (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re) =
      ‖∑ j ∈ Finset.range m, W j * E j‖ ^ 2 - ∑ j ∈ Finset.range m, ‖W j‖ ^ 2 := by
    intro W
    set u : ℕ → ℂ := fun j => W j * E j
    have hnormE : ∀ j, ‖E j‖ = 1 := fun j => Complex.norm_exp_ofReal_mul_I (γ j * L)
    have hdiag : ∀ j, (u j * starRingEnd ℂ (u j)).re = ‖W j‖ ^ 2 := by
      intro j
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, hnormE j, mul_one]
    have hfull : (∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, (u j * starRingEnd ℂ (u l)).re) =
        ‖∑ j ∈ Finset.range m, u j‖ ^ 2 := by
      have hre : ((∑ j ∈ Finset.range m, u j) * starRingEnd ℂ (∑ l ∈ Finset.range m, u l)).re =
          ‖∑ j ∈ Finset.range m, u j‖ ^ 2 := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [← hre, Finset.sum_mul, map_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Complex.re_sum]
    have hrow : ∀ j ∈ Finset.range m,
        (u j * starRingEnd ℂ (u j)).re +
          ∑ l ∈ (Finset.range m).erase j, (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re =
        ∑ l ∈ Finset.range m, (u j * starRingEnd ℂ (u l)).re := by
      intro j hj
      have hcongr : ∑ l ∈ (Finset.range m).erase j,
          (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re =
          ∑ l ∈ (Finset.range m).erase j, (u j * starRingEnd ℂ (u l)).re := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [u, map_mul]
        ring_nf
      rw [hcongr]
      exact Finset.add_sum_erase (Finset.range m) (fun l => (u j * starRingEnd ℂ (u l)).re) hj
    have hsum_row := Finset.sum_congr rfl hrow
    rw [Finset.sum_add_distrib, hfull] at hsum_row
    have hdiag_sum : ∑ j ∈ Finset.range m, (u j * starRingEnd ℂ (u j)).re =
        ∑ j ∈ Finset.range m, ‖W j‖ ^ 2 := Finset.sum_congr rfl fun j _ => hdiag j
    linarith
  have h1 := hcross W₁
  have h2 := hcross W₂
  have hsum : ∑ j ∈ Finset.range m, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2) =
      (∑ j ∈ Finset.range m, ‖W₁ j‖ ^ 2) + ∑ j ∈ Finset.range m, ‖W₂ j‖ ^ 2 :=
    Finset.sum_add_distrib
  constructor
  · linarith
  · have hnn : 0 ≤ ‖∑ j ∈ Finset.range m, W₁ j * E j‖ ^ 2 + ‖∑ j ∈ Finset.range m, W₂ j * E j‖ ^ 2 := by
      positivity
    linarith
