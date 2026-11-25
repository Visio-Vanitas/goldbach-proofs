import Mathlib

theorem PEqualNP.Outside.L_goldbach_u1n_lorentz_reflection : ∀ (N : ℕ) (a : ℕ → ℝ), 2 ≤ N → let z : ℕ → ℂ := fun ξ => ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)); (∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2 + (z 0) ^ 2 = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)) ∧ (‖z 0‖ ^ 2 - ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖ ^ 2 = 2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 - ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2) := by
  intro N a hN
  dsimp only
  set z : ℕ → ℂ := fun ξ =>
    ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N,
      (a n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsqrt : ((N : ℝ).sqrt : ℂ)⁻¹ ^ 2 * (N : ℂ) = 1 := by
    have hsq : ((N : ℝ).sqrt : ℂ) ^ 2 = (N : ℂ) := by
      exact_mod_cast Real.sq_sqrt hNpos.le
    rw [inv_pow, hsq, inv_mul_cancel₀ hNne]
  have hgeom : ∀ k : ℤ, (-(N : ℤ) < k ∧ k < 2 * (N : ℤ)) →
      ∑ ξ ∈ Finset.range N, Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ) / (N : ℂ)) =
        if k = 0 ∨ k = (N : ℤ) then (N : ℂ) else 0 := by
    intro k hk
    split_ifs with h0
    · rcases h0 with rfl | rfl
      · simp
      · have hsum1 : ∑ ξ ∈ Finset.range N,
            Complex.exp (-2 * Real.pi * Complex.I * ((N : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) =
            ∑ _ξ ∈ Finset.range N, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          have harg : -2 * Real.pi * Complex.I * ((N : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ) =
              (ξ : ℂ) * (-2 * Real.pi * Complex.I) := by
            push_cast; field_simp [hNne]
          rw [harg, Complex.exp_nat_mul]
          have hbase : Complex.exp (-2 * Real.pi * Complex.I) = 1 := by
            rw [show (-2 * Real.pi * Complex.I : ℂ) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
              Complex.exp_int_mul_two_pi_mul_I]
          rw [hbase, one_pow]
        rw [hsum1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · set ω : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ))
      have hsum_ω : ∑ ξ ∈ Finset.range N,
          Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ) / (N : ℂ)) =
          ∑ ξ ∈ Finset.range N, ω ^ ξ := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← Complex.exp_nat_mul]
        congr 1
        ring
      rw [hsum_ω]
      have hωne : ω ≠ 1 := by
        intro hω1
        rw [Complex.exp_eq_one_iff] at hω1
        obtain ⟨m, hm⟩ := hω1
        have hpiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have hcast : -(k : ℂ) = (m : ℂ) * (N : ℂ) := by
          have h1 : (-2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) * (N : ℂ) / (2 * Real.pi * Complex.I) =
              -(k : ℂ) := by field_simp [hNne, hpiI]
          have h2 : (m : ℂ) * (2 * Real.pi * Complex.I) * (N : ℂ) / (2 * Real.pi * Complex.I) =
              (m : ℂ) * (N : ℂ) := by field_simp [hpiI]
          calc -(k : ℂ) = (-2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) * (N : ℂ) / (2 * Real.pi * Complex.I) := h1.symm
            _ = (m : ℂ) * (2 * Real.pi * Complex.I) * (N : ℂ) / (2 * Real.pi * Complex.I) := by rw [hm]
            _ = (m : ℂ) * (N : ℂ) := h2
        have hint : -k = m * (N : ℤ) := by exact_mod_cast hcast
        rcases hk with ⟨hkl, hku⟩
        have hNz : (0 : ℤ) < (N : ℤ) := by omega
        have hml : -1 ≤ m := by
          by_contra hm'
          have : m ≤ -2 := by omega
          nlinarith
        have hmu : m ≤ 0 := by
          by_contra hm'
          have : 1 ≤ m := by omega
          nlinarith
        have hm_range : m = 0 ∨ m = -1 := by omega
        rcases hm_range with rfl | rfl
        · exact absurd (Or.inl (by omega)) h0
        · exact absurd (Or.inr (by omega)) h0
      rw [geom_sum_eq hωne]
      have hωN : ω ^ N = 1 := by
        dsimp [ω]
        rw [← Complex.exp_nat_mul]
        have harg : (N : ℂ) * (-2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) =
            (-k : ℤ) * (2 * Real.pi * Complex.I) := by
          push_cast; field_simp [hNne]
        rw [harg, Complex.exp_int_mul_two_pi_mul_I]
      rw [hωN, sub_self, zero_div]
  have hmerge : ∀ f : ℕ → ℂ, ∑ ξ ∈ Finset.Ico 1 N, f ξ + f 0 = ∑ ξ ∈ Finset.range N, f ξ := by
    intro f
    rw [Finset.range_eq_Ico]
    have h0N : 0 < N := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot h0N f]
    ring
  constructor
  · change ∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2 + (z 0) ^ 2 = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)
    rw [hmerge fun ξ => (z ξ) ^ 2]
    have hterm : ∀ ξ ∈ Finset.range N, (z ξ) ^ 2 =
        ((N : ℝ).sqrt : ℂ)⁻¹ ^ 2 * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
          (a n : ℂ) * (a m : ℂ) *
            Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
      intro ξ _
      dsimp [z]
      rw [mul_pow, sq (∑ n ∈ Finset.Ico 1 N, _), Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hexp : Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ)) =
          Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [mul_mul_mul_comm, hexp]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
    have hswap : (∑ n ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, ∑ m ∈ Finset.Ico 1 N,
        (a n : ℂ) * (a m : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ))) =
        ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
          ∑ ξ ∈ Finset.range N,
            Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.mul_sum]
    rw [hswap]
    have hinner : ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
          ∑ ξ ∈ Finset.range N,
            Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) =
        (N : ℂ) * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (a (N - n) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ico] at hn
      have hm_cond : ∀ m ∈ Finset.Ico 1 N,
          ∑ ξ ∈ Finset.range N,
            Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) =
          if m = N - n then (N : ℂ) else 0 := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [hgeom ((n : ℤ) + (m : ℤ)) ⟨by omega, by omega⟩]
        split_ifs with hcond hmn
        · rfl
        · exact absurd (by omega : m = N - n) hmn
        · exact absurd (Or.inr (by omega : (n : ℤ) + (m : ℤ) = (N : ℤ))) hcond
        · rfl
      calc ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
            ∑ ξ ∈ Finset.range N,
              Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) + (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ))
        _ = ∑ m ∈ Finset.Ico 1 N, if m = N - n then (a n : ℂ) * (a m : ℂ) * (N : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hm_cond m hm]
          split_ifs <;> ring
        _ = (a n : ℂ) * (a (N - n) : ℂ) * (N : ℂ) := by
          rw [Finset.sum_ite_eq']
          split_ifs with hmem
          · rfl
          · exact absurd (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hmem
        _ = (N : ℂ) * ((a n : ℂ) * (a (N - n) : ℂ)) := by ring
    rw [hinner, ← mul_assoc, hsqrt, one_mul]
    push_cast
    rfl
  · change ‖z 0‖ ^ 2 - ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖ ^ 2 =
      2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 - ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2
    have hz0 : ‖z 0‖ ^ 2 = (N : ℝ)⁻¹ * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 := by
      have hz0_eq : z 0 = ((((N : ℝ).sqrt)⁻¹ * ∑ n ∈ Finset.Ico 1 N, a n : ℝ) : ℂ) := by
        dsimp [z]
        simp only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one]
        push_cast
        rfl
      rw [hz0_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow,
        Real.sq_sqrt hNpos.le]
    have hmergeR : ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖ ^ 2 + ‖z 0‖ ^ 2 = ∑ ξ ∈ Finset.range N, ‖z ξ‖ ^ 2 := by
      have h0N : 0 < N := by omega
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h0N (fun ξ => ‖z ξ‖ ^ 2)]
      ring
    have hfull : ∑ ξ ∈ Finset.range N, ‖z ξ‖ ^ 2 = ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2 := by
      have hterm : ∀ ξ ∈ Finset.range N, ((‖z ξ‖ ^ 2 : ℝ) : ℂ) =
          ((N : ℝ).sqrt : ℂ)⁻¹ ^ 2 * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
            (a n : ℂ) * (a m : ℂ) *
              Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
        intro ξ _
        have hns : ((‖z ξ‖ ^ 2 : ℝ) : ℂ) = z ξ * starRingEnd ℂ (z ξ) := by
          rw [Complex.mul_conj']
          push_cast
          rfl
        rw [hns]
        dsimp [z]
        rw [map_mul, map_inv₀, map_sum, Complex.conj_ofReal]
        have hsum_conj : ∑ m ∈ Finset.Ico 1 N,
            starRingEnd ℂ ((a m : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ))) =
            ∑ m ∈ Finset.Ico 1 N,
              (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
          congr 2
          simp [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]
        rw [hsum_conj, mul_mul_mul_comm, ← sq (((N : ℝ).sqrt : ℂ)⁻¹), Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hexp : Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ)) =
            Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [mul_mul_mul_comm, hexp]
      have hC : ((∑ ξ ∈ Finset.range N, ‖z ξ‖ ^ 2 : ℝ) : ℂ) = ((∑ n ∈ Finset.Ico 1 N, (a n) ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum, Complex.ofReal_sum]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
        have hswap : (∑ n ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, ∑ m ∈ Finset.Ico 1 N,
            (a n : ℂ) * (a m : ℂ) *
              Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ))) =
            ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
              ∑ ξ ∈ Finset.range N,
                Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← Finset.mul_sum]
        rw [hswap]
        have hinner : ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
              ∑ ξ ∈ Finset.range N,
                Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) =
            (N : ℂ) * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Ico] at hn
          have hm_cond : ∀ m ∈ Finset.Ico 1 N,
              ∑ ξ ∈ Finset.range N,
                Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) =
              if m = n then (N : ℂ) else 0 := by
            intro m hm
            rw [Finset.mem_Ico] at hm
            rw [hgeom ((n : ℤ) - (m : ℤ)) ⟨by omega, by omega⟩]
            split_ifs with hcond hmn
            · rfl
            · exact absurd (by omega : m = n) hmn
            · exact absurd (Or.inl (by omega : (n : ℤ) - (m : ℤ) = 0)) hcond
            · rfl
          calc ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) *
                ∑ ξ ∈ Finset.range N,
                  Complex.exp (-2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ))
            _ = ∑ m ∈ Finset.Ico 1 N, if m = n then (a n : ℂ) * (a m : ℂ) * (N : ℂ) else 0 := by
              refine Finset.sum_congr rfl fun m hm => ?_
              rw [hm_cond m hm]
              split_ifs <;> ring
            _ = (a n : ℂ) * (a n : ℂ) * (N : ℂ) := by
              rw [Finset.sum_ite_eq']
              split_ifs with hmem
              · rfl
              · exact absurd (Finset.mem_Ico.mpr hn) hmem
            _ = (N : ℂ) * (a n : ℂ) ^ 2 := by ring
        rw [hinner, ← mul_assoc, hsqrt, one_mul]
        push_cast
        rfl
      exact Complex.ofReal_injective hC
    have hdiv : 2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 = 2 * ((N : ℝ)⁻¹ * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2) := by
      ring
    linarith
