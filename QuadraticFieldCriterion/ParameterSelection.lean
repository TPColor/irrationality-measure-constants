import QuadraticFieldCriterion.DimensionLimits
import QuadraticFieldCriterion.DeterminantTermBounds
import QuadraticFieldCriterion.LogDenominators

/-! # Choosing the scales before the approximation weights -/

namespace QuadraticField

theorem natFloor_ratCast (r : ℚ) : ⌊(r : ℝ)⌋₊ = ⌊r⌋₊ := by
  simp only [← Int.floor_toNat, Rat.floor_cast]

theorem natCeil_ratCast (r : ℚ) : ⌈(r : ℝ)⌉₊ = ⌈r⌉₊ := by
  simp only [← Int.ceil_toNat, Rat.ceil_cast]

theorem rational_truncation_denominator_cost {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {H F v₀ : ℚ} (hH : 0 ≤ H) (hF : 0 ≤ F) (hv₀ : 0 < v₀) :
    Real.log ((∏ i, (Nat.lcmUpto ⌈F * w i / v₀⌉₊) ^ ⌊H / w i⌋₊ : ℕ) : ℝ) ≤
      (Real.log 4 + 4) * (H : ℝ) *
        ((F : ℝ) * m / (v₀ : ℝ) + ∑ i, 1 / (w i : ℝ)) := by
  have h := truncation_denominator_cost (fun i => (w i : ℝ))
    (fun i => by exact_mod_cast hw i) (show (0 : ℝ) ≤ H by exact_mod_cast hH)
    (show (0 : ℝ) ≤ F by exact_mod_cast hF) (show (0 : ℝ) < v₀ by exact_mod_cast hv₀)
  have ht : ∀ i, ⌈(F : ℝ) * (w i : ℝ) / (v₀ : ℝ)⌉₊ = ⌈F * w i / v₀⌉₊ := by
    intro i
    rw [← Rat.cast_mul, ← Rat.cast_div, natCeil_ratCast]
  have hn : ∀ i, ⌊(H : ℝ) / (w i : ℝ)⌋₊ = ⌊H / w i⌋₊ := by
    intro i
    rw [← Rat.cast_div, natFloor_ratCast]
  simpa only [ht, hn, Fintype.card_fin] using h

theorem exists_criterion_scales (ν : ℝ) (θ A B C : ℚ) (η ε height : ℝ) (ω : ℂ)
    (_hν : 0 < ν) (_hθ : 0 < θ) (hA : 0 < A) (hAB : A < B) (hC : 1 < C)
    (hCB : C * B < 1) (hBCT : B < C * θ) (hη : 0 < η) (hε : 0 < ε)
    (g : ℕ → ℝ) (margin : ℝ) :
    ∃ F : ℚ, ∃ m : ℕ, ∃ wstar : ℚ,
      0 < F ∧ 1 / θ ≤ F ∧ ν / (F : ℝ) < ε ∧ 0 < m ∧ 0 < wstar ∧
      (((Real.log 4 + 4) * (F : ℝ)) * m + 2 * Real.log 2) /
          jetWeight θ B C m +
        (height + 4 * (1 + ‖ω‖)) * ((centreCount C m : ℝ) / degreeWeight B m) < ε ∧
      margin < (Real.log 2 / 4) * (η ^ 2 * ((B : ℝ) / A) ^ m / (2 * (m + 1))) ∧
      g m / (wstar : ℝ) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (1 / (θ : ℝ)) (ν / ε)))
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN)
  have hF : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  have hFθ : (1 / θ : ℚ) ≤ (N : ℚ) := by
    have h := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hN
    exact_mod_cast h.le
  have hνF : ν / (N : ℝ) < ε := by
    apply (div_lt_iff₀ hNpos).mpr
    have h := (div_lt_iff₀ hε).mp (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hN)
    nlinarith
  obtain ⟨m, hm, herr, hmargin⟩ := exists_dimension_with_arbitrary_margin
    (show (0 : ℝ) < A by exact_mod_cast hA)
    (show (A : ℝ) < B by exact_mod_cast hAB)
    (show (1 : ℝ) < C by exact_mod_cast hC)
    (show (C : ℝ) * B < 1 by exact_mod_cast hCB)
    (show (B : ℝ) < C * θ by exact_mod_cast hBCT)
    hη (show 0 < Real.log 2 / 4 by positivity) hε
    ((Real.log 4 + 4) * N) (2 * Real.log 2) (height + 4 * (1 + ‖ω‖)) margin
  obtain ⟨W, hW⟩ := exists_nat_gt (max 1 (g m / ε))
  have hWpos : (0 : ℝ) < W := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hW)
  have hg : g m / (W : ℝ) < ε := by
    apply (div_lt_iff₀ hWpos).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hW)
    nlinarith
  refine ⟨N, m, W, hF, hFθ, ?_, hm, ?_, ?_, hmargin, ?_⟩
  · simpa only [Rat.cast_natCast] using hνF
  · exact_mod_cast hWpos
  · simpa only [Rat.cast_natCast] using herr
  · simpa only [Rat.cast_natCast] using hg

noncomputable def criterionArithmeticError {m : ℕ} (w : Fin m → ℝ)
    (F v₀ θ w₀ wstar height K : ℝ) : ℝ :=
  (Real.log 4 + 4) * (F * m / v₀ + ∑ i, 1 / w i) + K * height / w₀ + θ / wstar

theorem combined_criterion_error_le {m : ℕ} (w : Fin m → ℝ)
    (F v₀ θ w₀ wstar height K ν E R : ℝ) (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ w i) :
    criterionArithmeticError w F v₀ θ w₀ wstar height K +
        translationCost ν E F v₀ wstar + holomorphicCost R w₀ wstar v₀ ≤
      ((Real.log 4 + 4) * F * m + 2 * Real.log 2) / v₀ +
        (K * height + R) / w₀ + ν / F +
        ((Real.log 4 + 4) * m + θ + Real.log (4 * E) + Real.log (2 * R)) / wstar := by
  have hsum : (∑ i, 1 / w i) ≤ (m : ℝ) / wstar := by
    calc
      _ ≤ ∑ _i : Fin m, 1 / wstar := Finset.sum_le_sum (fun i _ =>
        one_div_le_one_div_of_le hwstar (hmin i))
      _ = _ := by simp [div_eq_mul_inv]
  have hΛ : 0 ≤ Real.log 4 + 4 := by positivity
  have h := mul_le_mul_of_nonneg_left hsum hΛ
  unfold criterionArithmeticError translationCost holomorphicCost
  simp only [div_eq_mul_inv] at h ⊢
  linear_combination h

end QuadraticField
