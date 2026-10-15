import QuadraticFieldCriterion.ArithmeticEstimate
import QuadraticFieldCriterion.FullAnalyticEstimate
import QuadraticFieldCriterion.DegreeErrors

/-! # Normalizing the concrete determinant estimates -/

namespace QuadraticField

theorem normalized_log_norm_le {z : ℂ} {C U M H : ℝ}
    (hz : z ≠ 0) (hC : 0 < C) (hM : 0 < M) (hH : 0 < H)
    (hbound : ‖z‖ ≤ C * Real.exp U) :
    Real.log ‖z‖ / (M * H) ≤ U / (M * H) + Real.log C / (M * H) := by
  have h := Real.log_le_log (norm_pos_iff.mpr hz) hbound
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  apply (div_le_div_of_nonneg_right h (mul_pos hM hH).le).trans_eq
  ring

theorem normalized_averaged_log_lower_bound {S M H b Ear : ℝ} {Δplus Δminus : ℂ}
    (hS : 0 < S) (hM : 0 < M) (hH : 0 < H) (hp : Δplus ≠ 0) (hm : Δminus ≠ 0)
    (hN : 1 ≤ S ^ 2 * (‖Δplus‖ * ‖Δminus‖))
    (hcost : Real.log S ≤ M * H * (1 - b + Ear)) :
    -(1 - b) - Ear ≤ ((Real.log ‖Δplus‖ + Real.log ‖Δminus‖) / 2) / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hlower := averaged_log_lower_bound hS hp hm hN
  nlinarith

theorem normalize_analytic_exponent {M H D : ℝ} (hM : 0 < M) (hH : 0 < H) (hD : 0 < D)
    (ν W E rem c η A : ℝ) :
    (ν * W + M * H * E + M * rem +
      max (-c * (η ^ 2 * M ^ 2 / D)) (-ν * ((1 - η) * M * (A * H)))) / (M * H) =
      ν * (W / (M * H)) + E + rem / H +
        max (-c * (η ^ 2 * M / (D * H))) (-ν * (A * (1 - η))) := by
  have hc : (-c * (η ^ 2 * M ^ 2 / D)) / (M * H) = -c * (η ^ 2 * M / (D * H)) := by
    field_simp
  have hh : (-ν * ((1 - η) * M * (A * H))) / (M * H) = -ν * (A * (1 - η)) := by
    field_simp
  rw [add_div, add_div, add_div, ← max_div_div_right (mul_pos hM hH).le, hc, hh]
  have h₁ : M * H * E / (M * H) = E := by field_simp
  have h₂ : M * rem / (M * H) = rem / H := by field_simp
  rw [h₁, h₂]
  ring

theorem normalize_arithmetic_cost {M H w₀ wstar : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (logDen logHeight W θ : ℝ) :
    (M * logDen + logHeight * (M * (H / w₀)) + M * H - W + M * (θ * H / wstar)) / (M * H) =
      1 - W / (M * H) + logDen / H + logHeight / w₀ + θ / wstar := by
  field_simp
  ring

theorem normalized_translated_det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {m : ℕ} (T N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ)
    (ω : ℂ) (l : ι → Fin m → ℕ) (error : ι → Fin m → ℂ)
    (hN : ∀ c i, l c i ≤ N i) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {A F v₀ H w₀ wstar : ℚ} {η ν E R C : ℝ}
    (hA : 0 ≤ A) (hH : 0 < H) (hη : 0 ≤ η)
    (hF : 0 < F) (hv₀ : 0 < v₀) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ w i) (hE : 1 ≤ E) (hν : 0 ≤ ν) (hR : 1 ≤ R)
    (hz : ∀ r, ‖(j r : ℂ) * ω‖ + 1 ≤ R / 2)
    (hh : ∀ c, (h c : ℚ) ≤ H / w₀)
    (hl : ∀ c, (∑ i, w i * (l c i : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ)) (hjet : ∀ r, v₀ * (s r : ℚ) < H)
    (herror : ∀ r i, ‖error r i‖ ≤ E * Real.exp (-ν * (w i : ℝ)))
    (hC : 0 < C) (hsC : ∀ r, (s r : ℝ) + 1 ≤ C * (H : ℝ))
    (hNC : ∀ i, (N i : ℝ) + 1 ≤ C * (H : ℝ))
    (hne : (Matrix.of (fun r c => translatedInterpolationEntry m (h c) (j r) (s r) ω T (l c) (β r) (error r))).det ≠ 0) :
    Real.log ‖(Matrix.of (fun r c => translatedInterpolationEntry m (h c) (j r) (s r) ω T (l c) (β r) (error r))).det‖ /
      (Fintype.card ι * (H : ℝ)) ≤
      ν * ((∑ r, ∑ i, (w i : ℝ) * (β r i : ℝ)) / (Fintype.card ι * (H : ℝ))) +
      translationCost ν E F v₀ wstar + holomorphicCost R w₀ wstar v₀ +
      determinantRemainder (Fintype.card ι) / (H : ℝ) +
      (2 * m + 1) * Real.log (C * (H : ℝ)) / (H : ℝ) +
      max (-(Real.log 2 / 4) * (η ^ 2 * Fintype.card ι /
        ((ImaginaryQuadratic.monomialIndices w (A * H)).card * (H : ℝ))))
        (-ν * ((A : ℝ) * (1 - η))) := by
  have hnorm := norm_translated_det_le_exp T N β s h j ω l error hN w hw hA hH.le hη
    hF hv₀ hw₀ hwstar hmin hE hν hR hz hh hl htrunc hjet herror
  have hM : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hchoices : (0 : ℝ) < Fintype.card (∀ r, RowChoice N (β r) (s r)) := by
    exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < (ImaginaryQuadratic.monomialIndices w (A * H)).card := by
    rw [← card_lowWeightIndices]
    exact_mod_cast card_lowWeightIndices_pos w hw (mul_nonneg hA hH.le)
  have hn := normalized_log_norm_le hne hchoices hM hH' hnorm
  rw [normalize_analytic_exponent hM hH' hD] at hn
  have hc := normalized_log_choice_count_le N β s hH' hC hsC hNC
  dsimp only [translationCost, holomorphicCost, determinantRemainder] at hn ⊢
  linarith

end QuadraticField
