import QuadraticFieldCriterion.DeterminantTermBounds
import QuadraticFieldCriterion.LowWeightCounts

/-! # The full analytic estimate for the truncated interpolation determinant -/

namespace QuadraticField

theorem norm_translated_det_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (T N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ)
    (ω : ℂ) (l : ι → Fin m → ℕ) (error : ι → Fin m → ℂ)
    (hN : ∀ c i, l c i ≤ N i) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {A F v₀ H w₀ wstar : ℚ} {η ν E R : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hF : 0 < F) (hv₀ : 0 < v₀) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ w i) (hE : 1 ≤ E) (hν : 0 ≤ ν) (hR : 1 ≤ R)
    (hz : ∀ r, ‖(j r : ℂ) * ω‖ + 1 ≤ R / 2)
    (hh : ∀ c, (h c : ℚ) ≤ H / w₀)
    (hl : ∀ c, (∑ i, w i * (l c i : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ)) (hjet : ∀ r, v₀ * (s r : ℚ) < H)
    (herror : ∀ r i, ‖error r i‖ ≤ E * Real.exp (-ν * (w i : ℝ))) :
    ‖(Matrix.of (fun r c => translatedInterpolationEntry m (h c) (j r) (s r) ω T (l c) (β r) (error r))).det‖ ≤
      (Fintype.card (∀ r, RowChoice N (β r) (s r)) : ℝ) *
        Real.exp (ν * (∑ r, ∑ i, (w i : ℝ) * (β r i : ℝ)) +
          Fintype.card ι * (H : ℝ) * (translationCost ν E F v₀ wstar + holomorphicCost R w₀ wstar v₀) +
          Fintype.card ι * determinantRemainder (Fintype.card ι) +
          max (-(Real.log 2 / 4) * (η ^ 2 * (Fintype.card ι : ℝ) ^ 2 /
            (ImaginaryQuadratic.monomialIndices w (A * H)).card))
            (-ν * ((1 - η) * Fintype.card ι * ((A : ℝ) * (H : ℝ))))) := by
  classical
  apply (norm_translated_interpolation_det_le m ω T N h j s l hN β error).trans
  calc
    _ ≤ ∑ _f : ∀ r, RowChoice N (β r) (s r),
        Real.exp (ν * (∑ r, ∑ i, (w i : ℝ) * (β r i : ℝ)) +
          Fintype.card ι * (H : ℝ) * (translationCost ν E F v₀ wstar + holomorphicCost R w₀ wstar v₀) +
          Fintype.card ι * determinantRemainder (Fintype.card ι) +
          max (-(Real.log 2 / 4) * (η ^ 2 * (Fintype.card ι : ℝ) ^ 2 /
            (ImaginaryQuadratic.monomialIndices w (A * H)).card))
            (-ν * ((1 - η) * Fintype.card ι * ((A : ℝ) * (H : ℝ))))) := by
      apply Finset.sum_le_sum
      intro f hf
      have ht := norm_rowChoice_term_le_exp T N β s h j ω l error f w hw
        hF hv₀ hw₀ hwstar hmin hE hν hR hz hh hl htrunc hjet herror
      have hgain := weighted_collision_exponent_bound (fun r i => ((f r).1 i : ℕ)) w hw
        hA hH hη hν (show 0 ≤ Real.log 2 / 4 by positivity)
      apply ht.trans
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by simp

end QuadraticField
