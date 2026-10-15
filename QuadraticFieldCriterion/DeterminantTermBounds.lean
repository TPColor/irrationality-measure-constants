import QuadraticFieldCriterion.RowChoiceBounds
import QuadraticFieldCriterion.CollisionAlternatives

/-! # The combined scalar and holomorphic bound for every determinant term -/

namespace QuadraticField

noncomputable def translationCost (ν E F v₀ wstar : ℝ) : ℝ :=
  ν / F + Real.log 2 / v₀ + Real.log (4 * E) / wstar

noncomputable def holomorphicCost (R w₀ wstar v₀ : ℝ) : ℝ :=
  R / w₀ + Real.log (2 * R) / wstar + Real.log 2 / v₀

noncomputable def determinantRemainder (M : ℕ) : ℝ :=
  Real.log (M + 1) + Real.log 2 / 4 - Real.log (1 - Real.exp (-(Real.log 2 / 2)))

theorem norm_rowChoice_term_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (T N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ)
    (ω : ℂ) (l : ι → Fin m → ℕ) (error : ι → Fin m → ℂ)
    (f : ∀ r, RowChoice N (β r) (s r)) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {F v₀ H w₀ wstar : ℚ} {ν E R : ℝ}
    (hF : 0 < F) (hv₀ : 0 < v₀) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ w i) (hE : 1 ≤ E) (hν : 0 ≤ ν) (hR : 1 ≤ R)
    (hz : ∀ r, ‖(j r : ℂ) * ω‖ + 1 ≤ R / 2)
    (hh : ∀ c, (h c : ℚ) ≤ H / w₀)
    (hl : ∀ c, (∑ i, w i * (l c i : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ)) (hjet : ∀ r, v₀ * (s r : ℚ) < H)
    (herror : ∀ r i, ‖error r i‖ ≤ E * Real.exp (-ν * (w i : ℝ))) :
    (∏ r, ‖rowChoiceScalar T N (β r) (s r) (error r) (f r)‖) *
        ‖(rowChoiceMatrix N β s h j ω l f).det‖ ≤
      Real.exp (-ν * (∑ r, ∑ i, (w i : ℝ) * (((f r).1 i : ℕ) : ℝ)) +
        ν * (∑ r, ∑ i, (w i : ℝ) * (β r i : ℝ)) -
        (Real.log 2 / 4) * collisionMass (fun r i => ((f r).1 i : ℕ)) +
        Fintype.card ι * (H : ℝ) * (translationCost ν E F v₀ wstar + holomorphicCost R w₀ wstar v₀) +
        Fintype.card ι * determinantRemainder (Fintype.card ι)) := by
  classical
  by_cases hdet : (rowChoiceMatrix N β s h j ω l f).det = 0
  · rw [hdet, norm_zero, mul_zero]
    exact (Real.exp_pos _).le
  by_cases hprod : (∏ r, ‖rowChoiceScalar T N (β r) (s r) (error r) (f r)‖) = 0
  · rw [hprod, zero_mul]
    exact (Real.exp_pos _).le
  have hβ : ∀ r i, β r i ≤ ((f r).1 i : ℕ) := by
    intro r
    by_contra hr
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp only [rowChoiceScalar, ite_eq_right hr, norm_zero]
  have hdegree := rowChoice_weight_budget_of_det_ne_zero N β s h j ω l f w
    (fun i => (hw i).le) H hl hdet
  have hscalar := prod_norm_rowChoiceScalar_le T N β s error f w hw hF hv₀ hwstar hmin
    hE hν hdegree htrunc hjet herror
  have hmatrix := norm_rowChoiceMatrix_le_exp N β s h j ω l f R H w₀ wstar v₀ hR
    (by exact_mod_cast hw₀) (by exact_mod_cast hwstar) hz
    (fun c => by exact_mod_cast hh c)
    (fun c => by exact_mod_cast ImaginaryQuadratic.transverse_degree_le_of_min_weight w hwstar hmin (l c) (hl c))
    (fun r => by
      have hs : (s r : ℚ) ≤ H / v₀ := (lt_div_iff₀ hv₀).mpr (by nlinarith [hjet r]) |>.le
      exact_mod_cast hs)
  have hdiff : (∑ r, ∑ i, (w i : ℝ) * ((((f r).1 i : ℕ) - β r i : ℕ) : ℝ)) =
      (∑ r, ∑ i, (w i : ℝ) * (((f r).1 i : ℕ) : ℝ)) -
        ∑ r, ∑ i, (w i : ℝ) * (β r i : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_sub (hβ r i)]
    ring
  have hbound := mul_le_mul hscalar hmatrix (norm_nonneg _) (Real.exp_pos _).le
  rw [← Real.exp_add, hdiff] at hbound
  convert hbound using 1
  unfold translationCost holomorphicCost determinantRemainder
  ring_nf

end QuadraticField
