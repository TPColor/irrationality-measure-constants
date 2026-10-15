import QuadraticFieldCriterion.RowChoices
import QuadraticFieldCriterion.AnalyticDeterminant

/-! # Bounds for the actual finite choices in a determinant row -/

namespace QuadraticField

theorem norm_rowChoiceScalar_le {m : ℕ} (T N : Fin m → ℕ) (β : Fin m →₀ ℕ)
    (s : ℕ) (error : Fin m → ℂ) (r : RowChoice N β s)
    (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {F v₀ H wstar : ℚ} {ν E : ℝ}
    (hF : 0 < F) (hv₀ : 0 < v₀) (hwstar : 0 < wstar) (hmin : ∀ i, wstar ≤ w i)
    (hE : 1 ≤ E) (hν : 0 ≤ ν)
    (hdegree : (∑ i, w i * ((r.1 i : ℕ) : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ)) (hjet : v₀ * (s : ℚ) < H)
    (herror : ∀ i, ‖error i‖ ≤ E * Real.exp (-ν * (w i : ℝ))) :
    ‖rowChoiceScalar T N β s error r‖ ≤
      Real.exp (-ν * (∑ i, (w i : ℝ) * (((r.1 i : ℕ) - β i : ℕ) : ℝ)) +
        (H : ℝ) * (ν / (F : ℝ) + Real.log 2 / (v₀ : ℝ) + Real.log (4 * E) / (wstar : ℝ))) := by
  classical
  unfold rowChoiceScalar
  split_ifs with hβ
  · exact translationScalar_bound_of_packet m T (fun i => (r.1 i : ℕ)) β
      (fun i => (r.2.2 i : ℕ)) error w hw hF hv₀ hwstar hmin hE hν hβ
      (fun i => Nat.le_of_lt_succ (r.2.2 i).isLt) hdegree htrunc
      (Nat.le_of_lt_succ r.2.1.isLt) hjet herror
  · simpa only [norm_zero] using (Real.exp_pos _).le

noncomputable def rowChoiceMatrix {ι : Type*} {m : ℕ} (N : Fin m → ℕ)
    (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ) (ω : ℂ) (l : ι → Fin m → ℕ)
    (f : ∀ r, RowChoice N (β r) (s r)) : Matrix ι ι ℂ :=
  fun r c => rowChoiceTest N (β r) (s r) (h c) (j r) ω (l c) (f r)

theorem rowChoiceMatrix_eq_columnLogarithmicMatrix {ι : Type*} {m : ℕ}
    (N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ) (ω : ℂ)
    (l : ι → Fin m → ℕ) (f : ∀ r, RowChoice N (β r) (s r)) :
    rowChoiceMatrix N β s h j ω l f =
      columnLogarithmicMatrix h l (fun r i => ((f r).1 i : ℕ))
        (fun r => (j r : ℂ) * ω) (fun r => s r - ((f r).2.1 : ℕ)) := rfl

theorem rowChoice_weight_budget_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ) (ω : ℂ)
    (l : ι → Fin m → ℕ) (f : ∀ r, RowChoice N (β r) (s r))
    (w : Fin m → ℚ) (hw : ∀ i, 0 ≤ w i) (H : ℚ)
    (hl : ∀ c, (∑ i, w i * (l c i : ℚ)) ≤ H)
    (hne : (rowChoiceMatrix N β s h j ω l f).det ≠ 0) :
    ∀ r, (∑ i, w i * (((f r).1 i : ℕ) : ℚ)) ≤ H := by
  classical
  intro r
  by_contra hr
  apply hne
  apply Matrix.det_eq_zero_of_row_eq_zero r
  intro c
  have ha : ¬ (∀ i, ((f r).1 i : ℕ) ≤ l c i) := by
    intro ha
    apply hr
    exact (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (show (((f r).1 i : ℕ) : ℚ) ≤ l c i by exact_mod_cast ha i) (hw i))).trans (hl c)
  have hz : columnFunction (h c) (l c) (fun i => ((f r).1 i : ℕ)) = fun _ => 0 := by
    funext z
    simp only [columnFunction, ite_eq_right ha]
  change taylorCoefficient _ _ 0 = 0
  rw [hz]
  have hc := (HasTaylorSeries.const (0 : ℂ)).coeff_eq (s r - ((f r).2.1 : ℕ))
  simpa using hc

theorem norm_rowChoiceMatrix_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s h j : ι → ℕ) (ω : ℂ)
    (l : ι → Fin m → ℕ) (f : ∀ r, RowChoice N (β r) (s r))
    (R H w₀ wstar v₀ : ℝ) (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (hz : ∀ r, ‖(j r : ℂ) * ω‖ + 1 ≤ R / 2)
    (hh : ∀ c, (h c : ℝ) ≤ H / w₀)
    (hl : ∀ c, ((∑ i, l c i : ℕ) : ℝ) ≤ H / wstar)
    (hs : ∀ r, (s r : ℝ) ≤ H / v₀) :
    ‖(rowChoiceMatrix N β s h j ω l f).det‖ ≤
      Real.exp (-(Real.log 2 / 4) * collisionMass (fun r i => ((f r).1 i : ℕ)) +
        Fintype.card ι * H * (R / w₀ + Real.log (2 * R) / wstar + Real.log 2 / v₀) +
        Fintype.card ι * (Real.log (Fintype.card ι + 1) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-(Real.log 2 / 2))))) := by
  by_cases hne : (rowChoiceMatrix N β s h j ω l f).det = 0
  · rw [hne, norm_zero]
    exact (Real.exp_pos _).le
  have horders : ((∑ r, (s r - ((f r).2.1 : ℕ)) : ℕ) : ℝ) ≤ Fintype.card ι * H / v₀ := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r, (s r : ℝ) := Finset.sum_le_sum (fun r hr => by exact_mod_cast Nat.sub_le (s r) ((f r).2.1 : ℕ))
      _ ≤ ∑ _r : ι, H / v₀ := Finset.sum_le_sum (fun r hr => hs r)
      _ = _ := by simp [mul_div_assoc]
  rw [rowChoiceMatrix_eq_columnLogarithmicMatrix] at hne ⊢
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr hne)).mp
  exact column_logarithmic_collision_bound h l (fun r i => ((f r).1 i : ℕ))
    (fun r => (j r : ℂ) * ω) (fun r => s r - ((f r).2.1 : ℕ))
    R H w₀ wstar v₀ hR hw₀ hwstar hz hh hl horders hne

theorem prod_norm_rowChoiceScalar_le {ι : Type*} [Fintype ι]
    {m : ℕ} (T N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s : ι → ℕ)
    (error : ι → Fin m → ℂ) (f : ∀ r, RowChoice N (β r) (s r))
    (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {F v₀ H wstar : ℚ} {ν E : ℝ}
    (hF : 0 < F) (hv₀ : 0 < v₀) (hwstar : 0 < wstar) (hmin : ∀ i, wstar ≤ w i)
    (hE : 1 ≤ E) (hν : 0 ≤ ν)
    (hdegree : ∀ r, (∑ i, w i * (((f r).1 i : ℕ) : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ)) (hjet : ∀ r, v₀ * (s r : ℚ) < H)
    (herror : ∀ r i, ‖error r i‖ ≤ E * Real.exp (-ν * (w i : ℝ))) :
    (∏ r, ‖rowChoiceScalar T N (β r) (s r) (error r) (f r)‖) ≤
      Real.exp (-ν * (∑ r, ∑ i, (w i : ℝ) * ((((f r).1 i : ℕ) - β r i : ℕ) : ℝ)) +
        Fintype.card ι * (H : ℝ) *
          (ν / (F : ℝ) + Real.log 2 / (v₀ : ℝ) + Real.log (4 * E) / (wstar : ℝ))) := by
  calc
    _ ≤ ∏ r, Real.exp (-ν * (∑ i, (w i : ℝ) * ((((f r).1 i : ℕ) - β r i : ℕ) : ℝ)) +
        (H : ℝ) * (ν / (F : ℝ) + Real.log 2 / (v₀ : ℝ) + Real.log (4 * E) / (wstar : ℝ))) :=
      Finset.prod_le_prod₀ (fun r hr => norm_nonneg _) (fun r hr =>
        norm_rowChoiceScalar_le T N (β r) (s r) (error r) (f r) w hw
          hF hv₀ hwstar hmin hE hν (hdegree r) htrunc (hjet r) (herror r))
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      ring

end QuadraticField
