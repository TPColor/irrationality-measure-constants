import QuadraticFieldCriterion.TaylorSeriesBridge
import QuadraticFieldCriterion.InterpolationBudgets

/-! # Scalar bounds in the exact row expansion -/

namespace QuadraticField

noncomputable def translationScalar (m : ℕ) (T a β e : Fin m → ℕ)
    (error : Fin m → ℂ) (k : ℕ) : ℂ :=
  (∏ i, ((a i).choose (β i) : ℂ) * ((a i - β i).choose (e i) : ℂ) *
    error i ^ (a i - β i - e i)) *
  MvPowerSeries.coeff (Finsupp.single 0 k)
    (∏ i, (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i)

theorem norm_translation_factor_le (a β e : ℕ) (error : ℂ) (ν w E : ℝ)
    (hE : 1 ≤ E) (herror : ‖error‖ ≤ E * Real.exp (-ν * w)) :
    ‖(a.choose β : ℂ) * ((a - β).choose e : ℂ) * error ^ (a - β - e)‖ ≤
      (4 * E) ^ a * Real.exp (-ν * w * (a - β - e : ℕ)) := by
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have hc₁ : (a.choose β : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast Nat.choose_le_two_pow a β
  have hc₂ : ((a - β).choose e : ℝ) ≤ (2 : ℝ) ^ a := by
    have h : ((a - β).choose e : ℝ) ≤ (2 : ℝ) ^ (a - β) := by
      exact_mod_cast Nat.choose_le_two_pow (a - β) e
    exact h.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  have hc : (a.choose β : ℝ) * ((a - β).choose e : ℝ) ≤ (4 : ℝ) ^ a := by
    calc
      _ ≤ (2 : ℝ) ^ a * 2 ^ a := mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hp : ‖error‖ ^ (a - β - e) ≤ E ^ a * Real.exp (-ν * w * (a - β - e : ℕ)) := by
    calc
      _ ≤ (E * Real.exp (-ν * w)) ^ (a - β - e) := pow_le_pow_left₀ (norm_nonneg _) herror _
      _ = E ^ (a - β - e) * Real.exp (-ν * w * (a - β - e : ℕ)) := by
        rw [mul_pow, mul_comm (-ν * w), Real.exp_nat_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hE ((Nat.sub_le (a - β) e).trans (Nat.sub_le a β))) (Real.exp_pos _).le
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ 4 ^ a * (E ^ a * Real.exp (-ν * w * (a - β - e : ℕ))) :=
      mul_le_mul hc hp (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem norm_translationScalar_le (m : ℕ) (T a β e : Fin m → ℕ)
    (error : Fin m → ℂ) (k : ℕ) (ν E : ℝ) (w : Fin m → ℝ)
    (hT : ∀ i, 0 < T i) (hE : 1 ≤ E)
    (herror : ∀ i, ‖error i‖ ≤ E * Real.exp (-ν * w i)) :
    ‖translationScalar m T a β e error k‖ ≤
      (4 * E) ^ (∑ i, a i) *
        Real.exp (-ν * ∑ i, w i * ((a i - β i - e i : ℕ) : ℝ)) * (2 : ℝ) ^ k := by
  rw [translationScalar, norm_mul, norm_prod]
  calc
    _ ≤ (∏ i, (4 * E) ^ a i * Real.exp (-ν * w i * (a i - β i - e i : ℕ))) * 2 ^ k :=
      mul_le_mul (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
        norm_translation_factor_le (a i) (β i) (e i) (error i) ν (w i) E hE (herror i)))
        (norm_formal_tail_product_coefficient_le m T e hT k) (norm_nonneg _)
        (Finset.prod_nonneg (fun i _ => mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The coefficient bound (4.1), with the fixed centre factor represented
by `E`. The nonzero-tail weight loss is supplied by `TailBudget`. -/
theorem translationScalar_exponential_bound (m : ℕ) (T a β e : Fin m → ℕ)
    (error : Fin m → ℂ) (k : ℕ) (w : Fin m → ℝ) {ν E H F v₀ wstar : ℝ}
    (hT : ∀ i, 0 < T i) (hE : 1 ≤ E) (hν : 0 ≤ ν)
    (_hF : 0 < F) (_hv₀ : 0 < v₀) (_hwstar : 0 < wstar)
    (_hβ : ∀ i, β i ≤ a i) (he : ∀ i, e i ≤ a i - β i)
    (hdegree : ((∑ i, a i : ℕ) : ℝ) ≤ H / wstar)
    (horder : (k : ℝ) ≤ H / v₀)
    (hloss : (∑ i, w i * (e i : ℝ)) ≤ H / F)
    (herror : ∀ i, ‖error i‖ ≤ E * Real.exp (-ν * w i)) :
    ‖translationScalar m T a β e error k‖ ≤
      Real.exp (-ν * (∑ i, w i * ((a i - β i : ℕ) : ℝ)) +
        H * (ν / F + Real.log 2 / v₀ + Real.log (4 * E) / wstar)) := by
  have hEpos : 0 < 4 * E := by linarith
  have hlogE : 0 ≤ Real.log (4 * E) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := norm_translationScalar_le m T a β e error k ν E w hT hE herror
  have hdiff : (∑ i, w i * ((a i - β i - e i : ℕ) : ℝ)) =
      (∑ i, w i * ((a i - β i : ℕ) : ℝ)) - ∑ i, w i * (e i : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_sub (he i)]
    ring
  have hp₁ : (4 * E) ^ (∑ i, a i) = Real.exp (((∑ i, a i : ℕ) : ℝ) * Real.log (4 * E)) := by
    rw [Real.exp_nat_mul, Real.exp_log hEpos]
  have hp₂ : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hp₁, hp₂, ← Real.exp_add, ← Real.exp_add, hdiff] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hdegree hlogE
  have h₂ := mul_le_mul_of_nonneg_right horder hlog2
  have h₃ := mul_le_mul_of_nonneg_left hloss hν
  simp only [div_eq_mul_inv] at h₁ h₂ h₃ ⊢
  nlinarith

/-- For a retained row, the scalar estimate follows directly from the
truncation orders and the weighted source budget. Zero tail coefficients
are handled without requiring a weight-loss bound for them. -/
theorem translationScalar_bound_of_packet (m : ℕ) (T a β e : Fin m → ℕ)
    (error : Fin m → ℂ) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {F v₀ H wstar : ℚ} {ν E : ℝ} {k s : ℕ}
    (hF : 0 < F) (hv₀ : 0 < v₀) (hwstar : 0 < wstar) (hmin : ∀ i, wstar ≤ w i)
    (hE : 1 ≤ E) (hν : 0 ≤ ν) (hβ : ∀ i, β i ≤ a i) (he : ∀ i, e i ≤ a i - β i)
    (hdegree : (∑ i, w i * (a i : ℚ)) ≤ H)
    (htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ))
    (hks : k ≤ s) (hjet : v₀ * (s : ℚ) < H)
    (herror : ∀ i, ‖error i‖ ≤ E * Real.exp (-ν * (w i : ℝ))) :
    ‖translationScalar m T a β e error k‖ ≤
      Real.exp (-ν * (∑ i, (w i : ℝ) * ((a i - β i : ℕ) : ℝ)) +
        (H : ℝ) * (ν / (F : ℝ) + Real.log 2 / (v₀ : ℝ) + Real.log (4 * E) / (wstar : ℝ))) := by
  classical
  let tail := MvPowerSeries.coeff (Finsupp.single 0 k)
    (∏ i, (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i)
  by_cases htail : tail = 0
  · simp only [translationScalar, show MvPowerSeries.coeff (Finsupp.single 0 k)
      (∏ i, (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i) = 0 from htail,
      mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  have hT : ∀ i, 0 < T i := by
    intro i
    by_contra h
    have ht : T i = 0 := Nat.eq_zero_of_not_pos h
    have h := htrunc i
    rw [ht, Nat.cast_zero, mul_zero] at h
    exact (not_le_of_gt (mul_pos hF (hw i))) h
  have hmass := ImaginaryQuadratic.transverse_degree_le_of_min_weight w hwstar hmin a hdegree
  have horder : (k : ℚ) ≤ H / v₀ := by
    apply (le_div_iff₀ hv₀).mpr
    have h := mul_le_mul_of_nonneg_left (show (k : ℚ) ≤ s by exact_mod_cast hks) hv₀.le
    nlinarith
  let v : Fin (m + 1) → ℚ := Fin.cases v₀ (fun _ => 0)
  have hv : ∀ i, 0 ≤ v i := fun i => Fin.cases hv₀.le (fun _ => le_rfl) i
  have hloss := ImaginaryQuadratic.tail_coefficient_weight_budget v hv w T e hF
    (fun i => by simpa only [v, Fin.cases_zero] using htrunc i) hks
    (by simpa only [v, Fin.cases_zero] using hjet) htail
  apply translationScalar_exponential_bound m T a β e error k (fun i => (w i : ℝ))
    hT hE hν (by exact_mod_cast hF) (by exact_mod_cast hv₀) (by exact_mod_cast hwstar) hβ he
  · exact_mod_cast hmass
  · exact_mod_cast horder
  · have h := hloss.le
    simpa only [mul_comm] using (show (∑ i, (e i : ℝ) * (w i : ℝ)) ≤ (H : ℝ) / (F : ℝ) by exact_mod_cast h)
  · exact herror

end QuadraticField
