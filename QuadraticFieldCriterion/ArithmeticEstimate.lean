import QuadraticFieldCriterion.CoefficientClearing
import QuadraticFieldCriterion.ApproximationSelection

/-! # Logarithmic cost of the full interpolation scaling -/

namespace QuadraticField

theorem interpolationRowScale_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 0 < q i)
    (β : Fin (m + 1) →₀ ℕ) : 0 < interpolationRowScale q β :=
  Finset.prod_pos (fun i _ => pow_pos (inv_pos.mpr (by exact_mod_cast hq i)) _)

theorem interpolationColumnScale_pos {m : ℕ} (T q N : Fin m → ℕ)
    (hq : ∀ i, 0 < q i) (s : ℕ) (hs : 0 < s) (ℓ : Fin (m + 1) →₀ ℕ) :
    0 < interpolationColumnScale T q N s ℓ := by
  have hd : 0 < ∏ i, (Nat.lcmUpto (T i) : ℚ) ^ N i :=
    Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast Nat.lcmUpto_pos (T i)) _)
  have hq' : 0 < ∏ i, (q i : ℚ) ^ ℓ i.succ :=
    Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)
  exact mul_pos (mul_pos hd (pow_pos (by exact_mod_cast hs) _)) hq'

theorem log_interpolationRowScale {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 0 < q i)
    (β : Fin (m + 1) →₀ ℕ) :
    Real.log (interpolationRowScale q β : ℝ) =
      -∑ i, (β i.succ : ℝ) * Real.log (q i : ℝ) := by
  have hcast : (interpolationRowScale q β : ℝ) =
      ∏ i, ((q i : ℝ)⁻¹) ^ β i.succ := by simp [interpolationRowScale]
  rw [hcast, Real.log_prod (fun i _ => pow_ne_zero _ (inv_ne_zero (by exact_mod_cast (hq i).ne')))]
  simp only [Real.log_pow, Real.log_inv, mul_neg, Finset.sum_neg_distrib]

theorem log_interpolationColumnScale {m : ℕ} (T q N : Fin m → ℕ)
    (hq : ∀ i, 0 < q i) (s : ℕ) (hs : 0 < s) (ℓ : Fin (m + 1) →₀ ℕ) :
    Real.log (interpolationColumnScale T q N s ℓ : ℝ) =
      Real.log ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) +
        (ℓ 0 : ℝ) * Real.log (s : ℝ) + ∑ i, (ℓ i.succ : ℝ) * Real.log (q i : ℝ) := by
  have hcast : (interpolationColumnScale T q N s ℓ : ℝ) =
      ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) *
        (s : ℝ) ^ ℓ 0 * ∏ i, (q i : ℝ) ^ ℓ i.succ := by
    simp [interpolationColumnScale]
  have hd : (0 : ℝ) < ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp only [Nat.cast_pow]
    exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast Nat.lcmUpto_pos (T i)) _)
  have hq' : (0 : ℝ) < ∏ i, (q i : ℝ) ^ ℓ i.succ :=
    Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [hcast, Real.log_mul (mul_pos hd (pow_pos hs' _)).ne' hq'.ne',
    Real.log_mul hd.ne' (pow_ne_zero _ hs'.ne'), Real.log_pow,
    Real.log_prod (fun i _ => pow_ne_zero _ (by exact_mod_cast (hq i).ne'))]
  simp only [Real.log_pow]

theorem log_interpolation_scaling {m : ℕ} {ι : Type*} [Fintype ι]
    (T q N : Fin m → ℕ) (hq : ∀ i, 0 < q i) (s : ℕ) (hs : 0 < s)
    (row column : ι → (Fin (m + 1) →₀ ℕ)) :
    Real.log |(((∏ i, interpolationRowScale q (row i)) *
        ∏ j, interpolationColumnScale T q N s (column j) : ℚ) : ℝ)| =
      Fintype.card ι * Real.log ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) +
      Real.log (s : ℝ) * (∑ j, (column j 0 : ℝ)) +
      (∑ j, ∑ i, (column j i.succ : ℝ) * Real.log (q i : ℝ)) -
      (∑ j, ∑ i, (row j i.succ : ℝ) * Real.log (q i : ℝ)) := by
  classical
  have hr : (0 : ℝ) < ∏ i, (interpolationRowScale q (row i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast interpolationRowScale_pos q hq (row i))
  have hc : (0 : ℝ) < ∏ j, (interpolationColumnScale T q N s (column j) : ℝ) :=
    Finset.prod_pos (fun j _ => by exact_mod_cast interpolationColumnScale_pos T q N hq s hs (column j))
  simp only [Rat.cast_mul, Rat.cast_prod]
  rw [abs_of_pos (mul_pos hr hc), Real.log_mul hr.ne' hc.ne',
    Real.log_prod (fun i _ => by exact_mod_cast (interpolationRowScale_pos q hq (row i)).ne'),
    Real.log_prod (fun j _ => by exact_mod_cast (interpolationColumnScale_pos T q N hq s hs (column j)).ne')]
  simp_rw [log_interpolationRowScale q hq, log_interpolationColumnScale T q N hq s hs]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
  ring

/-- The arithmetic cost with the row denominator saving retained. -/
theorem log_interpolation_scaling_le {m : ℕ} {ι : Type*} [Fintype ι]
    (T q N : Fin m → ℕ) (hq : ∀ i, 0 < q i) (s : ℕ) (hs : 0 < s)
    (row column : ι → (Fin (m + 1) →₀ ℕ)) {H θ w₀ wstar : ℝ}
    (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ (⌈Real.log (q i : ℝ)⌉ : ℤ))
    (hh : ∀ j, (column j 0 : ℝ) ≤ H / w₀)
    (hcol : ∀ j, (∑ i, (column j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ H)
    (hrow : ∀ j, (∑ i, (row j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ θ * H) :
    Real.log |(((∏ i, interpolationRowScale q (row i)) *
        ∏ j, interpolationColumnScale T q N s (column j) : ℚ) : ℝ)| ≤
      Fintype.card ι * Real.log ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) +
      Real.log (s : ℝ) * (Fintype.card ι * (H / w₀)) + Fintype.card ι * H -
      (∑ j, ∑ i, (row j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) +
      Fintype.card ι * (θ * H / wstar) := by
  classical
  have hlog : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg (by exact_mod_cast hs)
  have hheight : (∑ j, (column j 0 : ℝ)) ≤ Fintype.card ι * (H / w₀) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hh j)
  have hcolumns : (∑ j, ∑ i, (column j i.succ : ℝ) * Real.log (q i : ℝ)) ≤
      Fintype.card ι * H := by
    have hsingle : ∀ j, (∑ i, (column j i.succ : ℝ) * Real.log (q i : ℝ)) ≤ H := by
      intro j
      exact (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (Int.le_ceil _) (Nat.cast_nonneg _))).trans (hcol j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hsingle j)
  have hrows : (∑ j, ∑ i, (row j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) -
      Fintype.card ι * (θ * H / wstar) ≤
      ∑ j, ∑ i, (row j i.succ : ℝ) * Real.log (q i : ℝ) := by
    have hsingle := fun j => row_log_denominator_lower_bound q
      (fun i => row j i.succ) hwstar hmin (hrow j)
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hsingle j)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  rw [log_interpolation_scaling T q N hq s hs row column]
  have := mul_le_mul_of_nonneg_left hheight hlog
  linarith

noncomputable def interpolationArithmeticCost {m : ℕ} {ι : Type*} [Fintype ι]
    (T q N : Fin m → ℕ) (s : ℕ) (row : ι → (Fin (m + 1) →₀ ℕ))
    (H θ w₀ wstar : ℝ) : ℝ :=
  Fintype.card ι * Real.log ((∏ i, (Nat.lcmUpto (T i)) ^ N i : ℕ) : ℝ) +
  Real.log (s : ℝ) * (Fintype.card ι * (H / w₀)) + Fintype.card ι * H -
  (∑ j, ∑ i, (row j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) +
  Fintype.card ι * (θ * H / wstar)

/-- The full averaged arithmetic estimate, obtained from coefficient
integrality and the norm, with no determinant estimate assumed. -/
theorem full_interpolation_arithmetic_estimate {D : ℤ} (hD : ¬ IsSquare D)
    {m K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T q N : Fin m → ℕ) (s : ℕ) (hs : 0 < s)
    (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (hy : ∀ j, (s : Algebra D) * y j ∈ integerOrder D)
    (hq : ∀ i, 0 < q i) (hc : ∀ j i, (q i : Algebra D) * c j i ∈ integerOrder D)
    (centre : ι → Fin K) (row column : ι → (Fin (m + 1) →₀ ℕ))
    (hcolumn : ∀ j i, column j i.succ ≤ N i)
    (hne : (quadraticInterpolationMatrix D T y c centre row column).det ≠ 0)
    {H θ w₀ wstar : ℝ} (hwstar : 0 < wstar)
    (hmin : ∀ i, wstar ≤ (⌈Real.log (q i : ℝ)⌉ : ℤ))
    (hh : ∀ j, (column j 0 : ℝ) ≤ H / w₀)
    (hcol : ∀ j, (∑ i, (column j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ H)
    (hrow : ∀ j, (∑ i, (row j i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ θ * H) :
    -interpolationArithmeticCost T q N s row H θ w₀ wstar ≤
      (Real.log ‖((quadraticInterpolationMatrix D T y c centre row column).map (embedding D)).det‖ +
       Real.log ‖((quadraticInterpolationMatrix D T y c centre row column).map (conjugateEmbedding D)).det‖) / 2 := by
  have hN := interpolation_matrix_norm_lower_bound hD T q N s hs y c hy hq hc
    centre row column hcolumn hne
  let S : ℝ := |(((∏ i, interpolationRowScale q (row i)) *
      ∏ j, interpolationColumnScale T q N s (column j) : ℚ) : ℝ)|
  have hS : 0 < S := by
    apply abs_pos.mpr
    have hp : (0 : ℚ) < (∏ i, interpolationRowScale q (row i)) *
        ∏ j, interpolationColumnScale T q N s (column j) :=
      mul_pos (Finset.prod_pos (fun i _ => interpolationRowScale_pos q hq (row i)))
        (Finset.prod_pos (fun j _ => interpolationColumnScale_pos T q N hq s hs (column j)))
    exact_mod_cast hp.ne'
  have hp : ((quadraticInterpolationMatrix D T y c centre row column).map (embedding D)).det ≠ 0 := by
    intro h
    simp [h] at hN
    norm_num at hN
  have hm : ((quadraticInterpolationMatrix D T y c centre row column).map (conjugateEmbedding D)).det ≠ 0 := by
    intro h
    simp [h] at hN
    norm_num at hN
  have hlower := averaged_log_lower_bound hS hp hm hN
  have hcost := log_interpolation_scaling_le T q N hq s hs row column hwstar hmin hh hcol hrow
  change Real.log S ≤ interpolationArithmeticCost T q N s row H θ w₀ wstar at hcost
  linarith

end QuadraticField
