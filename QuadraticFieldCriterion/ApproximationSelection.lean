import QuadraticFieldCriterion.ApproximationConclusion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.List.OfFn

/-! # Selecting approximations beyond any weight threshold -/

namespace QuadraticField

/-- Negating the desired bound leaves a fixed exponent and arbitrarily large
bad denominators; no reduced-fraction assumption is introduced. -/
theorem not_eventualStrictBound_iff (x : ℝ) :
    ¬ ImaginaryQuadratic.EventualStrictBound x ↔
      ∃ ν : ℝ, 2 < ν ∧ ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
        Q ≤ q ∧ 0 < q ∧ |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν) := by
  unfold ImaginaryQuadratic.EventualStrictBound
  push Not
  rfl

/-- The logarithmic weights of bad approximations are arbitrarily large.
For a nonzero target their numerators can also be required to be nonzero. -/
theorem exists_bad_approximation_above_weight {x ν : ℝ} (hx : x ≠ 0) (hν : 2 < ν)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ 0 < q ∧ |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) (T : ℝ) :
    ∃ p : ℤ, ∃ q : ℕ, p ≠ 0 ∧ 2 ≤ q ∧
      T < (⌈Real.log (q : ℝ)⌉ : ℤ) ∧
      |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν) := by
  have hxabs : 0 < |x| := abs_pos.mpr hx
  obtain ⟨Q, hQ⟩ := exists_nat_gt (max 2 (max (Real.exp T) (1 / |x|)))
  obtain ⟨p, q, hqQ, hq0, herr⟩ := hbad Q
  have hqQ' : (Q : ℝ) ≤ q := by exact_mod_cast hqQ
  have hq2 : (2 : ℝ) < q := (lt_of_le_of_lt (le_max_left _ _) hQ).trans_le hqQ'
  have hqexp : Real.exp T < (q : ℝ) :=
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hQ).trans_le hqQ'
  have hqinv : 1 / |x| < (q : ℝ) :=
    (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hQ).trans_le hqQ'
  have hp : p ≠ 0 := by
    intro hp
    subst p
    simp only [Int.cast_zero, zero_div, sub_zero] at herr
    have hpow : (q : ℝ) ^ (-ν) ≤ (q : ℝ)⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ q)
        (by linarith : -ν ≤ (-1 : ℝ))
      simpa only [Real.rpow_neg_one] using h
    have hsmall : (q : ℝ)⁻¹ < |x| := by
      rw [← one_div]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < q)).mpr
      have h := (div_lt_iff₀ hxabs).mp hqinv
      nlinarith
    exact (not_lt_of_ge herr) (hpow.trans_lt hsmall)
  refine ⟨p, q, hp, by exact_mod_cast hq2.le, ?_, herr⟩
  have hlog : T < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < q)).mpr hqexp
  exact hlog.trans_le (Int.le_ceil _)

/-- Arbitrarily large choices can meet thresholds depending on all preceding
weights, in exactly the order quantified by the interpolation theorem. -/
theorem exists_successive_choices {α : Type*} (P : α → Prop) (weight : α → ℚ)
    (hchoose : ∀ T : ℚ, ∃ a, P a ∧ T < weight a) (m : ℕ)
    (threshold : Fin m → List ℚ → ℚ) :
    ∃ f : Fin m → α, ∀ i, P (f i) ∧
      threshold i ((List.ofFn (fun j => weight (f j))).take i.val) < weight (f i) := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨f, hf⟩ := ih (fun i => threshold i.castSucc)
    obtain ⟨a, ha, hweight⟩ := hchoose
      (threshold (Fin.last m) (List.ofFn (fun j => weight (f j))))
    refine ⟨Fin.snoc f a, ?_⟩
    have hlist : List.ofFn (fun j => weight ((Fin.snoc f a : Fin (m + 1) → α) j)) =
        List.ofFn (fun j => weight (f j)) ++ [weight a] := by
      rw [List.ofFn_succ_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Fin.val_last, hlist]
      rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
      exact ⟨ha, hweight⟩
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc, hlist]
      rw [List.take_append_of_le_length (by simp)]
      exact hf j

/-- All approximation weights and their interpolation thresholds are fixed
before any degree or centre threshold is used. -/
theorem exists_successive_bad_approximations {x ν : ℝ} (hx : x ≠ 0) (hν : 2 < ν)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ 0 < q ∧ |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν))
    (m : ℕ) (threshold : Fin m → List ℚ → ℚ) (L : ℚ) :
    ∃ pq : Fin m → ℤ × ℕ,
      let w := fun i => ((⌈Real.log (pq i).2⌉ : ℤ) : ℚ)
      (∀ i, (pq i).1 ≠ 0 ∧ 2 ≤ (pq i).2 ∧ L < w i ∧
        |x - ((pq i).1 : ℝ) / (pq i).2| ≤ ((pq i).2 : ℝ) ^ (-ν)) ∧
      ∀ i, threshold i ((List.ofFn w).take i.val) < w i := by
  let P : ℤ × ℕ → Prop := fun pq => pq.1 ≠ 0 ∧ 2 ≤ pq.2 ∧
    L < ((⌈Real.log (pq.2 : ℝ)⌉ : ℤ) : ℚ) ∧
    |x - (pq.1 : ℝ) / (pq.2 : ℝ)| ≤ (pq.2 : ℝ) ^ (-ν)
  let weight : ℤ × ℕ → ℚ := fun pq => (⌈Real.log (pq.2 : ℝ)⌉ : ℤ)
  have hchoose : ∀ T : ℚ, ∃ pq, P pq ∧ T < weight pq := by
    intro T
    obtain ⟨p, q, hp, hq, hw, herr⟩ :=
      exists_bad_approximation_above_weight hx hν hbad ((max L T : ℚ) : ℝ)
    have hw' : max L T < ((⌈Real.log (q : ℝ)⌉ : ℤ) : ℚ) := by exact_mod_cast hw
    exact ⟨(p, q), ⟨hp, hq, (le_max_left _ _).trans_lt hw', herr⟩,
      (le_max_right _ _).trans_lt hw'⟩
  obtain ⟨pq, hpq⟩ := exists_successive_choices P weight hchoose m threshold
  exact ⟨pq, fun i => (hpq i).1, fun i => (hpq i).2⟩

/-- Rounding a denominator logarithm loses only the fixed factor `exp ν`. -/
theorem approximation_error_le_exp_weight {x ν : ℝ} {p : ℤ} {q : ℕ}
    (hq : 0 < q) (hν : 0 ≤ ν)
    (herr : |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    |x - (p : ℝ) / (q : ℝ)| ≤ Real.exp ν *
      Real.exp (-ν * (⌈Real.log (q : ℝ)⌉ : ℤ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hw := Int.ceil_lt_add_one (Real.log (q : ℝ))
  calc
    _ ≤ (q : ℝ) ^ (-ν) := herr
    _ = Real.exp (Real.log q * (-ν)) := Real.rpow_def_of_pos hq' _
    _ ≤ Real.exp (ν + -ν * (⌈Real.log (q : ℝ)⌉ : ℤ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := Real.exp_add _ _

theorem centre_error_le_exp_weight {x ν : ℝ} {p : ℤ} {q j K : ℕ}
    (γ : ℂ) (hq : 0 < q) (hj : j ≤ K) (hν : 0 ≤ ν)
    (herr : |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    ‖(j : ℂ) * γ * (((p : ℝ) / (q : ℝ) - x : ℝ) : ℂ)‖ ≤
      (K : ℝ) * ‖γ‖ * Real.exp ν * Real.exp (-ν * (⌈Real.log (q : ℝ)⌉ : ℤ)) := by
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm]
  have h := approximation_error_le_exp_weight hq hν herr
  calc
    _ ≤ ((K : ℝ) * ‖γ‖) * (Real.exp ν *
        Real.exp (-ν * (⌈Real.log (q : ℝ)⌉ : ℤ))) := mul_le_mul
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (norm_nonneg _)) h
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The row denominator saving survives replacing `log q` by its ceiling;
the loss is bounded by the weighted row budget divided by the least weight. -/
theorem row_log_denominator_lower_bound {ι : Type*} [Fintype ι]
    (q β : ι → ℕ) {H wstar : ℝ} (hwstar : 0 < wstar)
    (hweights : ∀ i, wstar ≤ (⌈Real.log (q i : ℝ)⌉ : ℤ))
    (hbudget : (∑ i, (β i : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ H) :
    (∑ i, (β i : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) - H / wstar ≤
      ∑ i, (β i : ℝ) * Real.log (q i : ℝ) := by
  have hdegree : (∑ i, (β i : ℝ)) ≤ H / wstar := by
    apply (le_div_iff₀ hwstar).mpr
    calc
      _ = ∑ i, (β i : ℝ) * wstar := Finset.sum_mul _ _ _
      _ ≤ ∑ i, (β i : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hweights i) (Nat.cast_nonneg _))
      _ ≤ H := hbudget
  have hlog : (∑ i, (β i : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) -
      (∑ i, (β i : ℝ)) ≤ ∑ i, (β i : ℝ) * Real.log (q i : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hc := Int.ceil_lt_add_one (Real.log (q i : ℝ))
    have hb : (0 : ℝ) ≤ β i := Nat.cast_nonneg _
    nlinarith
  linarith

end QuadraticField
