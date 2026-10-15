import QuadraticFieldCriterion.EntireColumns
import QuadraticFieldCriterion.LogTruncation
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Exact finite identities for translating interpolation rows -/

namespace QuadraticField

/-- Expanding the transverse variables gives exactly the entire columns
used in the analytic determinant estimate. -/
theorem entire_column_binomial_identity {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h : ℕ) (l : σ → ℕ) (z : ℂ) (u : σ → ℂ) :
    Complex.exp ((h : ℂ) * z) * ∏ i, (z + u i) ^ l i =
      ∑ a : ∀ i, Fin (l i + 1), columnFunction h l (fun i => (a i : ℕ)) z *
        ∏ i, u i ^ (a i : ℕ) := by
  classical
  have hbinom : (∏ i, (z + u i) ^ l i) =
      ∏ i, ∑ a : Fin (l i + 1), u i ^ (a : ℕ) * z ^ (l i - (a : ℕ)) *
        ((l i).choose (a : ℕ) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [add_comm z, add_pow]
    exact (Fin.sum_univ_eq_sum_range (fun a => u i ^ a * z ^ (l i - a) *
      ((l i).choose a : ℂ)) (l i + 1)).symm
  rw [hbinom, Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : ∀ i, (a i : ℕ) ≤ l i := fun i => Nat.le_of_lt_succ (a i).isLt
  rw [columnFunction, ite_eq_left hle]
  simp only [entireMonomial, Nat.cast_prod, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

/-- The exponential coordinate in the translated row is the original
multiplicative centre times `1+t`. -/
theorem exponential_log_curve (ω : ℂ) (j : ℕ) {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    Complex.exp ((j : ℂ) * ω + Complex.log (1 + t)) =
      (Complex.exp ω) ^ j * (1 + t) := by
  have hne : 1 + t ≠ 0 := by
    intro h
    have heq : t = -1 := by linear_combination h
    rw [heq, norm_neg, norm_one] at ht
    norm_num at ht
  rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_log hne]

/-- The additive coordinates are translated by the approximation error and
the logarithm tail; the same identity holds at either signed centre. -/
theorem additive_translation_identity (z logt G u error : ℂ) :
    z + error + G + u = z + logt + (u + error + (G - logt)) := by ring

/-- The exact monomial translation before extracting `t` and `u`
coefficients. The approximation errors and truncation tails occur only in
the factors multiplying the entire columns. -/
theorem translated_monomial_identity {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h j : ℕ) (l : σ → ℕ) (ω : ℂ) (G u error : σ → ℂ)
    {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    (Complex.exp ω) ^ (j * h) * (1 + t) ^ h *
      (∏ i, ((j : ℂ) * ω + error i + G i + u i) ^ l i) =
      ∑ a : ∀ i, Fin (l i + 1),
        columnFunction h l (fun i => (a i : ℕ)) ((j : ℂ) * ω + Complex.log (1 + t)) *
          ∏ i, (u i + error i + (G i - Complex.log (1 + t))) ^ (a i : ℕ) := by
  calc
    _ = Complex.exp ((h : ℂ) * ((j : ℂ) * ω + Complex.log (1 + t))) *
        ∏ i, ((j : ℂ) * ω + Complex.log (1 + t) +
          (u i + error i + (G i - Complex.log (1 + t)))) ^ l i := by
      rw [Complex.exp_nat_mul, exponential_log_curve ω j ht, mul_pow, ← pow_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      ring
    _ = _ := entire_column_binomial_identity h l _ _

noncomputable def logarithmTail (T : ℕ) (t : ℂ) : ℂ :=
  Complex.logTaylor T t - Complex.log (1 + t)

theorem norm_logarithmTail_le_one {T : ℕ} (hT : 0 < T) {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    ‖logarithmTail T t‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
  rw [logarithmTail, norm_sub_rev]
  have h := Complex.norm_log_sub_logTaylor_le n (by linarith : ‖t‖ < 1)
  have hpow : ‖t‖ ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (n := n) (norm_nonneg t) (by linarith))
      (norm_nonneg t)).trans (by simpa using ht)
  apply h.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 1 - ‖t‖)).mpr
  have hn : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  nlinarith

theorem differentiableOn_logarithmTail (T : ℕ) :
    DifferentiableOn ℂ (logarithmTail T) (Metric.closedBall 0 (1 / 2)) := by
  have hp : Differentiable ℂ (Complex.logTaylor T) := by
    unfold Complex.logTaylor
    fun_prop
  intro t ht
  have ht' : ‖t‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using ht
  exact ((hp t).sub ((Complex.differentiableAt_log
    (one_add_mem_slitPlane_of_norm_le_half ht')).comp t
      (differentiableAt_const (1 : ℂ) |>.add differentiableAt_id))).differentiableWithinAt

/-- Cauchy's coefficient bound for every product of the truncation tails. -/
theorem norm_tail_product_taylorCoefficient_le {σ : Type*} [Fintype σ]
    (T e : σ → ℕ) (hT : ∀ i, 0 < T i) (k : ℕ) :
    ‖taylorCoefficient (fun t => ∏ i, logarithmTail (T i) t ^ e i) k 0‖ ≤ (2 : ℝ) ^ k := by
  have hf : DifferentiableOn ℂ (fun t => ∏ i, logarithmTail (T i) t ^ e i)
      (Metric.closedBall 0 (1 / 2)) :=
    DifferentiableOn.fun_finsetProd (fun i _ => (differentiableOn_logarithmTail (T i)).pow (e i))
  have hbound : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      ‖∏ i, logarithmTail (T i) t ^ e i‖ ≤ 1 := by
    intro t ht
    have ht' : ‖t‖ ≤ 1 / 2 := by
      have heq : ‖t‖ = 1 / 2 := by simpa [Metric.mem_sphere, dist_zero_right] using ht
      exact heq.le
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : σ, (1 : ℝ) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_logarithmTail_le_one (hT i) ht'))
      _ = 1 := by simp
  have h := norm_taylorCoefficient_le (by norm_num : (0 : ℝ) < 1 / 2)
    (hf.mono Metric.closure_ball_subset_closedBall |>.diffContOnCl) hbound k
  convert h using 1
  simp only [div_pow, one_pow]
  field_simp

/-- Normalized derivatives obey the coefficient convolution law. -/
theorem taylorCoefficient_mul {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoefficient (fun t => f t * g t) n 0 =
      ∑ i ∈ Finset.range (n + 1), taylorCoefficient f i 0 * taylorCoefficient g (n - i) 0 := by
  rw [taylorCoefficient, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hni : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  unfold taylorCoefficient
  field_simp [hn, hi, hni]
  linear_combination iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 * hfac

theorem taylorCoefficient_log_one_add (k : ℕ) :
    taylorCoefficient (fun t : ℂ => Complex.log (1 + t)) k 0 =
      (-1 : ℂ) ^ (k + 1) / (k : ℂ) := by
  have hknown := hasFPowerSeriesAt_clog_one_add
  have hcanonical := hknown.analyticAt.hasFPowerSeriesAt
  have heq := hcanonical.eq_formalMultilinearSeries hknown
  have h := congrArg (fun p => p.coeff k) heq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at h
  change taylorCoefficient _ k 0 = -(-1 : ℂ) ^ k / (k : ℂ) at h
  rw [h, pow_succ]
  ring

theorem taylorCoefficient_monomial (c : ℂ) (j k : ℕ) :
    taylorCoefficient (fun t : ℂ => c * t ^ j) k 0 = if k = j then c else 0 := by
  simp only [taylorCoefficient, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases hk : k = j
  · subst k
    simp only [ite_true]
    have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
  · simp [hk]

theorem taylorCoefficient_logTaylor (T k : ℕ) :
    taylorCoefficient (Complex.logTaylor T) k 0 =
      if k < T then (-1 : ℂ) ^ (k + 1) / (k : ℂ) else 0 := by
  classical
  have heq : Complex.logTaylor T = fun t : ℂ =>
      ∑ j ∈ Finset.range T, ((-1 : ℂ) ^ (j + 1) / (j : ℂ)) * t ^ j := by
    funext t
    unfold Complex.logTaylor
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, taylorCoefficient, iteratedDeriv_fun_sum (fun j _ => by fun_prop), Finset.sum_div]
  change (∑ j ∈ Finset.range T,
    taylorCoefficient (fun t : ℂ => ((-1 : ℂ) ^ (j + 1) / (j : ℂ)) * t ^ j) k 0) = _
  simp only [taylorCoefficient_monomial]
  simp [Finset.mem_range]

/-- The analytic tail coefficients are precisely the formal coefficients
used by the filtered interpolation construction. -/
theorem taylorCoefficient_logarithmTail (m T k : ℕ) :
    taylorCoefficient (logarithmTail T) k 0 =
      MvPowerSeries.coeff (Finsupp.single 0 k)
        (ImaginaryQuadratic.truncatedLog m T - LiuJiangZhang.logOneAdd m) := by
  have hp : AnalyticAt ℂ (Complex.logTaylor T) 0 := by
    apply Differentiable.analyticAt
    unfold Complex.logTaylor
    fun_prop
  have hl := hasFPowerSeriesAt_clog_one_add.analyticAt
  change iteratedDeriv k (fun t => Complex.logTaylor T t - Complex.log (1 + t)) 0 /
    (k.factorial : ℂ) = _
  rw [iteratedDeriv_fun_sub hp.contDiffAt hl.contDiffAt, sub_div]
  change taylorCoefficient (Complex.logTaylor T) k 0 -
    taylorCoefficient (fun t : ℂ => Complex.log (1 + t)) k 0 = _
  rw [taylorCoefficient_logTaylor, taylorCoefficient_log_one_add]
  rw [map_sub]
  simp [ImaginaryQuadratic.truncatedLog, LiuJiangZhang.logOneAdd, MvPowerSeries.coeff_apply]

end QuadraticField
