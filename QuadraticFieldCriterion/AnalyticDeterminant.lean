import QuadraticFieldCriterion.TaylorComposition

/-! # Collision bound for logarithmic derivatives of entire functions -/

namespace QuadraticField

/-- The repeated-index determinant estimate for actual analytic coefficient
tests, rather than an assumed Taylor-series representation of the entries. -/
theorem logarithmic_collision_estimate {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ)
    (f : κ → ι → ℂ → ℂ) (z : ι → ℂ) (ℓ : ι → ℕ) (R B : ℝ)
    (hR : 0 < R) (hB : 0 ≤ B) (hz : ∀ i, ‖z i‖ + 1 ≤ R / 2)
    (hf : ∀ k j, Differentiable ℂ (f k j))
    (hbound : ∀ k j w, w ∈ Metric.sphere (0 : ℂ) R → ‖f k j w‖ ≤ B) :
    ‖(Matrix.of (fun i j => taylorCoefficient
      (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0)).det‖ ≤
      ((Fintype.card ι).factorial * B ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ i, ℓ i) *
        Real.exp (-(Real.log 2 / 4) * (collisionMass a - Fintype.card ι))) *
        ((1 - Real.exp (-(Real.log 2 / 2)))⁻¹) ^ Fintype.card ι := by
  let coeff : κ → ℕ → ι → ℂ :=
    fun k n j => taylorCoefficient (f k j) n 0 * (R : ℂ) ^ n
  let test : ι → ℕ → ℂ := fun i n => logarithmicTest (z i) R (ℓ i) n
  have h := collision_estimate a coeff test B (Real.log 2) (fun i => (2 : ℝ) ^ ℓ i)
    hB (Real.log_pos (by norm_num)) (fun i => by positivity)
    (fun k n j => norm_scaled_taylorCoefficient_le hR (hf k j) (hbound k j) n)
    (fun i n => norm_logarithmicTest_le_exp hR (hz i) (ℓ i) n)
  have heq : (Matrix.of (fun i j => ∑' n, test i n * coeff (a i) n j)) =
      Matrix.of (fun i j => taylorCoefficient
        (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0) := by
    ext i j
    exact logarithmic_taylor_identity (hf (a i) j) hR (hz i) (hbound (a i) j) (ℓ i)
  rw [heq, Finset.prod_pow_eq_pow_sum] at h
  exact h

/-- The exact logarithmic version of the analytic estimate. The factorial
and geometric-series costs are explicit, ready for the degree limit. -/
theorem logarithmic_collision_log_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ)
    (f : κ → ι → ℂ → ℂ) (z : ι → ℂ) (ℓ : ι → ℕ) (R growth : ℝ)
    (hR : 0 < R) (hz : ∀ i, ‖z i‖ + 1 ≤ R / 2)
    (hf : ∀ k j, Differentiable ℂ (f k j))
    (hbound : ∀ k j w, w ∈ Metric.sphere (0 : ℂ) R → ‖f k j w‖ ≤ Real.exp growth)
    (hne : (Matrix.of (fun i j => taylorCoefficient
      (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0)).det ≠ 0) :
    Real.log ‖(Matrix.of (fun i j => taylorCoefficient
      (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0)).det‖ ≤
      Real.log ((Fintype.card ι).factorial : ℝ) + Fintype.card ι * growth +
        (∑ i, ℓ i : ℕ) * Real.log 2 -
        (Real.log 2 / 4) * (collisionMass a - Fintype.card ι) -
        Fintype.card ι * Real.log (1 - Real.exp (-(Real.log 2 / 2))) := by
  have h := logarithmic_collision_estimate a f z ℓ R (Real.exp growth)
    hR (Real.exp_pos _).le hz hf hbound
  have hq : 0 < 1 - Real.exp (-(Real.log 2 / 2)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hlog := Real.log_le_log (norm_pos_iff.mpr hne) h
  simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_exp,
    Real.log_inv] at hlog
  linarith

theorem log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n + 1) := by
  have hpow : (n.factorial : ℝ) ≤ (n + 1 : ℝ) ^ n := by
    have h := (Nat.factorial_le_pow n).trans
      (Nat.pow_le_pow_left (Nat.le_succ n) n)
    exact_mod_cast h
  have h := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) hpow
  rwa [Real.log_pow] at h

/-- The collision saving separated from the holomorphic cost and the
factorial/geometric remainder, in the form used in the degree limit. -/
theorem logarithmic_collision_degree_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ)
    (f : κ → ι → ℂ → ℂ) (z : ι → ℂ) (ℓ : ι → ℕ) (R H growth v₀ : ℝ)
    (hR : 0 < R) (hz : ∀ i, ‖z i‖ + 1 ≤ R / 2)
    (hf : ∀ k j, Differentiable ℂ (f k j))
    (hbound : ∀ k j w, w ∈ Metric.sphere (0 : ℂ) R → ‖f k j w‖ ≤ Real.exp (H * growth))
    (horders : ((∑ i, ℓ i : ℕ) : ℝ) ≤ Fintype.card ι * H / v₀)
    (hne : (Matrix.of (fun i j => taylorCoefficient
      (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0)).det ≠ 0) :
    Real.log ‖(Matrix.of (fun i j => taylorCoefficient
      (fun t => f (a i) j (z i + Complex.log (1 + t))) (ℓ i) 0)).det‖ ≤
      -(Real.log 2 / 4) * collisionMass a +
        Fintype.card ι * H * (growth + Real.log 2 / v₀) +
        Fintype.card ι * (Real.log (Fintype.card ι + 1) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-(Real.log 2 / 2)))) := by
  have h := logarithmic_collision_log_bound a f z ℓ R (H * growth) hR hz hf hbound hne
  have hfactorial := log_factorial_le (Fintype.card ι)
  have horder := mul_le_mul_of_nonneg_right horders
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have heq : (Fintype.card ι : ℝ) * H / v₀ * Real.log 2 =
      Fintype.card ι * H * (Real.log 2 / v₀) := by ring
  rw [heq] at horder
  nlinarith

/-- The centres in either embedding fit inside the disk used for the tests. -/
theorem centre_radius_bound (ω : ℂ) {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ) * ω‖ + 1 ≤ (4 * K * (1 + ‖ω‖)) / 2 := by
  rw [norm_mul, Complex.norm_natCast]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hj' : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hmul := mul_le_mul_of_nonneg_right hj' (norm_nonneg ω)
  nlinarith [norm_nonneg ω]

noncomputable def columnLogarithmicMatrix {ι σ : Type*} [Fintype σ]
    (h : ι → ℕ) (l : ι → σ → ℕ) (a : ι → σ → ℕ)
    (z : ι → ℂ) (ℓ : ι → ℕ) : Matrix ι ι ℂ :=
  fun i j => taylorCoefficient
    (fun t => columnFunction (h j) (l j) (a i) (z i + Complex.log (1 + t))) (ℓ i) 0

/-- The analytic estimate specialized to the selected monomial columns of
the interpolation matrix. No analytic estimate is an extra hypothesis. -/
theorem column_logarithmic_collision_bound {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ]
    (h : ι → ℕ) (l : ι → σ → ℕ) (a : ι → σ → ℕ)
    (z : ι → ℂ) (ℓ : ι → ℕ) (R H w₀ wstar v₀ : ℝ)
    (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hwstar : 0 < wstar)
    (hz : ∀ i, ‖z i‖ + 1 ≤ R / 2)
    (hh : ∀ j, (h j : ℝ) ≤ H / w₀)
    (hl : ∀ j, ((∑ k, l j k : ℕ) : ℝ) ≤ H / wstar)
    (horders : ((∑ i, ℓ i : ℕ) : ℝ) ≤ Fintype.card ι * H / v₀)
    (hne : (columnLogarithmicMatrix h l a z ℓ).det ≠ 0) :
    Real.log ‖(columnLogarithmicMatrix h l a z ℓ).det‖ ≤
      -(Real.log 2 / 4) * collisionMass a +
        Fintype.card ι * H * (R / w₀ + Real.log (2 * R) / wstar + Real.log 2 / v₀) +
        Fintype.card ι * (Real.log (Fintype.card ι + 1) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-(Real.log 2 / 2)))) := by
  exact logarithmic_collision_degree_bound a (fun k j => columnFunction (h j) (l j) k)
    z ℓ R H (R / w₀ + Real.log (2 * R) / wstar) v₀ (by linarith) hz
    (fun k j => differentiable_columnFunction _ _ _)
    (fun k j w hw => norm_columnFunction_le_exp _ _ _ hR hw₀ hwstar
      (hh j) (hl j) (by
        have heq : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
        exact heq.le))
    horders hne

end QuadraticField
