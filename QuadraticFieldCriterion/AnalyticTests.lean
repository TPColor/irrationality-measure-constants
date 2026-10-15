import QuadraticFieldCriterion.CollisionEstimate
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Cauchy estimates for the logarithmic coefficient tests

The tests are normalized Taylor derivatives at `t = 0` of
`((z₀ + log(1+t))/R)^n`. They obey geometric decay in `n`, uniformly in
every centre inside the half-radius region.
-/

namespace QuadraticField

noncomputable def taylorCoefficient (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv n f z / n.factorial

theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {z : ℂ} {R B : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball z R))
    (hB : ∀ w ∈ Metric.sphere z R, ‖f w‖ ≤ B) (n : ℕ) :
    ‖taylorCoefficient f n z‖ ≤ B / R ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hB
  rw [taylorCoefficient, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  convert h using 1
  ring

theorem one_add_mem_slitPlane_of_norm_le_half {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    1 + t ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hre := (abs_le.mp (Complex.abs_re_le_norm t)).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem differentiableOn_log_test (z : ℂ) (R : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (fun t : ℂ => ((z + Complex.log (1 + t)) / (R : ℂ)) ^ n)
      (Metric.closedBall 0 (1 / 2)) := by
  intro t ht
  have ht' : ‖t‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using ht
  have hlog := (Complex.differentiableAt_log
    (one_add_mem_slitPlane_of_norm_le_half ht')).comp t
      (differentiableAt_const (1 : ℂ) |>.add differentiableAt_id)
  exact ((differentiableAt_const z |>.add hlog).div_const (R : ℂ)).pow n
    |>.differentiableWithinAt

noncomputable def logarithmicTest (z : ℂ) (R : ℝ) (ℓ n : ℕ) : ℂ :=
  taylorCoefficient (fun t : ℂ => ((z + Complex.log (1 + t)) / (R : ℂ)) ^ n) ℓ 0

/-- Geometric Taylor-degree decay is uniform on all permitted centres. -/
theorem norm_logarithmicTest_le {z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ + 1 ≤ R / 2) (ℓ n : ℕ) :
    ‖logarithmicTest z R ℓ n‖ ≤ (2 : ℝ) ^ ℓ * (1 / 2 : ℝ) ^ n := by
  have hsup : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      ‖((z + Complex.log (1 + t)) / (R : ℂ)) ^ n‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro t ht
    have ht' : ‖t‖ = 1 / 2 := by simpa [Metric.mem_sphere, dist_zero_right] using ht
    have hlog : ‖Complex.log (1 + t)‖ ≤ 1 := by
      have h := Complex.norm_log_one_add_half_le_self ht'.le
      rw [ht'] at h
      linarith
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _) _ n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply (div_le_iff₀ hR).mpr
    have h := norm_add_le z (Complex.log (1 + t))
    linarith
  have hf := (differentiableOn_log_test z R n).mono
    Metric.closure_ball_subset_closedBall |>.diffContOnCl
  have h := norm_taylorCoefficient_le (by norm_num : (0 : ℝ) < 1 / 2) hf hsup ℓ
  change ‖logarithmicTest z R ℓ n‖ ≤ _ at h
  convert h using 1
  simp only [div_pow, one_pow]
  field_simp

/-- The exponential form required by the collision estimate. -/
theorem norm_logarithmicTest_le_exp {z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ + 1 ≤ R / 2) (ℓ n : ℕ) :
    ‖logarithmicTest z R ℓ n‖ ≤
      (2 : ℝ) ^ ℓ * Real.exp (-Real.log 2 * n) := by
  have heq : Real.exp (-Real.log 2 * n) = (1 / 2 : ℝ) ^ n := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [heq]
  exact norm_logarithmicTest_le hR hz ℓ n

/-- Cauchy's estimate also bounds normalized Taylor coefficients of the
entire column functions on the larger disk. -/
theorem norm_scaled_taylorCoefficient_le {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hf : Differentiable ℂ f)
    (hB : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖f w‖ ≤ B) (n : ℕ) :
    ‖taylorCoefficient f n 0 * (R : ℂ) ^ n‖ ≤ B := by
  have hd : DiffContOnCl ℂ f (Metric.ball 0 R) := hf.differentiableOn.diffContOnCl
  have h := norm_taylorCoefficient_le hR hd hB n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact (le_div_iff₀ (pow_pos hR n)).mp h

end QuadraticField
