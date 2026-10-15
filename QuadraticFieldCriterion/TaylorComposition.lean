import QuadraticFieldCriterion.EntireColumns
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Applying logarithmic coefficient tests to entire Taylor series

Local uniform convergence justifies taking any fixed normalized derivative
term by term. This identifies the abstract collision matrix with actual
logarithmic derivatives of the entire column functions.
-/

open Filter Topology

namespace QuadraticField

theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

theorem locallyUniform_iteratedDeriv {ι : Type*} {p : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hlim : TendstoLocallyUniformlyOn F f p U)
    (hF : ∀ᶠ i in p, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) p U := by
  induction n with
  | zero => simpa using hlim
  | succ n ih =>
    have hd : ∀ᶠ i in p, DifferentiableOn ℂ (iteratedDeriv n (F i)) U :=
      hF.mono (fun i hi => differentiableOn_iteratedDeriv hi hU n)
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hd hU

theorem hasSum_taylorCoefficient_of_uniform_bound {ι : Type*}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {u : ι → ℝ} {z : ℂ}
    (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hU : IsOpen U) (hz : z ∈ U)
    (hbound : ∀ i w, w ∈ U → ‖F i w‖ ≤ u i)
    (hsum : ∀ w ∈ U, ∑' i, F i w = f w) (n : ℕ) :
    HasSum (fun i => taylorCoefficient (F i) n z) (taylorCoefficient f n z) := by
  classical
  have hlim := (tendstoUniformlyOn_tsum hu hbound).tendstoLocallyUniformlyOn
  have hlim' := hlim.congr_right (fun w hw => hsum w hw)
  have hder := locallyUniform_iteratedDeriv hlim'
    (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_sum (fun i _ => hF i))) hU n
  have hd : HasSum (fun i => iteratedDeriv n (F i) z) (iteratedDeriv n f z) := by
    change Tendsto (fun s : Finset ι => ∑ i ∈ s, iteratedDeriv n (F i) z)
      atTop (𝓝 (iteratedDeriv n f z))
    convert hder.tendsto_at hz using 1
    funext s
    exact (iteratedDeriv_fun_sum (fun i _ =>
      (hF i).contDiffOn hU |>.contDiffAt (hU.mem_nhds hz))).symm
  exact hd.div_const _

theorem hasSum_scaled_taylor {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : R ≠ 0) (w : ℂ) :
    HasSum (fun n => (w / (R : ℂ)) ^ n *
      (taylorCoefficient f n 0 * (R : ℂ) ^ n)) (f w) := by
  have hc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  convert Complex.hasSum_taylorSeries_of_entire hf 0 w using 1
  funext n
  simp only [sub_zero, smul_eq_mul, taylorCoefficient, div_pow]
  field_simp

theorem logarithmic_taylor_identity {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} {R B : ℝ} (hR : 0 < R) (hz : ‖z‖ + 1 ≤ R / 2)
    (hB : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖f w‖ ≤ B) (ℓ : ℕ) :
    ∑' n, logarithmicTest z R ℓ n * (taylorCoefficient f n 0 * (R : ℂ) ^ n) =
      taylorCoefficient (fun t => f (z + Complex.log (1 + t))) ℓ 0 := by
  let C : ℕ → ℂ := fun n => taylorCoefficient f n 0 * (R : ℂ) ^ n
  let F : ℕ → ℂ → ℂ := fun n t => ((z + Complex.log (1 + t)) / (R : ℂ)) ^ n * C n
  have hC : ∀ n, ‖C n‖ ≤ B := fun n => norm_scaled_taylorCoefficient_le hR hf hB n
  have hu : Summable (fun n : ℕ => B * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left B
  have hF : ∀ n, DifferentiableOn ℂ (F n) (Metric.ball 0 (1 / 2)) := by
    intro n
    exact ((differentiableOn_log_test z R n).mono Metric.ball_subset_closedBall).mul_const _
  have hbound : ∀ n t, t ∈ Metric.ball (0 : ℂ) (1 / 2) →
      ‖F n t‖ ≤ B * (1 / 2 : ℝ) ^ n := by
    intro n t ht
    have ht' : ‖t‖ ≤ 1 / 2 := by
      have ht'' : ‖t‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using ht
      exact ht''.le
    have hlog : ‖Complex.log (1 + t)‖ ≤ 1 := by
      have h := Complex.norm_log_one_add_half_le_self ht'
      linarith
    have hbase : ‖(z + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      apply (div_le_iff₀ hR).mpr
      have h := norm_add_le z (Complex.log (1 + t))
      linarith
    dsimp [F]
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (1 / 2 : ℝ) ^ n * B := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hbase n) (hC n) (norm_nonneg _)
        (by positivity)
      _ = _ := mul_comm _ _
  have hs := hasSum_taylorCoefficient_of_uniform_bound hu hF Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) hbound
    (fun t _ => (hasSum_scaled_taylor hf hR.ne' (z + Complex.log (1 + t))).tsum_eq) ℓ
  convert hs.tsum_eq using 1
  apply tsum_congr
  intro n
  change logarithmicTest z R ℓ n * C n = taylorCoefficient (F n) ℓ 0
  simp only [F, logarithmicTest, taylorCoefficient, iteratedDeriv_mul_const_field]
  ring

end QuadraticField
