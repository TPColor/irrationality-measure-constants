import QuadraticFieldCriterion.RowTranslation
import QuadraticFieldCriterion.TailBudget
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Analytic coefficient tests and formal series multiplication -/

namespace QuadraticField

def timeEmbedding (m : ℕ) : Unit ↪ Fin (m + 1) :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

noncomputable def timeProjection (m : ℕ) :
    MvPowerSeries (Fin (m + 1)) ℂ →ₐ[ℂ] PowerSeries ℂ :=
  MvPowerSeries.killCompl (timeEmbedding m)

theorem coeff_timeProjection (m k : ℕ) (P : MvPowerSeries (Fin (m + 1)) ℂ) :
    PowerSeries.coeff k (timeProjection m P) = MvPowerSeries.coeff (Finsupp.single 0 k) P := by
  change MvPowerSeries.coeff (Finsupp.single () k) (MvPowerSeries.killCompl (timeEmbedding m) P) = _
  rw [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_single]
  rfl

structure HasTaylorSeries (f : ℂ → ℂ) (P : PowerSeries ℂ) : Prop where
  analytic : AnalyticAt ℂ f 0
  coeff_eq : ∀ k, taylorCoefficient f k 0 = PowerSeries.coeff k P

theorem HasTaylorSeries.const (c : ℂ) : HasTaylorSeries (fun _ => c) (PowerSeries.C c) := by
  refine ⟨analyticAt_const, ?_⟩
  intro k
  have h := taylorCoefficient_monomial c 0 k
  simpa only [pow_zero, mul_one, PowerSeries.coeff_C] using h

theorem HasTaylorSeries.mul {f g : ℂ → ℂ} {P Q : PowerSeries ℂ}
    (hf : HasTaylorSeries f P) (hg : HasTaylorSeries g Q) :
    HasTaylorSeries (fun t => f t * g t) (P * Q) := by
  refine ⟨hf.analytic.mul hg.analytic, ?_⟩
  intro k
  rw [taylorCoefficient_mul hf.analytic hg.analytic, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i P * PowerSeries.coeff j Q) k]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hf.coeff_eq, hg.coeff_eq]

theorem HasTaylorSeries.add {f g : ℂ → ℂ} {P Q : PowerSeries ℂ}
    (hf : HasTaylorSeries f P) (hg : HasTaylorSeries g Q) :
    HasTaylorSeries (fun t => f t + g t) (P + Q) := by
  refine ⟨hf.analytic.add hg.analytic, ?_⟩
  intro k
  simp only [taylorCoefficient, iteratedDeriv_fun_add hf.analytic.contDiffAt hg.analytic.contDiffAt,
    add_div, map_add]
  exact congrArg₂ (· + ·) (hf.coeff_eq k) (hg.coeff_eq k)

theorem HasTaylorSeries.congr {f g : ℂ → ℂ} {P : PowerSeries ℂ}
    (hf : HasTaylorSeries f P) (hfg : f =ᶠ[nhds (0 : ℂ)] g) : HasTaylorSeries g P := by
  refine ⟨hf.analytic.congr hfg, ?_⟩
  intro k
  rw [← hf.coeff_eq]
  exact congrArg (fun x : ℂ => x / (k.factorial : ℂ)) (hfg.iteratedDeriv_eq k).symm

theorem HasTaylorSeries.id : HasTaylorSeries (fun t : ℂ => t) PowerSeries.X := by
  refine ⟨analyticAt_id, ?_⟩
  intro k
  have h := taylorCoefficient_monomial 1 1 k
  simpa [PowerSeries.coeff_X] using h

noncomputable def logarithmSeries (m : ℕ) : PowerSeries ℂ :=
  timeProjection m (LiuJiangZhang.logOneAdd m)

theorem logarithm_hasTaylorSeries (m : ℕ) :
    HasTaylorSeries (fun t : ℂ => Complex.log (1 + t)) (logarithmSeries m) := by
  refine ⟨hasFPowerSeriesAt_clog_one_add.analyticAt, ?_⟩
  intro k
  rw [taylorCoefficient_log_one_add, logarithmSeries, coeff_timeProjection]
  simp [LiuJiangZhang.logOneAdd, MvPowerSeries.coeff_apply]

theorem HasTaylorSeries.pow {f : ℂ → ℂ} {P : PowerSeries ℂ}
    (hf : HasTaylorSeries f P) (n : ℕ) : HasTaylorSeries (fun t => f t ^ n) (P ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using HasTaylorSeries.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem HasTaylorSeries.prod {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (P : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, HasTaylorSeries (f i) (P i)) :
    HasTaylorSeries (fun t => ∏ i ∈ s, f i t) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, map_one] using HasTaylorSeries.const 1
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem logarithmTail_hasTaylorSeries (m T : ℕ) :
    HasTaylorSeries (logarithmTail T)
      (timeProjection m (ImaginaryQuadratic.truncatedLog m T - LiuJiangZhang.logOneAdd m)) := by
  refine ⟨(differentiableOn_logarithmTail T).analyticAt ?_, ?_⟩
  · exact Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2)
  · intro k
    rw [coeff_timeProjection]
    exact taylorCoefficient_logarithmTail m T k

/-- Products and powers of the analytic tails have exactly the formal
coefficients used in the interpolation construction. -/
theorem taylorCoefficient_tail_product (m : ℕ) (T e : Fin m → ℕ) (k : ℕ) :
    taylorCoefficient (fun t => ∏ i, logarithmTail (T i) t ^ e i) k 0 =
      MvPowerSeries.coeff (Finsupp.single 0 k)
        (∏ i, (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i) := by
  have h := HasTaylorSeries.prod Finset.univ
    (fun i t => logarithmTail (T i) t ^ e i)
    (fun i => (timeProjection m (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m)) ^ e i)
    (fun i _ => (logarithmTail_hasTaylorSeries m (T i)).pow (e i))
  have hc := h.coeff_eq k
  simp only [← map_pow, ← map_prod] at hc
  rw [coeff_timeProjection] at hc
  exact hc

theorem norm_formal_tail_product_coefficient_le (m : ℕ) (T e : Fin m → ℕ)
    (hT : ∀ i, 0 < T i) (k : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 k)
        (∏ i, (ImaginaryQuadratic.truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i)‖ ≤
      (2 : ℝ) ^ k := by
  rw [← taylorCoefficient_tail_product]
  exact norm_tail_product_taylorCoefficient_le T e hT k

end QuadraticField
