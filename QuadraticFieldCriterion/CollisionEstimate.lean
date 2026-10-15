import QuadraticFieldCriterion.DeterminantExpansion
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The repeated-index determinant estimate

We first bound every finite Taylor truncation uniformly. The estimate exploits
only equality of coefficient rows with the same `(transverse index, degree)`.
It therefore applies to either embedding and arbitrary analytic centres.
-/

namespace QuadraticField

noncomputable def collisionMass {ι κ : Type*} [Fintype ι] (a : ι → κ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.univ.image a,
    (((Finset.univ.filter (fun i => a i = k)).card : ℝ) ^ 2)

theorem finite_geometric_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ n : Fin N, r ^ (n : ℕ) ≤ (1 - r)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul_neg r N
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  nlinarith [pow_nonneg hr0 N]

/-- Uniform bound for a coefficient determinant in a nonzero Taylor term. -/
theorem weighted_coefficient_det_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ) (d : ι → ℕ)
    (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (B b : ℝ) (T : ι → ℝ) (hB : 0 ≤ B) (hb : 0 < b)
    (hT : ∀ i, 0 ≤ T i)
    (hcoeff : ∀ k n j, ‖coeff k n j‖ ≤ B)
    (htest : ∀ i n, ‖test i n‖ ≤ T i * Real.exp (-b * n)) :
    (∏ i, ‖test i (d i)‖) *
        ‖(Matrix.of (fun i j => coeff (a i) (d i) j)).det‖ ≤
      ((Fintype.card ι).factorial * B ^ Fintype.card ι * (∏ i, T i) *
        Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι))) *
        (∏ i, Real.exp (-(b / 2) * d i)) := by
  classical
  let M := Matrix.of (fun i j => coeff (a i) (d i) j)
  have hTp : 0 ≤ ∏ i, T i := Finset.prod_nonneg (fun i hi => hT i)
  have hconst : 0 ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι * (∏ i, T i) := by
    positivity
  by_cases hzero : M.det = 0
  · rw [show (Matrix.of (fun i j => coeff (a i) (d i) j)).det = 0 from hzero,
      norm_zero, mul_zero]
    positivity
  have hdegrees := twice_sum_degrees_ge_fibre_squares a d
    (degrees_injective_on_fibre a d coeff hzero)
  change collisionMass a - Fintype.card ι ≤ 2 * ∑ i, (d i : ℝ) at hdegrees
  have hdecay : Real.exp (-b * ∑ i, (d i : ℝ)) ≤
      Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι)) *
        Real.exp (-(b / 2) * ∑ i, (d i : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdet : ‖M.det‖ ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
    simpa using norm_det_le_factorial_mul_prod M (fun _ => B) (fun _ => hB)
      (fun i j => hcoeff _ _ _)
  have hprod : (∏ i, ‖test i (d i)‖) ≤
      (∏ i, T i) * Real.exp (-b * ∑ i, (d i : ℝ)) := by
    calc
      _ ≤ ∏ i, (T i * Real.exp (-b * d i)) :=
        Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => htest _ _)
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
  calc
    _ ≤ ((∏ i, T i) * Real.exp (-b * ∑ i, (d i : ℝ))) *
        ((Fintype.card ι).factorial * B ^ Fintype.card ι) :=
      mul_le_mul hprod hdet (norm_nonneg _) (by positivity)
    _ ≤ ((∏ i, T i) * (Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι)) *
        Real.exp (-(b / 2) * ∑ i, (d i : ℝ)))) *
        ((Fintype.card ι).factorial * B ^ Fintype.card ι) := by
      gcongr
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]; ring

/-- The collision bound is independent of the Taylor cutoff `N`. -/
theorem finite_collision_estimate {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ)
    (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (B b : ℝ) (T : ι → ℝ) (hB : 0 ≤ B) (hb : 0 < b)
    (hT : ∀ i, 0 ≤ T i)
    (hcoeff : ∀ k n j, ‖coeff k n j‖ ≤ B)
    (htest : ∀ i n, ‖test i n‖ ≤ T i * Real.exp (-b * n)) (N : ℕ) :
    ‖(Matrix.of (fun i j => ∑ n : Fin N, test i n * coeff (a i) n j)).det‖ ≤
      ((Fintype.card ι).factorial * B ^ Fintype.card ι * (∏ i, T i) *
        Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι))) *
        ((1 - Real.exp (-(b / 2)))⁻¹) ^ Fintype.card ι := by
  classical
  let C : ℝ := (Fintype.card ι).factorial * B ^ Fintype.card ι * (∏ i, T i) *
    Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι))
  have hTp : 0 ≤ ∏ i, T i := Finset.prod_nonneg (fun i hi => hT i)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg0 : 0 ≤ Real.exp (-(b / 2)) := (Real.exp_pos _).le
  have hg1 : Real.exp (-(b / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc
    _ ≤ ∑ d : ι → Fin N, (∏ i, ‖test i (d i)‖) *
        ‖(Matrix.of (fun i j => coeff (a i) (d i) j)).det‖ :=
      norm_det_sum_smul_rows_le (fun (i : ι) (n : Fin N) => test i n)
        (fun (i : ι) (n : Fin N) => coeff (a i) n)
    _ ≤ ∑ d : ι → Fin N, C * ∏ i, Real.exp (-(b / 2) * (d i : ℕ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact weighted_coefficient_det_bound a (fun i => d i) coeff test B b T
        hB hb hT hcoeff htest
    _ = C * ∏ _i : ι, ∑ n : Fin N, Real.exp (-(b / 2) * (n : ℕ)) := by
      rw [← Finset.mul_sum, Fintype.prod_sum]
    _ ≤ C * ((1 - Real.exp (-(b / 2)))⁻¹) ^ Fintype.card ι := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        _ ≤ ∏ _i : ι, (1 - Real.exp (-(b / 2)))⁻¹ := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact Finset.sum_nonneg (fun n hn => (Real.exp_pos _).le)
          · intro i hi
            simpa only [mul_comm (-(b / 2)), Real.exp_nat_mul] using
              finite_geometric_le_inv hg0 hg1 N
        _ = _ := by simp

theorem summable_test_mul_coefficient {ι κ : Type*}
    (a : ι → κ) (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (B b : ℝ) (T : ι → ℝ) (_hB : 0 ≤ B) (hb : 0 < b)
    (hT : ∀ i, 0 ≤ T i)
    (hcoeff : ∀ k n j, ‖coeff k n j‖ ≤ B)
    (htest : ∀ i n, ‖test i n‖ ≤ T i * Real.exp (-b * n)) (i j : ι) :
    Summable (fun n => test i n * coeff (a i) n j) := by
  have hgeom := summable_geometric_of_lt_one (Real.exp_pos (-b)).le
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb))
  apply (hgeom.mul_left (T i * B)).of_norm_bounded
  intro n
  rw [norm_mul]
  calc
    _ ≤ (T i * Real.exp (-b * n)) * B :=
      mul_le_mul (htest i n) (hcoeff (a i) n j) (norm_nonneg _)
        (mul_nonneg (hT i) (Real.exp_pos _).le)
    _ = (T i * B) * Real.exp (-b) ^ n := by
      rw [mul_comm (-b), Real.exp_nat_mul]
      ring

/-- The bound for finite Taylor sums passes to their absolutely convergent
limit. No exchange of an infinite determinant expansion is assumed. -/
theorem collision_estimate {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ)
    (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (B b : ℝ) (T : ι → ℝ) (hB : 0 ≤ B) (hb : 0 < b)
    (hT : ∀ i, 0 ≤ T i)
    (hcoeff : ∀ k n j, ‖coeff k n j‖ ≤ B)
    (htest : ∀ i n, ‖test i n‖ ≤ T i * Real.exp (-b * n)) :
    ‖(Matrix.of (fun i j => ∑' n, test i n * coeff (a i) n j)).det‖ ≤
      ((Fintype.card ι).factorial * B ^ Fintype.card ι * (∏ i, T i) *
        Real.exp (-(b / 4) * (collisionMass a - Fintype.card ι))) *
        ((1 - Real.exp (-(b / 2)))⁻¹) ^ Fintype.card ι := by
  classical
  let M : Matrix ι ι ℂ := fun i j => ∑' n, test i n * coeff (a i) n j
  let truncations : ℕ → Matrix ι ι ℂ :=
    fun N i j => ∑ n : Fin N, test i n * coeff (a i) n j
  have hlim : Filter.Tendsto truncations Filter.atTop (nhds M) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (summable_test_mul_coefficient a coeff test B b T hB hb hT hcoeff htest i j).hasSum.tendsto_sum_nat
    have heq : (fun N => truncations N i j) =
        (fun N => ∑ n ∈ Finset.range N, test i n * coeff (a i) n j) := by
      funext N
      exact Fin.sum_univ_eq_sum_range (fun n => test i n * coeff (a i) n j) N
    rw [heq]
    exact h
  have hdet := (continuous_id.matrix_det.tendsto M).comp hlim
  have hnorm := hdet.norm
  apply le_of_tendsto hnorm
  exact Filter.Eventually.of_forall (fun N =>
    finite_collision_estimate a coeff test B b T hB hb hT hcoeff htest N)

end QuadraticField
