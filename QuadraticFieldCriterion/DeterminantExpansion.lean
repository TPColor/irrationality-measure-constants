import QuadraticFieldCriterion.TaylorDegrees
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Matrix

/-! # Finite row expansions and their determinant bounds -/

namespace QuadraticField

theorem det_sum_smul_rows_dependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (ξ : ∀ i, κ i → ℂ) (row : ∀ i, κ i → ι → ℂ) :
    (Matrix.of (fun i j => ∑ k, ξ i k * row i k j)).det =
      ∑ f : ∀ i, κ i, (∏ i, ξ i (f i)) *
        (Matrix.of (fun i j => row i (f i) j)).det := by
  have h := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i k j => ξ i k * row i k j)
  change Matrix.det (fun i => ∑ k, fun j => ξ i k * row i k j) =
    ∑ f : ∀ i, κ i, Matrix.det (fun i j => ξ i (f i) * row i (f i) j) at h
  have heq : Matrix.of (fun i j => ∑ k, ξ i k * row i k j) =
      (fun i => ∑ k, fun j => ξ i k * row i k j) := by ext i j; simp
  rw [heq, h]
  apply Finset.sum_congr rfl
  intro f hf
  exact Matrix.det_mul_column (fun i => ξ i (f i)) _

theorem norm_det_sum_smul_rows_dependent_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (ξ : ∀ i, κ i → ℂ) (row : ∀ i, κ i → ι → ℂ) :
    ‖(Matrix.of (fun i j => ∑ k, ξ i k * row i k j)).det‖ ≤
      ∑ f : ∀ i, κ i, (∏ i, ‖ξ i (f i)‖) *
        ‖(Matrix.of (fun i j => row i (f i) j)).det‖ := by
  rw [det_sum_smul_rows_dependent]
  calc
    _ ≤ ∑ f : ∀ i, κ i, ‖(∏ i, ξ i (f i)) *
        (Matrix.of (fun i j => row i (f i) j)).det‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_prod]

/-- The elementary determinant bound from its permutation expansion. -/
theorem norm_det_le_factorial_mul_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (B : ι → ℝ) (_hB : ∀ i, 0 ≤ B i)
    (hM : ∀ i j, ‖M i j‖ ≤ B i) :
    ‖M.det‖ ≤ (Fintype.card ι).factorial * ∏ i, B i := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, B i := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rw [Complex.norm_intCast, ← Int.cast_abs, Equiv.Perm.sign_abs]
        norm_num
      rw [norm_mul, hsign, one_mul, norm_prod]
      calc
        _ ≤ ∏ i, B (σ i) := Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => hM _ _)
        _ = ∏ i, B i := Equiv.prod_comp σ B
    _ = _ := by simp [Fintype.card_perm]

/-- Multilinearity expands independent finite choices in every row. -/
theorem det_sum_rows {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (row : ι → κ → ι → ℂ) :
    (Matrix.of (fun i j => ∑ k, row i k j)).det =
      ∑ f : ι → κ, (Matrix.of (fun i j => row i (f i) j)).det := by
  have h := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum row
  change Matrix.det (fun i => ∑ j, row i j) =
    ∑ f : ι → κ, Matrix.det (fun i => row i (f i)) at h
  have heq : Matrix.of (fun i j => ∑ k, row i k j) = (fun i => ∑ k, row i k) := by
    ext i j
    simp
  rw [heq]
  exact h

/-- Scalar coefficients factor out of each term in the row expansion. -/
theorem det_sum_smul_rows {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (ξ : ι → κ → ℂ) (row : ι → κ → ι → ℂ) :
    (Matrix.of (fun i j => ∑ k, ξ i k * row i k j)).det =
      ∑ f : ι → κ, (∏ i, ξ i (f i)) *
        (Matrix.of (fun i j => row i (f i) j)).det := by
  rw [det_sum_rows]
  apply Finset.sum_congr rfl
  intro f hf
  exact Matrix.det_mul_column (fun i => ξ i (f i)) _

/-- Taking absolute values before summing is valid for the full row expansion. -/
theorem norm_det_sum_smul_rows_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (ξ : ι → κ → ℂ) (row : ι → κ → ι → ℂ) :
    ‖(Matrix.of (fun i j => ∑ k, ξ i k * row i k j)).det‖ ≤
      ∑ f : ι → κ, (∏ i, ‖ξ i (f i)‖) *
        ‖(Matrix.of (fun i j => row i (f i) j)).det‖ := by
  rw [det_sum_smul_rows]
  calc
    _ ≤ ∑ f : ι → κ, ‖(∏ i, ξ i (f i)) *
        (Matrix.of (fun i j => row i (f i) j)).det‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_prod]

end QuadraticField
