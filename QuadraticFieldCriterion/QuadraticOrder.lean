import QuadraticFieldCriterion.QuadraticCriterionProof

/-! # Denominator-cleared determinants in the quadratic order -/

namespace QuadraticField

abbrev IntegerAlgebra (D : ℤ) := QuadraticAlgebra ℤ D 0

/-- The order `ℤ[√D]` maps into the rational quadratic algebra. -/
def integerEmbedding (D : ℤ) : IntegerAlgebra D →+* Algebra D where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp

def integerOrder (D : ℤ) : Subring (Algebra D) := (integerEmbedding D).range

theorem mem_integerOrder_iff (D : ℤ) (z : Algebra D) :
    z ∈ integerOrder D ↔ ∃ a b : ℤ, z = ⟨(a : ℚ), (b : ℚ)⟩ := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.re, w.im, hw.symm⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨⟨a, b⟩, rfl⟩

theorem det_mem_integerOrder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℤ) (M : Matrix ι ι (Algebra D))
    (hM : ∀ i j, M i j ∈ integerOrder D) : M.det ∈ integerOrder D := by
  classical
  rw [Matrix.det_apply']
  apply (integerOrder D).sum_mem
  intro σ hσ
  apply (integerOrder D).mul_mem
  · exact intCast_mem (integerOrder D) _
  · exact (integerOrder D).prod_mem (fun i hi => hM (σ i) i)

/-- The arithmetic lower bound applies to the product of the two embedded
determinants even when the absolute values of the embeddings differ. -/
theorem one_le_norm_det_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℤ} (hD : ¬ IsSquare D) (M : Matrix ι ι (Algebra D))
    (hM : ∀ i j, M i j ∈ integerOrder D) (hne : M.det ≠ 0) :
    1 ≤ ‖(M.map (embedding D)).det‖ * ‖(M.map (conjugateEmbedding D)).det‖ := by
  obtain ⟨a, b, hab⟩ := (mem_integerOrder_iff D M.det).mp (det_mem_integerOrder D M hM)
  have hn : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne (hab.trans (by rfl))
  have hp : (M.map (embedding D)).det = embedding D M.det :=
    ((embedding D).map_det M).symm
  let σ : Algebra D →+* ℂ := (embedding D).toRingHom.comp (starRingEnd (Algebra D))
  have hm : (M.map (conjugateEmbedding D)).det = conjugateEmbedding D M.det :=
    (σ.map_det M).symm
  rw [hp, hm, hab, embedding_apply, conjugateEmbedding_apply]
  norm_cast
  exact one_le_product_norm hD hn

/-- Multiplying rows and columns multiplies the determinant by their products. -/
theorem det_scaled {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (r c : ι → R) :
    (Matrix.of (fun i j => r i * M i j * c j)).det =
      (∏ i, r i) * (∏ i, c i) * M.det := by
  have heq : Matrix.of (fun i j => r i * M i j * c j) =
      Matrix.of (fun i j => r i * (c j * M i j)) := by
    ext i j
    simp only [Matrix.of_apply]
    ring
  rw [heq]
  calc
    _ = (∏ i, r i) * (Matrix.of (fun i j => c j * M i j)).det :=
      Matrix.det_mul_column r (Matrix.of (fun i j => c j * M i j))
    _ = _ := by rw [Matrix.det_mul_row c M]; ring

/-- If a rational scaling puts every entry in the quadratic order, the norm
bound uses the same scaling factor in both embeddings. -/
theorem scaled_norm_det_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℤ} (hD : ¬ IsSquare D) (M : Matrix ι ι (Algebra D))
    (r c : ι → ℚ) (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hM : ∀ i j, algebraMap ℚ (Algebra D) (r i) * M i j *
      algebraMap ℚ (Algebra D) (c j) ∈ integerOrder D)
    (hne : M.det ≠ 0) :
    1 ≤ |(((∏ i, r i) * (∏ i, c i) : ℚ) : ℝ)| ^ 2 *
      (‖(M.map (embedding D)).det‖ * ‖(M.map (conjugateEmbedding D)).det‖) := by
  let N : Matrix ι ι (Algebra D) := fun i j =>
    algebraMap ℚ (Algebra D) (r i) * M i j * algebraMap ℚ (Algebra D) (c j)
  have hdet : N.det = algebraMap ℚ (Algebra D) ((∏ i, r i) * (∏ i, c i)) * M.det := by
    rw [show N = Matrix.of (fun i j => algebraMap ℚ (Algebra D) (r i) * M i j *
      algebraMap ℚ (Algebra D) (c j)) from rfl, det_scaled]
    simp [map_mul, map_prod, mul_assoc]
  have hs : (∏ i, r i) * (∏ i, c i) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi => hr i))
      (Finset.prod_ne_zero_iff.mpr (fun i hi => hc i))
  let : Fact (¬ IsSquare (D : ℚ)) :=
    ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  have hN : N.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero ((map_ne_zero (algebraMap ℚ (Algebra D))).mpr hs) hne
  have h := one_le_norm_det_product hD N hM hN
  have hp : (N.map (embedding D)).det =
      (((∏ i, r i) * (∏ i, c i) : ℚ) : ℂ) * (M.map (embedding D)).det := by
    have hmap : (N.map (embedding D)).det = embedding D N.det :=
      ((embedding D).map_det N).symm
    rw [hmap, hdet, map_mul,
      (embedding D).commutes]
    have hmapM : (M.map (embedding D)).det = embedding D M.det :=
      ((embedding D).map_det M).symm
    rw [hmapM]
    simp
  let σ : Algebra D →+* ℂ := (embedding D).toRingHom.comp (starRingEnd (Algebra D))
  have hm : (N.map (conjugateEmbedding D)).det =
      (((∏ i, r i) * (∏ i, c i) : ℚ) : ℂ) * (M.map (conjugateEmbedding D)).det := by
    have hmap : (N.map (conjugateEmbedding D)).det = σ N.det :=
      (σ.map_det N).symm
    rw [hmap, hdet, map_mul]
    have hsigma : σ (algebraMap ℚ (Algebra D) ((∏ i, r i) * (∏ i, c i))) =
        (((∏ i, r i) * (∏ i, c i) : ℚ) : ℂ) := by
      change embedding D (star (algebraMap ℚ (Algebra D)
        ((∏ i, r i) * (∏ i, c i)))) = _
      rw [QuadraticAlgebra.algebraMap_eq]
      simp only [QuadraticAlgebra.star_mk, mul_zero, add_zero, neg_zero]
      rw [embedding_apply]
      simp
    have hmapM : (M.map (conjugateEmbedding D)).det = σ M.det :=
      (σ.map_det M).symm
    rw [hsigma, hmapM]
  rw [hp, hm, norm_mul, norm_mul, Complex.norm_ratCast] at h
  convert h using 1
  ring

end QuadraticField
