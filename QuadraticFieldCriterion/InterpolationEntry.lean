import QuadraticFieldCriterion.RowChoices
import QuadraticFieldCriterion.CoefficientClearing

/-! # Identifying the arithmetic and analytic interpolation entries -/

namespace QuadraticField

theorem truncated_monomial_entry_eq_translated {m K : ℕ} (T : Fin m → ℕ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (j : Fin K)
    (row column : Fin (m + 1) →₀ ℕ) (ω : ℂ) (error : Fin m → ℂ)
    (hy : y j = (Complex.exp ω) ^ (j : ℕ))
    (hc : ∀ i, c j i = (j : ℂ) * ω + error i) :
    MvPowerSeries.coeff row (MvPolynomial.eval₂ MvPowerSeries.C
      (ImaginaryQuadratic.truncatedLocalVariables T y c j) (MvPolynomial.monomial column 1)) =
      translatedInterpolationEntry m (column 0) j (row 0) ω T
        (fun i => column i.succ) row.tail error := by
  classical
  simp only [MvPolynomial.eval₂_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ,
    ImaginaryQuadratic.truncatedLocalVariables, Fin.cases_zero, Fin.cases_succ, hy, hc]
  change MvPowerSeries.coeff row _ = MvPowerSeries.coeff (row.tail.cons (row 0)) _
  rw [Finsupp.cons_tail]

theorem map_quadraticInterpolationMatrix_eq_translated (D : ℤ) {m K : ℕ} {ι : Type*}
    (T : Fin m → ℕ) (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (centre : ι → Fin K) (row column : ι → Fin (m + 1) →₀ ℕ)
    (φ : Algebra D →+* ℂ) (hφ : ∀ r : ℚ, φ (algebraMap ℚ (Algebra D) r) = (r : ℂ))
    (ω : ℂ) (error : ι → Fin m → ℂ)
    (hy : ∀ r, φ (y (centre r)) = (Complex.exp ω) ^ (centre r : ℕ))
    (hc : ∀ r i, φ (c (centre r) i) = (centre r : ℂ) * ω + error r i) :
    (quadraticInterpolationMatrix D T y c centre row column).map φ =
      Matrix.of (fun r k => translatedInterpolationEntry m (column k 0) (centre r) (row r 0)
        ω T (fun i => column k i.succ) (row r).tail (error r)) := by
  rw [map_quadraticInterpolationMatrix D T y c centre row column φ hφ]
  ext r k
  exact truncated_monomial_entry_eq_translated T (fun j => φ (y j)) (fun j i => φ (c j i))
    (centre r) (row r) (column k) ω (error r) (hy r) (hc r)

end QuadraticField
