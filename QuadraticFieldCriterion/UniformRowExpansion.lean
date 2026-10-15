import QuadraticFieldCriterion.InterpolationRowExpansion
import QuadraticFieldCriterion.FiniteChoices

/-! # A common finite set of choices for all monomial columns -/

namespace QuadraticField

noncomputable def rowExpansionTerm (m h j s : ℕ) (ω : ℂ) (T l : Fin m → ℕ)
    (β : Fin m →₀ ℕ) (error : Fin m → ℂ) (a : Fin m → ℕ) : ℂ :=
  if ∀ i, β i ≤ a i then
    ∑ k ∈ Finset.range (s + 1),
      ∑ e : ∀ i, Fin (a i - β i + 1),
        translationScalar m T a β (fun i => (e i : ℕ)) error k *
          taylorCoefficient (fun t => columnFunction h l a
            ((j : ℂ) * ω + Complex.log (1 + t))) (s - k) 0
  else 0

theorem rowExpansionTerm_eq_zero (m h j s : ℕ) (ω : ℂ) (T l : Fin m → ℕ)
    (β : Fin m →₀ ℕ) (error : Fin m → ℂ) (a : Fin m → ℕ)
    (ha : ¬ (∀ i, a i ≤ l i)) :
    rowExpansionTerm m h j s ω T l β error a = 0 := by
  classical
  have hz : columnFunction h l a = fun _ => 0 := by
    funext z
    simp only [columnFunction, ite_eq_right ha]
  have hc : ∀ k, taylorCoefficient (fun _ : ℂ => (0 : ℂ)) k 0 = 0 := by
    intro k
    have h := (HasTaylorSeries.const (0 : ℂ)).coeff_eq k
    simpa using h
  simp [rowExpansionTerm, hz, hc]

theorem uniform_interpolation_row_expansion (m h j s : ℕ) (ω : ℂ) (T l N : Fin m → ℕ)
    (hN : ∀ i, l i ≤ N i) (β : Fin m →₀ ℕ) (error : Fin m → ℂ) :
    MvPowerSeries.coeff (β.cons s)
      (((MvPowerSeries.C ((Complex.exp ω) ^ j) * (1 + MvPowerSeries.X 0)) ^ h) *
        ∏ i, (MvPowerSeries.C ((j : ℂ) * ω + error i) + MvPowerSeries.X i.succ +
          ImaginaryQuadratic.truncatedLog m (T i)) ^ l i) =
      ∑ a : ∀ i, Fin (N i + 1),
        rowExpansionTerm m h j s ω T l β error (fun i => (a i : ℕ)) := by
  rw [interpolation_row_expansion]
  exact sum_fin_pi_extend l N hN (rowExpansionTerm m h j s ω T l β error)
    (rowExpansionTerm_eq_zero m h j s ω T l β error)

end QuadraticField
