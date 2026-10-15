import QuadraticFieldCriterion.TransverseCoefficients
import QuadraticFieldCriterion.TranslationScalars

/-! # Exact finite expansion of formal interpolation rows -/

namespace QuadraticField

noncomputable def formalColumn (m : ℕ) (B z : PowerSeries ℂ) (l a : Fin m → ℕ) :
    PowerSeries ℂ :=
  B * (∏ i, ((l i).choose (a i) : PowerSeries ℂ)) * z ^ (∑ i, (l i - a i))

theorem formal_row_expansion (m s : ℕ) (β : Fin m →₀ ℕ)
    (B z : PowerSeries ℂ) (T l : Fin m → ℕ) (error : Fin m → ℂ) :
    MvPowerSeries.coeff (β.cons s)
      (timeLift m B * ∏ i, (MvPowerSeries.X i.succ +
        timeLift m (z + (PowerSeries.C (error i) + tailSeries m (T i)))) ^ l i) =
      ∑ a : ∀ i, Fin (l i + 1),
        if ∀ i, β i ≤ (a i : ℕ) then
          ∑ k ∈ Finset.range (s + 1),
            ∑ e : ∀ i, Fin ((a i : ℕ) - β i + 1),
              translationScalar m T (fun i => (a i : ℕ)) β (fun i => (e i : ℕ)) error k *
                PowerSeries.coeff (s - k) (formalColumn m B z l (fun i => (a i : ℕ)))
        else 0 := by
  classical
  rw [coeff_formal_translated_product]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hβ : ∀ i, β i ≤ (a i : ℕ)
  · rw [ite_eq_left hβ, ite_eq_left hβ]
    exact translationScalar_convolution m T (fun i => (a i : ℕ)) β error
      (formalColumn m B z l (fun i => (a i : ℕ))) s
  · rw [ite_eq_right hβ, ite_eq_right hβ, mul_zero, map_zero]

end QuadraticField
