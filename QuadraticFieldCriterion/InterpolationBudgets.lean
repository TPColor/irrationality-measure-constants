import QuadraticFieldCriterion.WeightedIndices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! # Degree and derivative budgets for the actual interpolation packets -/

namespace ImaginaryQuadratic

theorem source_degree_budgets {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {w₀ H : ℚ} (hw₀ : 0 < w₀) (ℓ : Fin (m + 1) →₀ ℕ)
    (hℓ : weightedDegree (Fin.cases w₀ w) ℓ ≤ H) :
    (ℓ 0 : ℚ) ≤ H / w₀ ∧ (∑ i, w i * (ℓ i.succ : ℚ)) ≤ H ∧
      ∀ i, ℓ i.succ ≤ ⌊H / w i⌋₊ := by
  have h0 := coordinate_le_weightedDegree (Fin.cases w₀ w)
    (fun i => Fin.cases hw₀.le (fun j => (hw j).le) i) ℓ 0
  simp only [Fin.cases_zero] at h0
  refine ⟨(le_div_iff₀ hw₀).mpr (by nlinarith), ?_, ?_⟩
  · simp only [weightedDegree, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] at hℓ
    have : 0 ≤ w₀ * (ℓ 0 : ℚ) := mul_nonneg hw₀.le (Nat.cast_nonneg _)
    linarith
  · intro i
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    have h := coordinate_le_weightedDegree (Fin.cases w₀ w)
      (fun k => Fin.cases hw₀.le (fun j => (hw j).le) k) ℓ i.succ
    simp only [Fin.cases_succ] at h
    nlinarith

theorem row_degree_budgets {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {v₀ θ H : ℚ} (hv₀ : 0 < v₀) (hθ : 0 < θ) (β : Fin (m + 1) →₀ ℕ)
    (hβ : weightedDegree (Fin.cases v₀ (fun i => w i / θ)) β < H) :
    (β 0 : ℚ) < H / v₀ ∧ (∑ i, w i * (β i.succ : ℚ)) < θ * H := by
  have h0 := coordinate_le_weightedDegree (Fin.cases v₀ (fun i => w i / θ))
    (fun i => Fin.cases hv₀.le (fun j => (div_pos (hw j) hθ).le) i) β 0
  simp only [Fin.cases_zero] at h0
  refine ⟨(lt_div_iff₀ hv₀).mpr (by nlinarith), ?_⟩
  have htail : 0 ≤ v₀ * (β 0 : ℚ) := mul_nonneg hv₀.le (Nat.cast_nonneg _)
  simp only [weightedDegree, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] at hβ
  have heq : (∑ i, (w i / θ) * (β i.succ : ℚ)) =
      (∑ i, w i * (β i.succ : ℚ)) / θ := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hβ
  have h := (div_lt_iff₀ hθ).mp (show (∑ i, w i * (β i.succ : ℚ)) / θ < H by linarith)
  simpa only [mul_comm] using h

theorem transverse_degree_le_of_min_weight {m : ℕ} (w : Fin m → ℚ)
    {H wstar : ℚ} (hwstar : 0 < wstar) (hmin : ∀ i, wstar ≤ w i)
    (ℓ : Fin m → ℕ) (hℓ : (∑ i, w i * (ℓ i : ℚ)) ≤ H) :
    (∑ i, ℓ i : ℕ) ≤ H / wstar := by
  apply (le_div_iff₀ hwstar).mpr
  push_cast
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i, w i * (ℓ i : ℚ) := Finset.sum_le_sum (fun i _ => by
      have h := mul_le_mul_of_nonneg_right (hmin i) (Nat.cast_nonneg (ℓ i) : (0 : ℚ) ≤ ℓ i)
      simpa only [mul_comm] using h)
    _ ≤ H := hℓ

end ImaginaryQuadratic
