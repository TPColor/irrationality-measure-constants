import QuadraticFieldCriterion.ColumnSeries

/-! # Expansion of the actual truncated interpolation entries -/

namespace QuadraticField

theorem timeLift_tailSeries (m T : ℕ) :
    timeLift m (tailSeries m T) =
      ImaginaryQuadratic.truncatedLog m T - LiuJiangZhang.logOneAdd m := by
  change timeLift m (timeProjection m (ImaginaryQuadratic.truncatedLog m T -
    LiuJiangZhang.logOneAdd m)) = _
  rw [map_sub, map_sub, timeLift_truncatedLog]
  rw [show timeLift m (timeProjection m (LiuJiangZhang.logOneAdd m)) =
    LiuJiangZhang.logOneAdd m from timeLift_logarithmSeries m]

theorem interpolation_row_expansion (m h j s : ℕ) (ω : ℂ) (T l : Fin m → ℕ)
    (β : Fin m →₀ ℕ) (error : Fin m → ℂ) :
    MvPowerSeries.coeff (β.cons s)
      (((MvPowerSeries.C ((Complex.exp ω) ^ j) * (1 + MvPowerSeries.X 0)) ^ h) *
        ∏ i, (MvPowerSeries.C ((j : ℂ) * ω + error i) + MvPowerSeries.X i.succ +
          ImaginaryQuadratic.truncatedLog m (T i)) ^ l i) =
      ∑ a : ∀ i, Fin (l i + 1),
        if ∀ i, β i ≤ (a i : ℕ) then
          ∑ k ∈ Finset.range (s + 1),
            ∑ e : ∀ i, Fin ((a i : ℕ) - β i + 1),
              translationScalar m T (fun i => (a i : ℕ)) β (fun i => (e i : ℕ)) error k *
                taylorCoefficient (fun t => columnFunction h l (fun i => (a i : ℕ))
                  ((j : ℂ) * ω + Complex.log (1 + t))) (s - k) 0
        else 0 := by
  classical
  let B : PowerSeries ℂ := PowerSeries.C ((Complex.exp ω) ^ (j * h)) * (1 + PowerSeries.X) ^ h
  let z : PowerSeries ℂ := PowerSeries.C ((j : ℂ) * ω) + logarithmSeries m
  have hC : ∀ c : ℂ, timeLift m (PowerSeries.C c) = MvPowerSeries.C c := fun c =>
    MvPowerSeries.rename_C (timeEmbedding m) c
  have hX : timeLift m PowerSeries.X = MvPowerSeries.X 0 :=
    MvPowerSeries.rename_X (timeEmbedding m) ()
  have hB : timeLift m B =
      (MvPowerSeries.C ((Complex.exp ω) ^ j) * (1 + MvPowerSeries.X 0)) ^ h := by
    simp only [B, map_mul, map_pow, map_add, map_one, hC, hX, mul_pow, pow_mul]
  have hz : ∀ i : Fin m,
      MvPowerSeries.X i.succ + timeLift m (z + (PowerSeries.C (error i) + tailSeries m (T i))) =
      MvPowerSeries.C ((j : ℂ) * ω + error i) + MvPowerSeries.X i.succ +
        ImaginaryQuadratic.truncatedLog m (T i) := by
    intro i
    simp only [z, map_add, timeLift_logarithmSeries, timeLift_tailSeries]
    rw [hC, hC]
    ring
  rw [← hB]
  simp_rw [← hz]
  rw [formal_row_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hβ : ∀ i, β i ≤ (a i : ℕ)
  · rw [ite_eq_left hβ, ite_eq_left hβ]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro e he
    rw [show formalColumn m B z l (fun i => (a i : ℕ)) =
      columnSeries m h j ω l (fun i => (a i : ℕ)) from rfl,
      coeff_columnSeries m h j (s - k) ω l (fun i => (a i : ℕ))
        (fun i => Nat.le_of_lt_succ (a i).isLt)]
  · rw [ite_eq_right hβ, ite_eq_right hβ]

end QuadraticField
