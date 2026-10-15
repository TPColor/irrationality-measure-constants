import QuadraticFieldCriterion.FormalRowExpansion

/-! # The formal column series represents the analytic column tests -/

namespace QuadraticField

noncomputable def columnSeries (m h j : ℕ) (ω : ℂ) (l a : Fin m → ℕ) : PowerSeries ℂ :=
  formalColumn m (PowerSeries.C ((Complex.exp ω) ^ (j * h)) * (1 + PowerSeries.X) ^ h)
    (PowerSeries.C ((j : ℂ) * ω) + logarithmSeries m) l a

theorem column_curve_hasTaylorSeries (m h j : ℕ) (ω : ℂ) (l a : Fin m → ℕ)
    (ha : ∀ i, a i ≤ l i) :
    HasTaylorSeries (fun t => columnFunction h l a ((j : ℂ) * ω + Complex.log (1 + t)))
      (columnSeries m h j ω l a) := by
  have hB := (HasTaylorSeries.const ((Complex.exp ω) ^ (j * h))).mul
    (((HasTaylorSeries.const 1).add HasTaylorSeries.id).pow h)
  have hZ := (HasTaylorSeries.const ((j : ℂ) * ω)).add (logarithm_hasTaylorSeries m)
  have hpack := (hB.mul (HasTaylorSeries.const ((∏ i, (l i).choose (a i) : ℕ) : ℂ))).mul
    (hZ.pow (∑ i, (l i - a i)))
  have hseries : (PowerSeries.C ((Complex.exp ω) ^ (j * h)) *
      (PowerSeries.C 1 + PowerSeries.X) ^ h *
      PowerSeries.C ((∏ i, (l i).choose (a i) : ℕ) : ℂ)) *
      (PowerSeries.C ((j : ℂ) * ω) + logarithmSeries m) ^ (∑ i, (l i - a i)) =
      columnSeries m h j ω l a := by
    simp only [columnSeries, formalColumn, map_one, Nat.cast_prod, map_prod, map_natCast]
  rw [hseries] at hpack
  apply hpack.congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
  have ht' : ‖t‖ ≤ 1 / 2 := by
    have := Metric.mem_ball.mp ht
    simpa only [dist_zero_right] using this.le
  rw [columnFunction, ite_eq_left ha, entireMonomial, Complex.exp_nat_mul,
    exponential_log_curve ω j ht', mul_pow, ← pow_mul]
  ring

theorem coeff_columnSeries (m h j k : ℕ) (ω : ℂ) (l a : Fin m → ℕ)
    (ha : ∀ i, a i ≤ l i) :
    PowerSeries.coeff k (columnSeries m h j ω l a) =
      taylorCoefficient (fun t => columnFunction h l a ((j : ℂ) * ω + Complex.log (1 + t))) k 0 :=
  ((column_curve_hasTaylorSeries m h j ω l a ha).coeff_eq k).symm

end QuadraticField
