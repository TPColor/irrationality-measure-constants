import QuadraticFieldCriterion.TranslationBounds

/-! # Exact convolution with the translation scalars -/

namespace QuadraticField

noncomputable def tailSeries (m T : ℕ) : PowerSeries ℂ :=
  timeProjection m (ImaginaryQuadratic.truncatedLog m T - LiuJiangZhang.logOneAdd m)

noncomputable def translationRemainder (m : ℕ) (T a β : Fin m → ℕ)
    (error : Fin m → ℂ) : PowerSeries ℂ :=
  ∏ i, ((a i).choose (β i) : PowerSeries ℂ) *
    (PowerSeries.C (error i) + tailSeries m (T i)) ^ (a i - β i)

theorem translationRemainder_expansion (m : ℕ) (T a β : Fin m → ℕ)
    (error : Fin m → ℂ) :
    translationRemainder m T a β error =
      ∑ e : ∀ i, Fin (a i - β i + 1),
        PowerSeries.C (∏ i, ((a i).choose (β i) : ℂ) *
          ((a i - β i).choose (e i : ℕ) : ℂ) * error i ^ (a i - β i - (e i : ℕ))) *
          ∏ i, tailSeries m (T i) ^ (e i : ℕ) := by
  classical
  have hbinom : ∀ i : Fin m,
      ((a i).choose (β i) : PowerSeries ℂ) *
        (PowerSeries.C (error i) + tailSeries m (T i)) ^ (a i - β i) =
      ∑ e : Fin (a i - β i + 1),
        PowerSeries.C (((a i).choose (β i) : ℂ) *
          ((a i - β i).choose (e : ℕ) : ℂ) * error i ^ (a i - β i - (e : ℕ))) *
          tailSeries m (T i) ^ (e : ℕ) := by
    intro i
    rw [add_comm, add_pow, Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro e he
    simp only [map_mul, map_natCast, map_pow]
    ring
  unfold translationRemainder
  simp_rw [hbinom]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.prod_mul_distrib, map_prod]

theorem coeff_translationRemainder (m : ℕ) (T a β : Fin m → ℕ)
    (error : Fin m → ℂ) (k : ℕ) :
    PowerSeries.coeff k (translationRemainder m T a β error) =
      ∑ e : ∀ i, Fin (a i - β i + 1),
        translationScalar m T a β (fun i => (e i : ℕ)) error k := by
  classical
  rw [translationRemainder_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [PowerSeries.coeff_C_mul]
  unfold translationScalar tailSeries
  congr 1
  simp only [← map_pow, ← map_prod]
  exact coeff_timeProjection m k _

theorem translationScalar_convolution (m : ℕ) (T a β : Fin m → ℕ)
    (error : Fin m → ℂ) (P : PowerSeries ℂ) (s : ℕ) :
    PowerSeries.coeff s (P * translationRemainder m T a β error) =
      ∑ k ∈ Finset.range (s + 1),
        ∑ e : ∀ i, Fin (a i - β i + 1),
          translationScalar m T a β (fun i => (e i : ℕ)) error k *
            PowerSeries.coeff (s - k) P := by
  rw [mul_comm P, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (translationRemainder m T a β error) *
        PowerSeries.coeff j P) s]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_translationRemainder, Finset.sum_mul]

end QuadraticField
