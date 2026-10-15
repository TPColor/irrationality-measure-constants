import QuadraticFieldCriterion.UniformRowExpansion
import QuadraticFieldCriterion.DeterminantExpansion

/-! # Finite row choices for determinant multilinearity -/

namespace QuadraticField

abbrev RowChoice {m : ℕ} (N : Fin m → ℕ) (β : Fin m →₀ ℕ) (s : ℕ) :=
  Σ a : ∀ i, Fin (N i + 1), Fin (s + 1) × (∀ i, Fin ((a i : ℕ) - β i + 1))

theorem card_RowChoice_le {m : ℕ} (N : Fin m → ℕ) (β : Fin m →₀ ℕ) (s : ℕ) :
    Fintype.card (RowChoice N β s) ≤ (s + 1) * (∏ i, (N i + 1)) ^ 2 := by
  classical
  simp only [RowChoice, Fintype.card_sigma, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  calc
    _ ≤ ∑ _a : ∀ i, Fin (N i + 1), (s + 1) * ∏ i, (N i + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Nat.mul_le_mul_left
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      intro i hi
      exact Nat.add_le_add_right ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ (a i).isLt)) 1
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi, Fintype.card_fin,
        Nat.cast_id]
      ring

theorem card_RowChoice_real_le {m : ℕ} (N : Fin m → ℕ) (β : Fin m →₀ ℕ) (s : ℕ)
    (C : ℝ) (hs : (s : ℝ) + 1 ≤ C) (hN : ∀ i, (N i : ℝ) + 1 ≤ C) :
    (Fintype.card (RowChoice N β s) : ℝ) ≤ C ^ (2 * m + 1) := by
  have hC : 0 ≤ C := by have := Nat.cast_nonneg (α := ℝ) s; linarith
  have hprod : (∏ i, ((N i : ℝ) + 1)) ≤ C ^ m := by
    calc
      _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hN i)
      _ = _ := by simp
  have hcard : (Fintype.card (RowChoice N β s) : ℝ) ≤
      ((s : ℝ) + 1) * (∏ i, ((N i : ℝ) + 1)) ^ 2 := by
    exact_mod_cast card_RowChoice_le N β s
  calc
    _ ≤ ((s : ℝ) + 1) * (∏ i, ((N i : ℝ) + 1)) ^ 2 := hcard
    _ ≤ C * (C ^ m) ^ 2 := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hprod 2)
      (by positivity) hC
    _ = C ^ (m * 2 + 1) := by rw [pow_add, pow_mul, pow_one]; ring
    _ = _ := by rw [Nat.mul_comm m 2]

noncomputable def rowChoiceScalar {m : ℕ} (T N : Fin m → ℕ) (β : Fin m →₀ ℕ)
    (s : ℕ) (error : Fin m → ℂ) (r : RowChoice N β s) : ℂ :=
  if ∀ i, β i ≤ (r.1 i : ℕ) then
    translationScalar m T (fun i => (r.1 i : ℕ)) β (fun i => (r.2.2 i : ℕ)) error r.2.1
  else 0

noncomputable def rowChoiceTest {m : ℕ} (N : Fin m → ℕ) (β : Fin m →₀ ℕ)
    (s h j : ℕ) (ω : ℂ) (l : Fin m → ℕ) (r : RowChoice N β s) : ℂ :=
  taylorCoefficient (fun t => columnFunction h l (fun i => (r.1 i : ℕ))
    ((j : ℂ) * ω + Complex.log (1 + t))) (s - (r.2.1 : ℕ)) 0

theorem sum_rowChoices (m h j s : ℕ) (ω : ℂ) (T l N : Fin m → ℕ)
    (β : Fin m →₀ ℕ) (error : Fin m → ℂ) :
    (∑ r : RowChoice N β s, rowChoiceScalar T N β s error r * rowChoiceTest N β s h j ω l r) =
      ∑ a : ∀ i, Fin (N i + 1), rowExpansionTerm m h j s ω T l β error (fun i => (a i : ℕ)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Fintype.sum_prod_type]
  by_cases hβ : ∀ i, β i ≤ (a i : ℕ)
  · simp only [rowChoiceScalar, rowChoiceTest, rowExpansionTerm, ite_eq_left hβ]
    exact Fin.sum_univ_eq_sum_range (fun k =>
      ∑ e : ∀ i, Fin ((a i : ℕ) - β i + 1),
        translationScalar m T (fun i => (a i : ℕ)) β (fun i => (e i : ℕ)) error k *
          taylorCoefficient (fun t => columnFunction h l (fun i => (a i : ℕ))
            ((j : ℂ) * ω + Complex.log (1 + t))) (s - k) 0) (s + 1)
  · simp [rowChoiceScalar, rowExpansionTerm, hβ]

noncomputable def translatedInterpolationEntry (m h j s : ℕ) (ω : ℂ) (T l : Fin m → ℕ)
    (β : Fin m →₀ ℕ) (error : Fin m → ℂ) : ℂ :=
  MvPowerSeries.coeff (β.cons s)
    (((MvPowerSeries.C ((Complex.exp ω) ^ j) * (1 + MvPowerSeries.X 0)) ^ h) *
      ∏ i, (MvPowerSeries.C ((j : ℂ) * ω + error i) + MvPowerSeries.X i.succ +
        ImaginaryQuadratic.truncatedLog m (T i)) ^ l i)

theorem translatedInterpolationEntry_eq_sum (m h j s : ℕ) (ω : ℂ) (T l N : Fin m → ℕ)
    (hN : ∀ i, l i ≤ N i) (β : Fin m →₀ ℕ) (error : Fin m → ℂ) :
    translatedInterpolationEntry m h j s ω T l β error =
      ∑ r : RowChoice N β s, rowChoiceScalar T N β s error r * rowChoiceTest N β s h j ω l r := by
  rw [sum_rowChoices]
  exact uniform_interpolation_row_expansion m h j s ω T l N hN β error

theorem norm_translated_interpolation_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (ω : ℂ) (T N : Fin m → ℕ) (h j s : ι → ℕ)
    (l : ι → Fin m → ℕ) (hN : ∀ c i, l c i ≤ N i)
    (β : ι → Fin m →₀ ℕ) (error : ι → Fin m → ℂ) :
    ‖(Matrix.of (fun r c => translatedInterpolationEntry m (h c) (j r) (s r) ω T (l c) (β r) (error r))).det‖ ≤
      ∑ f : ∀ r, RowChoice N (β r) (s r),
        (∏ r, ‖rowChoiceScalar T N (β r) (s r) (error r) (f r)‖) *
          ‖(Matrix.of (fun r c => rowChoiceTest N (β r) (s r) (h c) (j r) ω (l c) (f r))).det‖ := by
  have heq : Matrix.of (fun r c => translatedInterpolationEntry m (h c) (j r) (s r) ω T (l c) (β r) (error r)) =
      Matrix.of (fun r c => ∑ k : RowChoice N (β r) (s r),
        rowChoiceScalar T N (β r) (s r) (error r) k *
          rowChoiceTest N (β r) (s r) (h c) (j r) ω (l c) k) := by
    ext r c
    exact translatedInterpolationEntry_eq_sum m (h c) (j r) (s r) ω T (l c) N (hN c) (β r) (error r)
  rw [heq]
  exact norm_det_sum_smul_rows_dependent_le _ _

end QuadraticField
