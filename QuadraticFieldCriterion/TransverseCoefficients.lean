import QuadraticFieldCriterion.TaylorSeriesBridge
import QuadraticFieldCriterion.PolynomialTranslation

/-! # Separating the time coefficient from the transverse coefficient -/

namespace QuadraticField

noncomputable def timeLift (m : ℕ) : PowerSeries ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPowerSeries.rename (timeEmbedding m)

theorem coeff_timeLift (m s : ℕ) (β : Fin m →₀ ℕ) (P : PowerSeries ℂ) :
    MvPowerSeries.coeff (β.cons s) (timeLift m P) =
      if β = 0 then PowerSeries.coeff s P else 0 := by
  classical
  by_cases hβ : β = 0
  · subst β
    rw [ite_eq_left rfl, Finsupp.cons_zero_eq_single_zero]
    change MvPowerSeries.coeff (Finsupp.single 0 s)
      (MvPowerSeries.rename (timeEmbedding m) P) = _
    have h : Finsupp.embDomain (timeEmbedding m) (Finsupp.single () s) = Finsupp.single 0 s := by
      rw [Finsupp.embDomain_single]; rfl
    rw [← h, MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right hβ]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨a, ha⟩
    apply hβ
    ext i
    have hi := congrArg (fun x : Fin (m + 1) →₀ ℕ => x i.succ) ha
    have hn : i.succ ∉ Set.range (timeEmbedding m) := by
      rintro ⟨x, hx⟩
      exact Fin.succ_ne_zero i hx.symm
    rw [Finsupp.mapDomain_of_notMem_range a _ hn, Finsupp.cons_succ] at hi
    exact hi.symm

theorem timeLift_timeProjection_of_support (m : ℕ) (P : MvPowerSeries (Fin (m + 1)) ℂ)
    (hP : ∀ n, n ≠ Finsupp.single 0 (n 0) → MvPowerSeries.coeff n P = 0) :
    timeLift m (timeProjection m P) = P := by
  classical
  ext n
  rw [← Finsupp.cons_tail n, coeff_timeLift]
  by_cases ht : n.tail = 0
  · rw [ite_eq_left ht, coeff_timeProjection, ht, Finsupp.cons_zero_eq_single_zero]
  · rw [ite_eq_right ht]
    symm
    apply hP
    intro heq
    apply ht
    have h := (Finsupp.cons_eq_single_zero_iff).mp heq
    exact h.1

theorem timeLift_logarithmSeries (m : ℕ) :
    timeLift m (logarithmSeries m) = LiuJiangZhang.logOneAdd m := by
  apply timeLift_timeProjection_of_support
  intro n hn
  simp [LiuJiangZhang.logOneAdd, MvPowerSeries.coeff_apply, hn]

theorem timeLift_truncatedLog (m T : ℕ) :
    timeLift m (timeProjection m (ImaginaryQuadratic.truncatedLog m T)) =
      ImaginaryQuadratic.truncatedLog m T := by
  apply timeLift_timeProjection_of_support
  intro n hn
  simp [ImaginaryQuadratic.truncatedLog, LiuJiangZhang.logOneAdd, MvPowerSeries.coeff_apply, hn]

theorem coeff_timeLift_mul_transverse_monomial (m s : ℕ) (β a : Fin m →₀ ℕ)
    (P : PowerSeries ℂ) :
    MvPowerSeries.coeff (β.cons s)
      (timeLift m P * MvPowerSeries.monomial (a.cons 0) 1) =
      if a = β then PowerSeries.coeff s P else 0 := by
  classical
  rw [MvPowerSeries.coeff_mul_monomial]
  by_cases hab : a ≤ β
  · have hcons : a.cons 0 ≤ β.cons s := by
      intro i
      exact Fin.cases (Nat.zero_le s) (fun i => hab i) i
    rw [ite_eq_left hcons, mul_one]
    have hsub : β.cons s - a.cons 0 = (β - a).cons s := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [hsub, coeff_timeLift]
    by_cases heq : a = β
    · subst a; simp
    · rw [ite_eq_right heq, ite_eq_right]
      intro h
      exact heq (le_antisymm hab (tsub_eq_zero_iff_le.mp h))
  · rw [ite_eq_right, ite_eq_right]
    · intro h; exact hab (h.le)
    · intro h
      apply hab
      intro i
      exact h i.succ

noncomputable def transversePolynomialLift (m : ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.eval₂Hom (timeLift m).toRingHom (fun i => MvPowerSeries.X i.succ)

theorem prod_transverse_X (m : ℕ) (a : Fin m →₀ ℕ) :
    (∏ i, (MvPowerSeries.X i.succ : MvPowerSeries (Fin (m + 1)) ℂ) ^ a i) =
      MvPowerSeries.monomial (a.cons 0) 1 := by
  classical
  simp only [MvPowerSeries.X_pow_eq]
  rw [MvPowerSeries.prod_monomial]
  simp only [Finset.prod_const_one]
  have hsum : (∑ i : Fin m, Finsupp.single i.succ (a i)) = a.cons 0 := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [Finsupp.single_apply, Fin.succ_inj]
  rw [hsum]

theorem transversePolynomialLift_monomial (m : ℕ) (a : Fin m →₀ ℕ) (P : PowerSeries ℂ) :
    transversePolynomialLift m (MvPolynomial.monomial a P) =
      timeLift m P * MvPowerSeries.monomial (a.cons 0) 1 := by
  rw [transversePolynomialLift, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), prod_transverse_X]
  rfl

theorem coeff_transversePolynomialLift (m s : ℕ) (β : Fin m →₀ ℕ)
    (P : MvPolynomial (Fin m) (PowerSeries ℂ)) :
    MvPowerSeries.coeff (β.cons s) (transversePolynomialLift m P) =
      PowerSeries.coeff s (P.coeff β) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | monomial a P =>
    rw [transversePolynomialLift_monomial, coeff_timeLift_mul_transverse_monomial,
      MvPolynomial.coeff_monomial]
    split_ifs <;> simp

theorem coeff_formal_translated_product (m s : ℕ) (β : Fin m →₀ ℕ)
    (B z : PowerSeries ℂ) (l : Fin m → ℕ) (d : Fin m → PowerSeries ℂ) :
    MvPowerSeries.coeff (β.cons s)
      (timeLift m B * ∏ i, (MvPowerSeries.X i.succ + timeLift m (z + d i)) ^ l i) =
      ∑ a : ∀ i, Fin (l i + 1), PowerSeries.coeff s
        ((B * (∏ i, ((l i).choose (a i : ℕ) : PowerSeries ℂ)) *
          z ^ (∑ i, (l i - (a i : ℕ)))) *
          (if ∀ i, β i ≤ (a i : ℕ) then
            ∏ i, ((a i : ℕ).choose (β i) : PowerSeries ℂ) *
              d i ^ ((a i : ℕ) - β i) else 0)) := by
  classical
  let P : MvPolynomial (Fin m) (PowerSeries ℂ) :=
    MvPolynomial.C B * ∏ i, (MvPolynomial.X i + MvPolynomial.C (z + d i)) ^ l i
  have h := coeff_transversePolynomialLift m s β P
  have hl : transversePolynomialLift m P =
      timeLift m B * ∏ i, (MvPowerSeries.X i.succ + timeLift m (z + d i)) ^ l i := by
    simp [P, transversePolynomialLift]
  rw [hl] at h
  rw [h]
  simp only [P, coeff_translated_product, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> rfl

end QuadraticField
