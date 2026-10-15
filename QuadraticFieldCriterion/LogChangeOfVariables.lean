import QuadraticFieldCriterion.WeightedPackets
import QuadraticFieldCriterion.LogTruncation

namespace ImaginaryQuadratic

theorem weightedDegree_single {σ : Type*} [Fintype σ] (v : σ → ℚ)
    (i : σ) (n : ℕ) : weightedDegree v (Finsupp.single i n) = v i * n := by
  classical
  simp [weightedDegree, Finsupp.single_apply]

theorem vanishesBelow_X {σ : Type*} [Fintype σ] (v : σ → ℚ) (i : σ) :
    VanishesBelow v (v i) (MvPowerSeries.X i : MvPowerSeries σ ℂ) := by
  classical
  intro α hα
  rw [MvPowerSeries.coeff_X]
  apply ite_eq_right
  intro h
  rw [h, weightedDegree_single, Nat.cast_one, mul_one] at hα
  exact lt_irrefl _ hα

/-- The logarithm tail is a series in `t` only. -/
theorem logTail_support {m T : ℕ} (α : Fin (m + 1) →₀ ℕ)
    (hα : MvPowerSeries.coeff α
      (truncatedLog m T - LiuJiangZhang.logOneAdd m) ≠ 0) :
    α = Finsupp.single 0 (α 0) := by
  by_contra h
  apply hα
  change truncatedLog m T α - LiuJiangZhang.logOneAdd m α = 0
  simp [truncatedLog, LiuJiangZhang.logOneAdd, h]

theorem logTail_constantCoeff (m T : ℕ) :
    MvPowerSeries.constantCoeff
      (truncatedLog m T - LiuJiangZhang.logOneAdd m) = 0 := by
  change truncatedLog m T 0 - LiuJiangZhang.logOneAdd m 0 = 0
  simp [truncatedLog, LiuJiangZhang.logOneAdd]

noncomputable def logShift (m : ℕ) (T : Fin m → ℕ) :
    Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
  Fin.cases (MvPowerSeries.X 0) (fun i => MvPowerSeries.X i.succ +
    (truncatedLog m (T i) - LiuJiangZhang.logOneAdd m))

noncomputable def inverseLogShift (m : ℕ) (T : Fin m → ℕ) :
    Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
  Fin.cases (MvPowerSeries.X 0) (fun i => MvPowerSeries.X i.succ -
    (truncatedLog m (T i) - LiuJiangZhang.logOneAdd m))

theorem logShift_hasSubst (m : ℕ) (T : Fin m → ℕ) :
    MvPowerSeries.HasSubst (logShift m T) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [logShift]
  · simp [logShift, logTail_constantCoeff]

theorem inverseLogShift_hasSubst (m : ℕ) (T : Fin m → ℕ) :
    MvPowerSeries.HasSubst (inverseLogShift m T) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [inverseLogShift]
  · simp [inverseLogShift, logTail_constantCoeff]

theorem subst_logTail_of_fixed_t {m : ℕ}
    {a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ}
    (ha : MvPowerSeries.HasSubst a) (ha0 : a 0 = MvPowerSeries.X 0) (T : ℕ) :
    MvPowerSeries.subst a (truncatedLog m T - LiuJiangZhang.logOneAdd m) =
      truncatedLog m T - LiuJiangZhang.logOneAdd m := by
  apply subst_eq_of_fixed_support ha
  intro α hα i hi
  have hsupport := logTail_support α hα
  by_cases hi0 : i = 0
  · simpa [hi0] using ha0
  · have hz : α i = 0 := by rw [hsupport]; simp [hi0]
    exact False.elim ((Finsupp.mem_support_iff.mp hi) hz)

/-- The two triangular substitutions are inverse on the full series ring. -/
theorem logShift_inverse (m : ℕ) (T : Fin m → ℕ)
    (f : MvPowerSeries (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst (logShift m T)
      (MvPowerSeries.subst (inverseLogShift m T) f) = f := by
  rw [MvPowerSeries.subst_comp_subst_apply
    (inverseLogShift_hasSubst m T) (logShift_hasSubst m T)]
  have hvars : (fun i => MvPowerSeries.subst (logShift m T) (inverseLogShift m T i)) =
      MvPowerSeries.X := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [inverseLogShift, MvPowerSeries.subst_X (logShift_hasSubst m T), logShift]
    · simp only [inverseLogShift, Fin.cases_succ]
      rw [MvPowerSeries.subst_sub (logShift_hasSubst m T),
        MvPowerSeries.subst_X (logShift_hasSubst m T),
        subst_logTail_of_fixed_t (logShift_hasSubst m T) (by simp [logShift])]
      simp [logShift]
  rw [hvars]
  exact congrFun (MvPowerSeries.subst_self (R := ℂ)) f

/-- The ceiling orders in the manuscript make the change of variables filtered. -/
theorem logShift_filtered {m : ℕ} (v : Fin (m + 1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (T : Fin m → ℕ)
    (hT : ∀ i, v i.succ ≤ v 0 * (T i : ℚ)) :
    ∀ i, VanishesBelow v (v i) (logShift m T i) := by
  intro i
  refine Fin.cases (vanishesBelow_X v 0) (fun i => ?_) i
  apply (vanishesBelow_X v i.succ).add
  intro α hα
  exact logTail_coeff_eq_zero_of_weight v hv (v i.succ) (hT i) α hα

theorem subst_logOneAdd_of_fixed_t {m : ℕ}
    {a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ}
    (ha : MvPowerSeries.HasSubst a) (ha0 : a 0 = MvPowerSeries.X 0) :
    MvPowerSeries.subst a (LiuJiangZhang.logOneAdd m) = LiuJiangZhang.logOneAdd m := by
  apply subst_eq_of_fixed_support ha
  intro α hα i hi
  have hs : α = Finsupp.single 0 (α 0) := by
    by_contra h
    apply hα
    change LiuJiangZhang.logOneAdd m α = 0
    simp [LiuJiangZhang.logOneAdd, h]
  by_cases hi0 : i = 0
  · simpa [hi0] using ha0
  · have hz : α i = 0 := by rw [hs]; simp [hi0]
    exact False.elim ((Finsupp.mem_support_iff.mp hi) hz)

end ImaginaryQuadratic
