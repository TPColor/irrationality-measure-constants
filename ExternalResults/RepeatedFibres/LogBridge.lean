import ExternalResults.LiuJiangZhangLogSeries
import LogIrrationalityMeasure.Jets.FormalLogJet

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure.LogExponent

theorem formalLog_eq_logOneAdd (m : ℕ) : FormalLogJet.formalLog m = logOneAdd m := by
  classical
  ext α
  have htail : α.tail = 0 ↔ α = Finsupp.single 0 (α 0) := by
    constructor
    · intro h
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        have hi := DFunLike.congr_fun h i
        simpa only [Finsupp.tail_apply, Finsupp.zero_apply, Finsupp.single_eq_of_ne
          (Fin.succ_ne_zero i)] using hi
    · intro h
      rw [h]
      ext i
      simp [Finsupp.tail_apply]
  rw [FormalLogJet.formalLog, FormalLogJet.coeff_liftSeries]
  change (if α.tail = 0 then PowerSeries.coeff (α 0) (PowerSeries.log ℂ) else 0) =
    if α = Finsupp.single 0 (α 0) then (-1 : ℂ) ^ (α 0 + 1) / (α 0 : ℂ) else 0
  simp only [htail]
  split_ifs
  · rw [PowerSeries.coeff_log]
    split_ifs with hz
    · simp [hz]
    · push_cast
      rfl
  · rfl

theorem formalJet_eq_eval (m : ℕ) (y : ℂ) (c : Fin m → ℂ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    FormalLogJet.formalJet (Fin.cases y c) P =
      MvPolynomial.eval₂ MvPowerSeries.C
        (Fin.cases (MvPowerSeries.C y * (1 + MvPowerSeries.X 0))
          (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + logOneAdd m)) P := by
  simp only [FormalLogJet.formalJet, Fin.cases_zero, Fin.cases_succ,
    formalLog_eq_logOneAdd]
  rfl

theorem weight_eq_explicit {m : ℕ} (w0 : ℚ) (w : Fin m → ℚ)
    (α : Fin (m + 1) →₀ ℕ) :
    Finsupp.weight (Fin.cases w0 w) α =
      w0 * (α 0 : ℚ) + ∑ i : Fin m, w i * (α i.succ : ℚ) := by
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    nsmul_eq_mul, mul_comm]

end LiuJiangZhang.RepeatedFibres
