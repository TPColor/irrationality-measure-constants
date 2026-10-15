import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Basic.Complex.Basic

namespace LiuJiangZhang

/-- The formal series `log(1+t)`, independent of the transverse variables. -/
noncomputable def logOneAdd (m : ℕ) : MvPowerSeries (Fin (m + 1)) ℂ := by
  classical
  exact fun α =>
    if α = Finsupp.single 0 (α 0) then
      (-1 : ℂ) ^ (α 0 + 1) / (α 0 : ℂ)
    else 0

end LiuJiangZhang
