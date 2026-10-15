import ExternalResults.RepeatedFibres.AdmissibleJetAmpleness
import LogIrrationalityMeasure.Ampleness.BlowupJetSurjectivityComplete

/- Adapted from jdb19937/log-irrationality-measure, commit 09aeeb095cebdce6791e24eff7f16d227edcdcb6. The centres and weights are independent interpolation data. -/

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogIrrationalityMeasure.LogExponent

namespace AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry
open LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry LogExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable (d : InterpolationData)

theorem eventual_jetRestriction_surjective :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  exact eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) (blowupBundle_ample d)

theorem eventually_jetRestriction_surjective :
    ∀ᶠ n in Filter.atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  obtain ⟨N,hN⟩ := eventual_jetRestriction_surjective d
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

end
end AdmissibleJetSurjectivity

end LiuJiangZhang.RepeatedFibres
