import ExternalResults.RepeatedFibres.AdmissibleBlowupAmple
import LogIrrationalityMeasure.Ampleness.GlobalBlowupJetSurjectivity

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

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply LogExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end AdmissibleJetSurjectivity

end LiuJiangZhang.RepeatedFibres
