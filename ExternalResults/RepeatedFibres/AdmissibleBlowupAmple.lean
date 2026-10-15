import LogIrrationalityMeasure.Ampleness.NumericalAmplenessTheorem
import ExternalResults.RepeatedFibres.AdmissibleCurveDegreeData

/- Adapted from jdb19937/log-irrationality-measure, commit 09aeeb095cebdce6791e24eff7f16d227edcdcb6. The centres and weights are independent interpolation data. -/

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogIrrationalityMeasure.LogExponent

noncomputable section
namespace AdmissibleBlowupGeometry
variable (d : InterpolationData)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end AdmissibleBlowupGeometry

end

end LiuJiangZhang.RepeatedFibres
