import ExternalResults.RepeatedFibres.AdmissibleBlowupGeometry
import LogIrrationalityMeasure.Jets.AffineJetFramedPackets

/- Adapted from jdb19937/log-irrationality-measure, commit 09aeeb095cebdce6791e24eff7f16d227edcdcb6. The centres and weights are independent interpolation data. -/

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogIrrationalityMeasure.LogExponent

noncomputable section
namespace AdmissibleJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Geometry
open LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry
open LogExponent.BlowupJetSurjectivity LogExponent.ExceptionalAffineChart
attribute [local irreducible] AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  AdmissibleBlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable (d : InterpolationData)

abbrev affineOpen := chartOpen (affineChart d)

def sectionPolynomial (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) :
    AffineJetCoefficientInterface.Sections (hyperplane d) n → LogExponentApprox.FramePolynomial d.m :=
  AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e

theorem formalPackets_surjective_of_jetRestriction (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (FormalLogJet.formalJet (d.curveCenters j) (sectionPolynomial d n e s))) := by
  have he : ∀ i, (scale d).radius ≤ ((scale d).jetPowers i : ℚ) * d.curveJetWeights i := by
    intro i
    rw [mul_comm, (scale d).jetPowers_eq]
  have hs : (((centerIdeal d)^n).support : Set (compactification d)) ⊆
      (affineChart d).opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart d
  exact AffineJetFramedPackets.surjective_of_jetRestriction d.curveCenters
    d.curveCenters_injective d.curveCenters_zero_ne_zero (logCutoff d) (scale d).jetPowers (scale d).jetPowers_pos
    d.curveJetWeights d.curveJetWeights_pos (fun i => (logCutoff_strict d i).le)
    (scale d).radius he n (affineChart d) (centerIdeal d) (hyperplane d) e
    (centerIdeal_restrict d) hs hjet

end AdmissibleJetPackets
end

end LiuJiangZhang.RepeatedFibres
