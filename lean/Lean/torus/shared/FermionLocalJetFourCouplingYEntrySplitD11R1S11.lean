import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((584094513297858999975 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((8006160187731528843075 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((19018690671280589063440875 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1133784807463304495504775 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((696339590597106106822875 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-4825997977704796419374925 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((69743376462186767599875 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R1S11 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S11Row0,
    originalYRowSplitD11R1S11Row1,
    originalYRowSplitD11R1S11Row2,
    originalYRowSplitD11R1S11Row3,
    originalYRowSplitD11R1S11Row4,
    originalYRowSplitD11R1S11Row5,
    originalYRowSplitD11R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
