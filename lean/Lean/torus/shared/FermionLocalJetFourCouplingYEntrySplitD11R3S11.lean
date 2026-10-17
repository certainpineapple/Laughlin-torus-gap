import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((3730929215018977125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-725731406369701163685 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-175847790417280674380325 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((67401625128542515970775 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((83042778440310945673725 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1624320578377988959631625 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((18043787714062277475 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R3S11 :
    OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (1 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R3S11Row0,
    originalYRowSplitD11R3S11Row1,
    originalYRowSplitD11R3S11Row2,
    originalYRowSplitD11R3S11Row3,
    originalYRowSplitD11R3S11Row4,
    originalYRowSplitD11R3S11Row5,
    originalYRowSplitD11R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
