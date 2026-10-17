import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-11059603545499573939875 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-113390761804695750375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((1563314473231151192677125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2627267336919417273456375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((11400577120718603289883125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-25815284948803585019338125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((2911843890370779366877875 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S11 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S11Row0,
    originalYRowSplitD16R3S11Row1,
    originalYRowSplitD16R3S11Row2,
    originalYRowSplitD16R3S11Row3,
    originalYRowSplitD16R3S11Row4,
    originalYRowSplitD16R3S11Row5,
    originalYRowSplitD16R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
