import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((15951283367184075435525 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((103305738985481186379225 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-129820943743787733111675 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((106390416542676520421492325 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-56873114036247864172442625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((7355639266384853781362025 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S9 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S9Row0,
    originalYRowSplitD17R3S9Row1,
    originalYRowSplitD17R3S9Row2,
    originalYRowSplitD17R3S9Row3,
    originalYRowSplitD17R3S9Row4,
    originalYRowSplitD17R3S9Row5,
    originalYRowSplitD17R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
