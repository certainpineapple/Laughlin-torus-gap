import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((1007311621973473619775 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((1427939781338291594625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-185184084471164395534575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-778405458809149070720175 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((2082217015546444435574925 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((7332756492002843629569825 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 14 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-41382995429059534610325 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R5S5 :
    OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (2 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R5S5Row0,
    originalYRowSplitD14R5S5Row1,
    originalYRowSplitD14R5S5Row2,
    originalYRowSplitD14R5S5Row3,
    originalYRowSplitD14R5S5Row4,
    originalYRowSplitD14R5S5Row5,
    originalYRowSplitD14R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
