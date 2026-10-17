import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((437784044915790948375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-175620793000405027275 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-10041209220719772635965425 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-44038505928995884903471875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-51865434669123050037036975 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((101905244894152379352848175 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((23722603227468659090201625 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S7 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S7Row0,
    originalYRowSplitD16R3S7Row1,
    originalYRowSplitD16R3S7Row2,
    originalYRowSplitD16R3S7Row3,
    originalYRowSplitD16R3S7Row4,
    originalYRowSplitD16R3S7Row5,
    originalYRowSplitD16R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
