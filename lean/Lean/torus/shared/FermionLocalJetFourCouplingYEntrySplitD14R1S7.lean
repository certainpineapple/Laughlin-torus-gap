import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((43089143813220230700975 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((85827466556633820543525 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5940625711251852968522175 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-33863998004220622641428025 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3697357865718312580259475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-48670197575865710076557325 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1084561830452212761223575 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S7 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S7Row0,
    originalYRowSplitD14R1S7Row1,
    originalYRowSplitD14R1S7Row2,
    originalYRowSplitD14R1S7Row3,
    originalYRowSplitD14R1S7Row4,
    originalYRowSplitD14R1S7Row5,
    originalYRowSplitD14R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
