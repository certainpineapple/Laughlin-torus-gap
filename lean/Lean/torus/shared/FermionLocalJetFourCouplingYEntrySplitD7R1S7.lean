import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((15514482988745341335 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((34459028886161906571 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((207794480500460556638835 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-12487246647748499348535 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((20867558445854020401465 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-87026179675834894580205 / 134217728) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 7 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((201099333031028464725 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R1S7 :
    OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (0 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R1S7Row0,
    originalYRowSplitD7R1S7Row1,
    originalYRowSplitD7R1S7Row2,
    originalYRowSplitD7R1S7Row3,
    originalYRowSplitD7R1S7Row4,
    originalYRowSplitD7R1S7Row5,
    originalYRowSplitD7R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
