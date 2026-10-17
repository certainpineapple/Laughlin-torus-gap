import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((1153158553770801165 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((398875219468930779 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3344728266700356251085 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((2694741498446716664085 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3701247860527868239965 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-111316765905740996833665 / 134217728) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 7 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((21601964370283224165 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R5S7 :
    OAI.Laughlin.Certificate.errorRational 7 (2 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (2 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R5S7Row0,
    originalYRowSplitD7R5S7Row1,
    originalYRowSplitD7R5S7Row2,
    originalYRowSplitD7R5S7Row3,
    originalYRowSplitD7R5S7Row4,
    originalYRowSplitD7R5S7Row5,
    originalYRowSplitD7R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
