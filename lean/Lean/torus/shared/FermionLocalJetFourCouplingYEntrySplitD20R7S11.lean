import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((8927565923908241675690625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = (-116833799519596112703750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 20 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((32195412694155566480625 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R7S11 :
    OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (5 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (3 : Fin 10) (5 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R7S11Row0,
    originalYRowSplitD20R7S11Row1,
    originalYRowSplitD20R7S11Row2,
    originalYRowSplitD20R7S11Row3,
    originalYRowSplitD20R7S11Row4,
    originalYRowSplitD20R7S11Row5,
    originalYRowSplitD20R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
