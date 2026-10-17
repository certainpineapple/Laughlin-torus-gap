import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((478127345501331804206053125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = (5291667897197854375578375 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-324065607798169927347532875 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S11 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (5 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (5 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S11Row0,
    originalYRowSplitD20R1S11Row1,
    originalYRowSplitD20R1S11Row2,
    originalYRowSplitD20R1S11Row3,
    originalYRowSplitD20R1S11Row4,
    originalYRowSplitD20R1S11Row5,
    originalYRowSplitD20R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
