import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-204557146558589621474803125 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((1065078039970908277689375 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((3334248142683609505234505625 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S9 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S9Row0,
    originalYRowSplitD20R1S9Row1,
    originalYRowSplitD20R1S9Row2,
    originalYRowSplitD20R1S9Row3,
    originalYRowSplitD20R1S9Row4,
    originalYRowSplitD20R1S9Row5,
    originalYRowSplitD20R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
