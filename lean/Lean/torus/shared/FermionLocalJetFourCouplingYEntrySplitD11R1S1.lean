import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((20994407544809834608725 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((69189621770018965317075 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-234969207625115450282794725 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-59181641748709812977351625 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-661697527198884786366525 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-102949056149155855706498175 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2783922537275534295775575 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R1S1 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (0 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (0 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S1Row0,
    originalYRowSplitD11R1S1Row1,
    originalYRowSplitD11R1S1Row2,
    originalYRowSplitD11R1S1Row3,
    originalYRowSplitD11R1S1Row4,
    originalYRowSplitD11R1S1Row5,
    originalYRowSplitD11R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable11]


#print axioms originalYEntrySplitD11R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
