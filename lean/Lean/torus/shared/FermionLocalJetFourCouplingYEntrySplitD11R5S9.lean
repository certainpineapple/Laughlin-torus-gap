import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((7837270590707052075 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((39040613334124060275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-243182181678200114113125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((12985041753307269004275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((3930794664554657695725 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2632324418326141063875 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 11 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((1812399811964662587975 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R5S9 :
    OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (2 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R5S9Row0,
    originalYRowSplitD11R5S9Row1,
    originalYRowSplitD11R5S9Row2,
    originalYRowSplitD11R5S9Row3,
    originalYRowSplitD11R5S9Row4,
    originalYRowSplitD11R5S9Row5,
    originalYRowSplitD11R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
