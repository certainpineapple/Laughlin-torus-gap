import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((132329763882597480385725 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((61542164231401869548775 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((41833517670554440867069275 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((227924780284389492252632475 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3786029755432501425544575 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-196737404615822909075640975 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-41995508012920773493875 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S1 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (0 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (0 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S1Row0,
    originalYRowSplitD12R1S1Row1,
    originalYRowSplitD12R1S1Row2,
    originalYRowSplitD12R1S1Row3,
    originalYRowSplitD12R1S1Row4,
    originalYRowSplitD12R1S1Row5,
    originalYRowSplitD12R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
