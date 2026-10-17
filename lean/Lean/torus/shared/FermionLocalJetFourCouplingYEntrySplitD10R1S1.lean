import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1064085542726656177665 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4960322438153586718545 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-7882212971322923996825505 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2774995455156473573112915 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((159158124266644081333395 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-18120514899390017542620255 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 10 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-257395815130267793197575 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R1S1 :
    OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (0 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (0 : Fin 5) (0 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R1S1Row0,
    originalYRowSplitD10R1S1Row1,
    originalYRowSplitD10R1S1Row2,
    originalYRowSplitD10R1S1Row3,
    originalYRowSplitD10R1S1Row4,
    originalYRowSplitD10R1S1Row5,
    originalYRowSplitD10R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
