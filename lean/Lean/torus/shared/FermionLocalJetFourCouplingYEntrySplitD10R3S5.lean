import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((35120668026123695925 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((8734790591125953075 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((130304188327313893971375 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((32129273909029975108875 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((10571022626956481402775 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((45304767468957477233925 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 10 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((1877147975263643111925 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R3S5 :
    OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (1 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R3S5Row0,
    originalYRowSplitD10R3S5Row1,
    originalYRowSplitD10R3S5Row2,
    originalYRowSplitD10R3S5Row3,
    originalYRowSplitD10R3S5Row4,
    originalYRowSplitD10R3S5Row5,
    originalYRowSplitD10R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
