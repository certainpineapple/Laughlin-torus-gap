import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((6191530398213090372225 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((10894867941885604953640875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10558437616240267930556625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 18 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-134328942052534512393075 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R9S9 :
    OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (4 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R9S9Row0,
    originalYRowSplitD18R9S9Row1,
    originalYRowSplitD18R9S9Row2,
    originalYRowSplitD18R9S9Row3,
    originalYRowSplitD18R9S9Row4,
    originalYRowSplitD18R9S9Row5,
    originalYRowSplitD18R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
