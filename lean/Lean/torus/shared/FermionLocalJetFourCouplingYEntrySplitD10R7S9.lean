import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((20201208665871498615 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((14490271817712476595 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-61815279332507701572945 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-14925675676095246882645 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-59621983970998101615 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((100784075639678032678875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 10 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-74162917171665613935 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R7S9 :
    OAI.Laughlin.Certificate.errorRational 10 (3 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (3 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R7S9Row0,
    originalYRowSplitD10R7S9Row1,
    originalYRowSplitD10R7S9Row2,
    originalYRowSplitD10R7S9Row3,
    originalYRowSplitD10R7S9Row4,
    originalYRowSplitD10R7S9Row5,
    originalYRowSplitD10R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
