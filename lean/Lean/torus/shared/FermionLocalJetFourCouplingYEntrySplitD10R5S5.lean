import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-11719300320456956775 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((15532599784213655775 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-55278338527762369992225 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-4975185288184465801275 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((176275251040806032585175 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((77527734553117605762675 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 10 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1370467984389834881025 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R5S5 :
    OAI.Laughlin.Certificate.errorRational 10 (2 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (2 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R5S5Row0,
    originalYRowSplitD10R5S5Row1,
    originalYRowSplitD10R5S5Row2,
    originalYRowSplitD10R5S5Row3,
    originalYRowSplitD10R5S5Row4,
    originalYRowSplitD10R5S5Row5,
    originalYRowSplitD10R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
