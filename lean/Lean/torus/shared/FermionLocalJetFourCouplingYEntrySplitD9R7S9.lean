import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((9961370121410598555 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-943210096159456539 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-34554083128289472096315 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((6541691391476980324425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((25873942571301325438305 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-237424338055923605060085 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 9 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-52891986247320188745 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R7S9 :
    OAI.Laughlin.Certificate.errorRational 9 (3 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (3 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R7S9Row0,
    originalYRowSplitD9R7S9Row1,
    originalYRowSplitD9R7S9Row2,
    originalYRowSplitD9R7S9Row3,
    originalYRowSplitD9R7S9Row4,
    originalYRowSplitD9R7S9Row5,
    originalYRowSplitD9R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
