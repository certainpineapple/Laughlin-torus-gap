import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (2458049796363123585 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((16175590011205006941 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((477780451272987533829045 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((104049830962018791216675 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((63913564048297779379305 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-29666914396861622135535 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 9 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((94002280567764198525 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R9S9 :
    OAI.Laughlin.Certificate.errorRational 9 (4 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (4 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R9S9Row0,
    originalYRowSplitD9R9S9Row1,
    originalYRowSplitD9R9S9Row2,
    originalYRowSplitD9R9S9Row3,
    originalYRowSplitD9R9S9Row4,
    originalYRowSplitD9R9S9Row5,
    originalYRowSplitD9R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
