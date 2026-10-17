import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-26397741246896856375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-295222383526157425665 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-766290007067055718662945 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-174823312957673502039435 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((32583661087972149603585 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((1328597382760534080701505 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 10 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2085738643055669165235 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R1S9 :
    OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (0 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R1S9Row0,
    originalYRowSplitD10R1S9Row1,
    originalYRowSplitD10R1S9Row2,
    originalYRowSplitD10R1S9Row3,
    originalYRowSplitD10R1S9Row4,
    originalYRowSplitD10R1S9Row5,
    originalYRowSplitD10R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
