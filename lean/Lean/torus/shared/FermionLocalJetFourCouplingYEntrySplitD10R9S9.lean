import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((12032941126440706605 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((6708224048148534735 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((224087039114989893318495 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((96296610744895800972285 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((18357587065295053415505 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-22834373043545399166075 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 10 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-351552712935152887515 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R9S9 :
    OAI.Laughlin.Certificate.errorRational 10 (4 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (4 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R9S9Row0,
    originalYRowSplitD10R9S9Row1,
    originalYRowSplitD10R9S9Row2,
    originalYRowSplitD10R9S9Row3,
    originalYRowSplitD10R9S9Row4,
    originalYRowSplitD10R9S9Row5,
    originalYRowSplitD10R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
