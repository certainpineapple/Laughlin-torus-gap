import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-100563725700185222475 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((5538622819475576355525 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = (-11471312967139311536250 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((1031304107419226542526625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((19262779855871880893189625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-18212129783465836142925 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R9S13 :
    OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (4 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R9S13Row0,
    originalYRowSplitD17R9S13Row1,
    originalYRowSplitD17R9S13Row2,
    originalYRowSplitD17R9S13Row3,
    originalYRowSplitD17R9S13Row4,
    originalYRowSplitD17R9S13Row5,
    originalYRowSplitD17R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
