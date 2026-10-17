import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((495695314640274709275 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2753397798979091424525 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-7028228890898903730327525 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1859934441446323215290325 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((116225668165423549639725 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((6582793661241188593075425 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-22344180213029099794425 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R1S5 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S5Row0,
    originalYRowSplitD11R1S5Row1,
    originalYRowSplitD11R1S5Row2,
    originalYRowSplitD11R1S5Row3,
    originalYRowSplitD11R1S5Row4,
    originalYRowSplitD11R1S5Row5,
    originalYRowSplitD11R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
