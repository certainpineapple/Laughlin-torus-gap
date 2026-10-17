import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-73127607268004019856125 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((37378903075656190673625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((8227988021366982714470625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-82056616546430929488710625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((243122868782507058530167125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-67057270651175040474220125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((3944662068494687667001875 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S5 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S5Row0,
    originalYRowSplitD16R3S5Row1,
    originalYRowSplitD16R3S5Row2,
    originalYRowSplitD16R3S5Row3,
    originalYRowSplitD16R3S5Row4,
    originalYRowSplitD16R3S5Row5,
    originalYRowSplitD16R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
