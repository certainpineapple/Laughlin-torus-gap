import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((4682620406118861576995625 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-26993617218782413900147321875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((13623199714735988897446801875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-779293929331588057470208125 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S5 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S5Row0,
    originalYRowSplitD18R3S5Row1,
    originalYRowSplitD18R3S5Row2,
    originalYRowSplitD18R3S5Row3,
    originalYRowSplitD18R3S5Row4,
    originalYRowSplitD18R3S5Row5,
    originalYRowSplitD18R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
