import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((205314913297683315 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2180568515710116549 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((50011870045872224797155 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((126559883614713029393025 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-46679206856806148273295 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((486363383031076447124835 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 7 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-620279821822140423225 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R1S5 :
    OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (0 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R1S5Row0,
    originalYRowSplitD7R1S5Row1,
    originalYRowSplitD7R1S5Row2,
    originalYRowSplitD7R1S5Row3,
    originalYRowSplitD7R1S5Row4,
    originalYRowSplitD7R1S5Row5,
    originalYRowSplitD7R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
