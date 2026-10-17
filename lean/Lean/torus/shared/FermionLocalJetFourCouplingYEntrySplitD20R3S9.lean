import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((105563221968321585158315625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = (-103297060318426975625625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 20 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-29521451733195142536440625 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R3S9 :
    OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (1 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R3S9Row0,
    originalYRowSplitD20R3S9Row1,
    originalYRowSplitD20R3S9Row2,
    originalYRowSplitD20R3S9Row3,
    originalYRowSplitD20R3S9Row4,
    originalYRowSplitD20R3S9Row5,
    originalYRowSplitD20R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
