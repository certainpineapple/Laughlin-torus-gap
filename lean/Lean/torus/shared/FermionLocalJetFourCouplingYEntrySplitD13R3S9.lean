import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((415022167461084502725 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((1622028842159159585385 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((980234032756767009156225 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((337791490566897117030525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-358361571283202281721625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((674195962213956147576975 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((11095634707054355081925 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S9 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S9Row0,
    originalYRowSplitD13R3S9Row1,
    originalYRowSplitD13R3S9Row2,
    originalYRowSplitD13R3S9Row3,
    originalYRowSplitD13R3S9Row4,
    originalYRowSplitD13R3S9Row5,
    originalYRowSplitD13R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
