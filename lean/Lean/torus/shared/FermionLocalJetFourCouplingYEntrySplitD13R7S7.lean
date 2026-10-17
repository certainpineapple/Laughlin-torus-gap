import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-91519790205628031625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((450293822935471052325 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-61417749280649998175775 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-16429341900708450036225 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((171563815329656146510725 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2466681719776702842568725 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 13 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-347904380745188005725 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R7S7 :
    OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (3 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R7S7Row0,
    originalYRowSplitD13R7S7Row1,
    originalYRowSplitD13R7S7Row2,
    originalYRowSplitD13R7S7Row3,
    originalYRowSplitD13R7S7Row4,
    originalYRowSplitD13R7S7Row5,
    originalYRowSplitD13R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
