import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-29482763785841653245 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((7866895664760765897 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-825991533879872150445 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((58901045380419353591445 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((898662178057610818425 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((100330787491458237454185 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 8 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((139637915427504113235 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R1S7 :
    OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (0 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R1S7Row0,
    originalYRowSplitD8R1S7Row1,
    originalYRowSplitD8R1S7Row2,
    originalYRowSplitD8R1S7Row3,
    originalYRowSplitD8R1S7Row4,
    originalYRowSplitD8R1S7Row5,
    originalYRowSplitD8R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
