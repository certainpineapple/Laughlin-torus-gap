import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-541873416574187200125 / 512) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-153555584496279495165 / 2097152) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((33950521105803872356912875 / 8388608) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((6581555204884668587502225 / 2097152) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-688755948769240538693175 / 4194304) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((4789963414268027945068275 / 16777216) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

private theorem originalYRowSplitD11R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((19650589108514196447825 / 524288) : ℚ) := by
  unfold OAI.Laughlin.Certificate.yRow OAI.Laughlin.Certificate.yEntry
    OAI.Laughlin.Certificate.V OAI.Laughlin.Certificate.U
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

theorem originalYEntrySplitD11R1S3 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (1 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (1 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S3Row0,
    originalYRowSplitD11R1S3Row1,
    originalYRowSplitD11R1S3Row2,
    originalYRowSplitD11R1S3Row3,
    originalYRowSplitD11R1S3Row4,
    originalYRowSplitD11R1S3Row5,
    originalYRowSplitD11R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
