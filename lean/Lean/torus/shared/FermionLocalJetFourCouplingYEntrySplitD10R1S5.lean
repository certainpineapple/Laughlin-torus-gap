import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-210377412998448883425 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-128313696897982722825 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1149868753797848820869025 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-331678844001432780468975 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-50494813558154091624375 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2240052376445141599373175 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 10 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6580335615497095641525 / 2097152) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R1S5 :
    OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (0 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R1S5Row0,
    originalYRowSplitD10R1S5Row1,
    originalYRowSplitD10R1S5Row2,
    originalYRowSplitD10R1S5Row3,
    originalYRowSplitD10R1S5Row4,
    originalYRowSplitD10R1S5Row5,
    originalYRowSplitD10R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
