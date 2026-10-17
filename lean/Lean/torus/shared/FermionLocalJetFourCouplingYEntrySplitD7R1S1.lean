import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((7813395192175504245 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((36323988982144322139 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((56489461722547816265955 / 268435456) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-181450975756044921243195 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2508628320709374018255 / 29360128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((1591029590813751708821385 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 7 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-4276885373741756719485 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R1S1 :
    OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (0 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (0 : Fin 4) (0 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R1S1Row0,
    originalYRowSplitD7R1S1Row1,
    originalYRowSplitD7R1S1Row2,
    originalYRowSplitD7R1S1Row3,
    originalYRowSplitD7R1S1Row4,
    originalYRowSplitD7R1S1Row5,
    originalYRowSplitD7R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
