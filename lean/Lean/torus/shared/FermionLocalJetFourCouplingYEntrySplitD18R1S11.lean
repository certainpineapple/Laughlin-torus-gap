import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-74238821976349806628978125 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-672627855262357677975917625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((7322326890665278272113458125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((198059253393546032445082125 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S11 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S11Row0,
    originalYRowSplitD18R1S11Row1,
    originalYRowSplitD18R1S11Row2,
    originalYRowSplitD18R1S11Row3,
    originalYRowSplitD18R1S11Row4,
    originalYRowSplitD18R1S11Row5,
    originalYRowSplitD18R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
