import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD4R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((2886685355224401723 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((349902438649926827883 / 4697620480) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-47238680999941252555941 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((5511675478537614088105 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((516864747323349997591 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((21018657195805233353195 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 4 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((2309466974341920987 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD4R1S1 :
    OAI.Laughlin.Certificate.errorRational 4 (0 : Fin 2) (0 : Fin 2) =
      TorusLean.FermionM3.errorTable04 (0 : Fin 2) (0 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 4 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD4R1S1Row0,
    originalYRowSplitD4R1S1Row1,
    originalYRowSplitD4R1S1Row2,
    originalYRowSplitD4R1S1Row3,
    originalYRowSplitD4R1S1Row4,
    originalYRowSplitD4R1S1Row5,
    originalYRowSplitD4R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable04]

#print axioms originalYEntrySplitD4R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
