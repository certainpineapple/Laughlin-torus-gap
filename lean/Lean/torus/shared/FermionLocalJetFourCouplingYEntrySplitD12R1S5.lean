import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-2502849956226553031175 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((621914142952153777275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-7485185792391888758559525 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3058826694503181605415225 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((6731373725489957749425 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((1588571896113055450651725 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-62778683101346543660175 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S5 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S5Row0,
    originalYRowSplitD12R1S5Row1,
    originalYRowSplitD12R1S5Row2,
    originalYRowSplitD12R1S5Row3,
    originalYRowSplitD12R1S5Row4,
    originalYRowSplitD12R1S5Row5,
    originalYRowSplitD12R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
