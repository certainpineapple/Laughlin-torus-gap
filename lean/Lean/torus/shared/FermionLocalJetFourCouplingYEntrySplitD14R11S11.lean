import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (272131524456662351250 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-5405526661635968175 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-601557301018840775907375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((13150266039151164571725 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((89821193128689693114675 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-369888234510505694556375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 14 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-67516350827838669308475 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R11S11 :
    OAI.Laughlin.Certificate.errorRational 14 (5 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (5 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R11S11Row0,
    originalYRowSplitD14R11S11Row1,
    originalYRowSplitD14R11S11Row2,
    originalYRowSplitD14R11S11Row3,
    originalYRowSplitD14R11S11Row4,
    originalYRowSplitD14R11S11Row5,
    originalYRowSplitD14R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
