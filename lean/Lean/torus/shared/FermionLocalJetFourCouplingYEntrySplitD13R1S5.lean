import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data
import torus.shared.FermionLocalJetFourCouplingYLookupKernel

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((4888482156419812317675 / 16) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((20330373313849105690425 / 262144) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((17842482433576651634751825 / 1048576) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((11159216502097393133031375 / 262144) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4323313703194334274474675 / 1048576) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((135873233088199511072387175 / 4194304) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

private theorem originalYRowSplitD13R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((248883274174277614392675 / 524288) : ℚ) := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  decide +kernel

theorem originalYEntrySplitD13R1S5 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S5Row0,
    originalYRowSplitD13R1S5Row1,
    originalYRowSplitD13R1S5Row2,
    originalYRowSplitD13R1S5Row3,
    originalYRowSplitD13R1S5Row4,
    originalYRowSplitD13R1S5Row5,
    originalYRowSplitD13R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
