import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data
import Mathlib.Tactic.Ring
import torus.shared.FermionLocalJetFourCouplingYLookupKernel

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private def packedEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℚ :=
  let (p,j,a) := e
  let (q,l,b) := f
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  if D ≤ T then
    ((a * b * TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.lookupV r D T p j k *
      TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.lookupV s D T q l i *
      (i.factorial : ℤ) * (k.factorial : ℤ) * (t.factorial : ℤ) : ℤ) : ℚ) *
    (2 : ℚ) ^ (1-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)) /
      ((T-D).factorial : ℚ)
  else 0

private theorem lookupEntry_eq_packedEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.lookupEntry D r s t e f = packedEntry D r s t e f := by
  rcases e with ⟨p, j, a⟩
  rcases f with ⟨q, l, b⟩
  unfold TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.lookupEntry packedEntry
  dsimp only
  split_ifs <;> simp only [Int.cast_mul, Int.cast_natCast] <;> ring

private def packedRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => packedEntry D r s row.1 e f)).sum)).sum

private theorem yRow_eq_packedRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    OAI.Laughlin.Certificate.yRow D r s row = packedRow D r s row := by
  rw [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.yRow_eq_lookupRow]
  simp only [TorusLean.Shared.FermionLocalJet.FourCoupling.YLookupKernel.lookupRow, packedRow, lookupEntry_eq_packedEntry]

private theorem originalYRowSplitD13R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((1335042478078717802625 / 16) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-13599883138009654875015 / 65536) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((16230720534056996403395025 / 262144) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((375257473909222583707875 / 65536) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((1217224754604266284158975 / 131072) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-17980048569290024770876125 / 524288) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((189532816747307803313775 / 65536) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

theorem originalYEntrySplitD13R1S9 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S9Row0,
    originalYRowSplitD13R1S9Row1,
    originalYRowSplitD13R1S9Row2,
    originalYRowSplitD13R1S9Row3,
    originalYRowSplitD13R1S9Row4,
    originalYRowSplitD13R1S9Row5,
    originalYRowSplitD13R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
