import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data
import Mathlib.Tactic.Ring

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
    ((a * b * OAI.Laughlin.Certificate.V r D T p j k *
      OAI.Laughlin.Certificate.V s D T q l i *
      (i.factorial : ℤ) * (k.factorial : ℤ) * (t.factorial : ℤ) : ℤ) : ℚ) *
    (2 : ℚ) ^ (1-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)) /
      ((T-D).factorial : ℚ)
  else 0

private theorem yEntry_eq_packedEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    OAI.Laughlin.Certificate.yEntry D r s t e f = packedEntry D r s t e f := by
  rcases e with ⟨p, j, a⟩
  rcases f with ⟨q, l, b⟩
  unfold OAI.Laughlin.Certificate.yEntry packedEntry
  dsimp only
  split_ifs <;> simp only [Int.cast_mul, Int.cast_natCast] <;> ring

private def packedRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => packedEntry D r s row.1 e f)).sum)).sum

private theorem yRow_eq_packedRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    OAI.Laughlin.Certificate.yRow D r s row = packedRow D r s row := by
  simp only [OAI.Laughlin.Certificate.yRow, packedRow, yEntry_eq_packedEntry]

private theorem originalYRowSplitD13R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-8127659429844800231925 / 64) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-26686307224968057030375 / 131072) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5009180101233996737166975 / 524288) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1198649367086211464106375 / 131072) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2013645613828067556432975 / 524288) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-28819358585975586361295475 / 2097152) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

private theorem originalYRowSplitD13R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((13619714961509569021725 / 16384) : ℚ) := by
  rw [yRow_eq_packedRow]
  decide +kernel

theorem originalYEntrySplitD13R1S7 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S7Row0,
    originalYRowSplitD13R1S7Row1,
    originalYRowSplitD13R1S7Row2,
    originalYRowSplitD13R1S7Row3,
    originalYRowSplitD13R1S7Row4,
    originalYRowSplitD13R1S7Row5,
    originalYRowSplitD13R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
