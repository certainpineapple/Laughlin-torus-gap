import torus.shared.BosonFiniteCertificateCanonicalRowAssembly
import torus.shared.BosonFiniteCertificateConjugationPair

/-! Orbital-degree conservation kills the omitted channels exactly. This
uses the genuine removal words, not a numeric zero-action table. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

private theorem sum_map_zero {I A : Type*} [AddMonoid A] (l : List I) (f : I → A)
    (h : ∀ a ∈ l, f a = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a (by simp), zero_add]
    exact ih (fun b hb => h b (by simp [hb]))

theorem removalWeight_zero_of_sum_lt (s labels : List ℕ) (h : s.sum < labels.sum) :
    removalWeight s labels = 0 := by
  by_contra hn
  have hn' : wordRemovalWeight s labels ≠ 0 := by
    simpa only [removalWeight_eq_wordRemovalWeight] using hn
  have he := eraseWord_sum_add s labels hn'
  omega

theorem pairRemoval_zero_of_sum_lt (s : List ℕ) (t : ℕ) (h : s.sum < t) :
    pairRemoval s t = 0 := by
  apply sum_map_zero
  intro a ha
  have ha' : a ≤ t := Nat.le_of_lt_succ (List.mem_range.mp ha)
  apply removalWeight_zero_of_sum_lt
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem spectatorPairRemoval_zero_of_sum_lt (s : List ℕ) (p j : ℕ)
    (h : s.sum < p+j) : spectatorPairRemoval s p j = 0 := by
  apply sum_map_zero
  intro a ha
  have ha' : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  apply removalWeight_zero_of_sum_lt
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem frozen_column_degree_bound (t : Fin 4) (p j : ℕ)
    (h : some (p,j) ∈ columns t.val) : t.val ≤ p+j := by
  have ht : t.val ∈ List.range 4 := List.mem_range.mpr t.isLt
  have hw := List.all_eq_true.mp frozenSupport t.val ht
  have hc := List.all_eq_true.mp hw (some (p,j)) h
  change decide (t.val ≤ p+j ∧ p+j ≤ 8 ∧ p+j-t.val ≤ 8) = true at hc
  exact (of_decide_eq_true hc).1

theorem threeRowAction_zero_above_degree (t : Fin 4) (row : List ℤ) (s : List ℕ)
    (h : s.sum < t.val) : threeRowAction t.val row s = 0 := by
  have hz : ∀ term ∈ (columns t.val).zip row,
      term.2 * (match term.1 with
        | none => (pairRemoval s t.val : ℤ)
        | some (p,j) => (spectatorPairRemoval s p j : ℤ)) = 0 := by
    intro term ht
    have hc := (List.of_mem_zip ht).1
    rcases term with ⟨col,c⟩
    cases col with
    | none => simp [pairRemoval_zero_of_sum_lt s t.val h]
    | some pair =>
      rcases pair with ⟨p,j⟩
      have hp := frozen_column_degree_bound t p j hc
      simp [spectatorPairRemoval_zero_of_sum_lt s p j (by omega)]
  have hf (l : List (Option (ℕ × ℕ) × ℤ))
      (hl : ∀ term ∈ l,
        term.2 * (match term.1 with
          | none => (pairRemoval s t.val : ℤ)
          | some (p,j) => (spectatorPairRemoval s p j : ℤ)) = 0) (z : ℤ) :
      l.foldl (fun out term => out + term.2 * (match term.1 with
        | none => (pairRemoval s t.val : ℤ)
        | some (p,j) => (spectatorPairRemoval s p j : ℤ))) z = z := by
    induction l generalizing z with
    | nil => rfl
    | cons a l ih =>
      rw [List.foldl_cons, hl a (by simp), add_zero]
      exact ih (fun b hb => hl b (by simp [hb])) z
  exact hf _ hz 0

/-- A whole channel vanishes when every true row action vanishes on the block. -/
theorem canonicalRowChannel_zero {n r : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (rows : Fin r → List ℤ) (t : ℕ)
    (h : ∀ row a, canonicalFrozenRow9 t row
      (canonicalMonomial (factorialScale 8) (occ a)) = 0) :
    canonicalRowChannel occ rows t = 0 := by
  ext a b
  simp only [canonicalRowChannel, h, ip, occupationInner_zero_left,
    sub_self, Finset.sum_const_zero, Matrix.zero_apply]

/-- Enumerates each original row index once, including original zero and
repeated rows. No added padding rows. -/
def frozenRowCount (t : Fin 4) : ℕ :=
  match t.val with | 0 => 31 | 1 => 37 | 2 => 36 | _ => 34

theorem frozenRowCount_actual : ∀ t : Fin 4,
    frozenRowCount t = (frozenRows t.val).length := by
  intro t
  fin_cases t <;> decide +kernel

def canonicalAllRowChannels {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ)) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ t : Fin 4, canonicalRowChannel occ
    (fun i : Fin (frozenRowCount t) => ((frozenRows t.val)[i.val]?.getD [])) t.val

#print axioms threeRowAction_zero_above_degree
#print axioms canonicalRowChannel_zero
end TorusLean.BosonFiniteCertificate
