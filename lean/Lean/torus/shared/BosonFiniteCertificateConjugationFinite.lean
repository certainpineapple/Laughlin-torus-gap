import torus.shared.BosonFiniteCertificateConjugation

/-! Exact finite-label transport of the real frozen polynomial operators.
The modulo map below is only used under explicit label bounds. Its forward
embedding into Nat is proved to intertwine the actual derivative words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.BosonFiniteCertificate

variable {K : Type*} [Field K]

def fin9 (j : ℕ) : Fin 9 := ⟨j % 9, Nat.mod_lt _ (by decide)⟩

def sourceLabelsBounded9 (s : List ℕ) : Bool := s.all (fun j => decide (j < 9))

def wordLabelsBounded9 (creators annihilators : List ℕ) : Bool :=
  sourceLabelsBounded9 (creators ++ annihilators)

def columnLabelsBounded9 (t : ℕ) (col : Option (ℕ × ℕ)) : Bool :=
  match col with
  | none => (List.range (t+1)).all fun a => wordLabelsBounded9 [] [a,t-a]
  | some (p,j) => (List.range (p+1)).all fun a =>
      wordLabelsBounded9 [p+j-t] [j,a,p-a]

def rowLabelsBounded9 (t : ℕ) : Bool :=
  (columns t).all (columnLabelsBounded9 t)

theorem map_fin9_val (s : List ℕ) (h : sourceLabelsBounded9 s = true) :
    (s.map fin9).map Fin.val = s := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro j hj
  exact Nat.mod_eq_of_lt (of_decide_eq_true (List.all_eq_true.mp h j hj))

theorem rename_fin9_word (s : List ℕ) (h : sourceLabelsBounded9 s = true) :
    MvPolynomial.rename Fin.val (wordPolynomial (s.map fin9) : Core (Fin 9) K) =
      wordPolynomial s := by
  rw [rename_wordPolynomial, map_fin9_val s h]

theorem rename_fin9_normalWord (creators annihilators : List ℕ)
    (h : wordLabelsBounded9 creators annihilators = true) (p : Core (Fin 9) K) :
    MvPolynomial.rename Fin.val
      (normalWord (creators.map fin9) (annihilators.map fin9) p) =
      normalWord creators annihilators (MvPolynomial.rename Fin.val p) := by
  have hh : sourceLabelsBounded9 creators = true ∧
      sourceLabelsBounded9 annihilators = true := by
    simpa only [wordLabelsBounded9, sourceLabelsBounded9, List.all_append,
      Bool.and_eq_true] using h
  rw [← normalWord_rename Fin.val Fin.val_injective,
    map_fin9_val creators hh.1, map_fin9_val annihilators hh.2]

/-- A genuine finite sum of differential words, not an operator reconstructed
from a finite action table. Bounds are required only by the transport theorem. -/
def finitePaperColumn9 (t : ℕ) (col : Option (ℕ × ℕ)) :
    Core (Fin 9) K →ₗ[K] Core (Fin 9) K :=
  match col with
  | none => ((List.range (t+1)).map fun a =>
      normalWord ([] : List (Fin 9)) ([a,t-a].map fin9)).sum
  | some (p,j) => ((List.range (p+1)).map fun a =>
      normalWord ([p+j-t].map fin9) ([j,a,p-a].map fin9)).sum

def finitePaperRow9 (t : ℕ) (row : List ℤ) :
    Core (Fin 9) K →ₗ[K] Core (Fin 9) K :=
  (((columns t).zip row).map fun term =>
    ((term.2 : K) / 1000000000000) • finitePaperColumn9 t term.1).sum

private theorem rename_list_sum {I : Type*} (l : List I)
    (F : I → (Core (Fin 9) K →ₗ[K] Core (Fin 9) K))
    (G : I → (Core ℕ K →ₗ[K] Core ℕ K)) (p : Core (Fin 9) K)
    (h : ∀ a ∈ l, MvPolynomial.rename Fin.val (F a p) =
      G a (MvPolynomial.rename Fin.val p)) :
    MvPolynomial.rename Fin.val ((l.map F).sum p) =
      (l.map G).sum (MvPolynomial.rename Fin.val p) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, map_add]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem rename_finitePaperColumn9 (t : ℕ) (col : Option (ℕ × ℕ))
    (h : columnLabelsBounded9 t col = true) (p : Core (Fin 9) K) :
    MvPolynomial.rename Fin.val (finitePaperColumn9 t col p) =
      paperColumnWordOperator t col (MvPolynomial.rename Fin.val p) := by
  cases col with
  | none =>
    apply rename_list_sum
    intro a ha
    exact rename_fin9_normalWord [] [a,t-a] (List.all_eq_true.mp h a ha) p
  | some pair =>
    rcases pair with ⟨q,j⟩
    apply rename_list_sum
    intro a ha
    exact rename_fin9_normalWord [q+j-t] [j,a,q-a] (List.all_eq_true.mp h a ha) p

theorem rename_finitePaperRow9 (t : ℕ) (row : List ℤ)
    (h : rowLabelsBounded9 t = true) (p : Core (Fin 9) K) :
    MvPolynomial.rename Fin.val (finitePaperRow9 t row p) =
      paperRowWordOperator t row (MvPolynomial.rename Fin.val p) := by
  apply rename_list_sum
  intro term hm
  rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    rename_finitePaperColumn9 t term.1
      (List.all_eq_true.mp h term.1 (List.of_mem_zip hm).1)]

theorem finitePaperRow9_word_action (t d : ℕ) (row : List ℤ) (s : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hout : d-t < 9)
    (hb : rowLabelsBounded9 t = true) (ha : rowOutputOK t d s = true) :
    finitePaperRow9 t row (wordPolynomial (s.map fin9) : Core (Fin 9) K) =
      ((threeRowAction t row s : K) / 1000000000000) •
        MvPolynomial.X (fin9 (d-t)) := by
  apply MvPolynomial.rename_injective Fin.val Fin.val_injective
  rw [rename_finitePaperRow9 t row hb, rename_fin9_word s hs,
    paperRowWordOperator_apply t d row s ha, map_smul, MvPolynomial.rename_X]
  simp only [fin9, Nat.mod_eq_of_lt hout]

/-- Exact physical coordinate transport of the original row on each bounded
source word. The only assumptions are label bounds and the checked output shape. -/
theorem conjugated_finitePaperRow9_action (κ : Fin 9 → K) (hκ : ∀ j, κ j ≠ 0)
    (t d : ℕ) (row : List ℤ) (s : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hout : d-t < 9)
    (hb : rowLabelsBounded9 t = true) (ha : rowOutputOK t d s = true) :
    conjugateOperator κ hκ (finitePaperRow9 t row) (scaledWord κ (s.map fin9)) =
      ((threeRowAction t row s : K) / 1000000000000) •
        scaledWord κ [fin9 (d-t)] := by
  rw [← rescaleEquiv_word κ hκ, conjugateOperator_apply_rescale,
    finitePaperRow9_word_action t d row s hs hout hb ha, map_smul]
  have hw : (MvPolynomial.X (fin9 (d-t)) : Core (Fin 9) K) =
      wordPolynomial [fin9 (d-t)] := by simp [wordPolynomial]
  rw [hw, rescaleEquiv_word]

#print axioms normalWord_rename
#print axioms rename_finitePaperRow9
#print axioms conjugated_finitePaperRow9_action
end TorusLean.Shared.BosonFiniteCertificateConjugation
