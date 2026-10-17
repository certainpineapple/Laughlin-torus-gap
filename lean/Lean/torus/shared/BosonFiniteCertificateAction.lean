import torus.shared.BosonFiniteCertificatePlanar
import torus.shared.BosonFiniteCertificateWords

/-!
# Frozen rational rows act as genuine polynomial differential operators

The only output-shape assumption is a finite, decidable list statement:
each nonzero annihilator word leaves the stated singleton output. It contains
no PSD condition or target inequality and can be checked directly on the
finite input occupation lists. The row coefficients and ordering are exactly
`columns t` zipped with the stored integer row, divided by 10^12.
-/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Boson
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords

variable {K : Type*} [Field K]

theorem removalWeight_eq_wordRemovalWeight (s labels : List ℕ) :
    removalWeight s labels = wordRemovalWeight s labels := by
  induction labels generalizing s with
  | nil => rfl
  | cons j js ih => simp only [removalWeight, wordRemovalWeight, ih]

/-- A finite combinatorial test of the output of one genuine normal word. -/
def wordOutputOK (s creators annihilators : List ℕ) (out : ℕ) : Bool :=
  decide (removalWeight s annihilators = 0 ∨
    creators ++ eraseWord s annihilators = [out])

/-- The output test is independent of the values of the row coefficients. -/
def columnOutputOK (t d : ℕ) (s : List ℕ) (col : Option (ℕ × ℕ)) : Bool :=
  match col with
  | none => (List.range (t+1)).all fun a => wordOutputOK s [] [a,t-a] (d-t)
  | some (p,j) => (List.range (p+1)).all fun a =>
      wordOutputOK s [p+j-t] [j,a,p-a] (d-t)

def rowOutputOK (t d : ℕ) (s : List ℕ) : Bool :=
  (columns t).all (columnOutputOK t d s)

theorem normalWord_apply_of_outputOK (s creators annihilators : List ℕ) (out : ℕ)
    (h : wordOutputOK s creators annihilators out = true) :
    normalWord creators annihilators (wordPolynomial s : Core ℕ K) =
      (removalWeight s annihilators : K) • MvPolynomial.X out := by
  rw [normalWord_wordPolynomial, ← removalWeight_eq_wordRemovalWeight]
  have hh : removalWeight s annihilators = 0 ∨
      creators ++ eraseWord s annihilators = [out] := of_decide_eq_true h
  rcases hh with hz | ho
  · simp [hz]
  · simp [ho, wordPolynomial]

/-- The column is a finite sum of actual creation/derivative operators. -/
def paperColumnWordOperator (t : ℕ) (col : Option (ℕ × ℕ)) :
    Core ℕ K →ₗ[K] Core ℕ K :=
  match col with
  | none => ((List.range (t+1)).map fun a => normalWord [] [a,t-a]).sum
  | some (p,j) => ((List.range (p+1)).map fun a =>
      normalWord [p+j-t] [j,a,p-a]).sum

def columnRemoval (t : ℕ) (s : List ℕ) (col : Option (ℕ × ℕ)) : ℕ :=
  match col with
  | none => pairRemoval s t
  | some (p,j) => spectatorPairRemoval s p j

private theorem list_operator_action {I : Type*} (l : List I)
    (ops : I → (Core ℕ K →ₗ[K] Core ℕ K)) (coeff : I → K)
    (v w : Core ℕ K) (h : ∀ a ∈ l, ops a v = coeff a • w) :
    (l.map ops).sum v = (l.map coeff).sum • w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb])), add_smul]

private theorem nat_sum_cast {I : Type*} (l : List I) (f : I → ℕ) :
    (((l.map f).sum : ℕ) : K) = (l.map fun a => (f a : K)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem paperColumnWordOperator_apply (t d : ℕ) (s : List ℕ)
    (col : Option (ℕ × ℕ)) (h : columnOutputOK t d s col = true) :
    paperColumnWordOperator t col (wordPolynomial s : Core ℕ K) =
      (columnRemoval t s col : K) • MvPolynomial.X (d-t) := by
  cases col with
  | none =>
    rw [paperColumnWordOperator]
    rw [list_operator_action _ _
      (fun a => (removalWeight s [a,t-a] : K)) _ (MvPolynomial.X (d-t))]
    · rw [columnRemoval, pairRemoval, nat_sum_cast]
    · intro a ha
      exact normalWord_apply_of_outputOK s [] [a,t-a] (d-t)
        (List.all_eq_true.mp h a ha)
  | some pair =>
    rcases pair with ⟨p,j⟩
    rw [paperColumnWordOperator]
    rw [list_operator_action _ _
      (fun a => (removalWeight s [j,a,p-a] : K)) _ (MvPolynomial.X (d-t))]
    · rw [columnRemoval, spectatorPairRemoval, nat_sum_cast]
    · intro a ha
      exact normalWord_apply_of_outputOK s [p+j-t] [j,a,p-a] (d-t)
        (List.all_eq_true.mp h a ha)

/-- The actual rational row operator, with the frozen column convention. -/
def paperRowWordOperator (t : ℕ) (row : List ℤ) : Core ℕ K →ₗ[K] Core ℕ K :=
  (((columns t).zip row).map fun term =>
    ((term.2 : K) / 1000000000000) • paperColumnWordOperator t term.1).sum

private theorem foldl_add_sum {I : Type*} (l : List I) (f : I → ℤ) (acc : ℤ) :
    l.foldl (fun out term => out + f term) acc = acc + (l.map f).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

theorem threeRowAction_eq_sum (t : ℕ) (row : List ℤ) (s : List ℕ) :
    threeRowAction t row s =
      (((columns t).zip row).map fun term => term.2 * (columnRemoval t s term.1 : ℤ)).sum := by
  unfold threeRowAction
  rw [foldl_add_sum, zero_add]
  congr 1
  apply List.map_congr_left
  intro term hm
  rcases term with ⟨col,c⟩
  cases col with
  | none => rfl
  | some pair => cases pair; rfl

private theorem row_sum_cast (l : List (Option (ℕ × ℕ) × ℤ))
    (w : Option (ℕ × ℕ) → ℕ) :
    (l.map fun term => (term.2 : K) / 1000000000000 * (w term.1 : K)).sum =
      (((l.map fun term => term.2 * (w term.1 : ℤ)).sum : ℤ) : K) / 1000000000000 := by
  induction l with
  | nil => simp
  | cons term l ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, Int.cast_natCast, ih]
    ring

/-- Frozen integer row action equals a genuine MvPolynomial differential
operator under a finite output-shape condition alone. -/
theorem paperRowWordOperator_apply (t d : ℕ) (row : List ℤ) (s : List ℕ)
    (h : rowOutputOK t d s = true) :
    paperRowWordOperator t row (wordPolynomial s : Core ℕ K) =
      ((threeRowAction t row s : K) / 1000000000000) • MvPolynomial.X (d-t) := by
  unfold paperRowWordOperator
  rw [list_operator_action _ _
    (fun term => (term.2 : K) / 1000000000000 * (columnRemoval t s term.1 : K))
    _ (MvPolynomial.X (d-t))]
  · rw [row_sum_cast, threeRowAction_eq_sum]
  · intro term hm
    rw [LinearMap.smul_apply, paperColumnWordOperator_apply t d s term.1
      (List.all_eq_true.mp h term.1 (List.of_mem_zip hm).1), smul_smul]

#print axioms removalWeight_eq_wordRemovalWeight
#print axioms normalWord_apply_of_outputOK
#print axioms paperColumnWordOperator_apply
#print axioms threeRowAction_eq_sum
#print axioms paperRowWordOperator_apply
end TorusLean.Shared.BosonFiniteCertificateAction
