/- Computable unnormalized occupation-coordinate construction for the finite
three-particle planar comparison. Every row action uses the frozen integers.
The row form is F†F minus its two-body part; it is NOT the connected H square.
No thermal/periodization theorem is assumed here. -/
import torus.shared.BosonFiniteCertificateRows
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
namespace TorusLean.BosonFiniteCertificate

/-- Multiplicity of a derivative word on an occupation monomial. Missing
annihilators produce zero; repeated labels contribute their falling factorial. -/
def removalWeight : List ℕ → List ℕ → ℕ
  | _, [] => 1
  | s, j :: js => s.count j * removalWeight (s.erase j) js

def pairRemoval (s : List ℕ) (p : ℕ) : ℕ :=
  ((List.range (p+1)).map fun a => removalWeight s [a,p-a]).sum

def spectatorPairRemoval (s : List ℕ) (p j : ℕ) : ℕ :=
  ((List.range (p+1)).map fun a => removalWeight s [j,a,p-a]).sum

/-- Coefficient in the single surviving monomial x_(d-t). Ordered pairs,
including both orders of unequal labels, are included in pairRemoval. -/
def threeRowAction (t : ℕ) (row : List ℤ) (s : List ℕ) : ℤ :=
  ((columns t).zip row).foldl (fun out term => out + term.2 *
    (match term.1 with
     | none => (pairRemoval s t : ℤ)
     | some (p,j) => (spectatorPairRemoval s p j : ℤ))) 0

/-- Integer numerator of the quadratic form of the anchored M3 coefficient.
The factorial is the metric of the one-particle output, not an extra lift
factor. The purely two-body part is subtracted before the COM partial trace. -/
def threeRowFormNumerator (d : ℕ) (a b : List ℕ) : ℤ :=
  ((List.range 4).map fun t => if t ≤ d then
    (Nat.factorial (d-t) : ℤ) * ((frozenRows t).map fun row =>
      threeRowAction t row a * threeRowAction t row b -
        rowInteger row 0 * rowInteger row 0 *
          (pairRemoval a t : ℤ) * (pairRemoval b t : ℤ)).sum
    else 0).sum

def threeRowForm (d : ℕ) (a b : List ℕ) : ℚ :=
  (threeRowFormNumerator d a b : ℚ) / 1000000000000000000000000

/-- Actual planar pair-contact Hamiltonian form in the same factorial metric.
The planar coefficient p!/2^(p+1) is kept exactly. -/
def planarHForm (d : ℕ) (a b : List ℕ) : ℚ :=
  ((List.range (d+1)).map fun p =>
    (Nat.factorial p * Nat.factorial (d-p) * pairRemoval a p * pairRemoval b p : ℕ) /
      (2 : ℚ)^(p+1)).sum

def occupationMetric (s : List ℕ) : ℕ :=
  (s.eraseDups.map fun j => (s.count j).factorial * j.factorial ^ s.count j).prod

/-- Entire lexicographically ordered three-particle degree block, with
repetitions allowed and without a cutoff on individual occupation counts. -/
def threeBasis (d : ℕ) : List (List ℕ) :=
  (List.range (d+1)).flatMap fun a =>
    (List.range (d+1)).flatMap fun b =>
      ((List.range (d+1)).filter fun c => a ≤ b && b ≤ c && a+b+c == d).map
        fun c => [a,b,c]

def loweringEntry (a b : List ℕ) : ℤ :=
  (b.eraseDups.map fun j => if 0 < j &&
      List.insertionSort (· ≤ ·) ((j-1) :: b.erase j) == a then
    (j * b.count j : ℕ) else 0).sum

def raisingEntry (a b : List ℕ) : ℤ :=
  (b.eraseDups.map fun j => if
      List.insertionSort (· ≤ ·) ((j+1) :: b.erase j) == a then
    (b.count j : ℕ) else 0).sum

def integerForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (A i j : ℚ) / 1000000000000000000000000

/-- General split of the rational finite comparison; unlike M3, S3 is
constructed from the planar Hamiltonian square. -/
def planarSingleForm {n : ℕ} (Ginv H : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ := H * Ginv * H - H

#print axioms threeRowAction
end TorusLean.BosonFiniteCertificate
