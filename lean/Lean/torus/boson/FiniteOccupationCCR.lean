import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.Ring

/-!
# Bosonic finite occupation core

`Core ι K` is the algebraic symmetric Fock core in polynomial coordinates.
Every vector has finitely many occupation monomials, with arbitrary natural
occupations. It is not a definition of the physical torus LLL. For the paper's
rational coordinates take `ι = ℕ`, `K = ℚ`, with `x_j = sqrt(j!) a_j†`.
The physical metric and torus orbital bridge are recorded as pending in README.

Multiplication and formal differentiation preserve this common algebraic
domain. No bounded annihilator or fermionic CAR is used here.
-/

namespace TorusLean.Boson

noncomputable section

variable {ι K : Type*} [CommRing K]

/-- Finite linear combinations of unrestricted occupation monomials. -/
abbrev Core (ι K : Type*) [CommRing K] := MvPolynomial ι K

/-- Polynomial creation; its physical normalization depends on the metric. -/
def create (i : ι) : Core ι K →ₗ[K] Core ι K :=
  LinearMap.mulLeft K (MvPolynomial.X i)

/-- Polynomial annihilation on the finite occupation core. -/
def annihilate (i : ι) : Core ι K →ₗ[K] Core ι K :=
  (MvPolynomial.pderiv i).toLinearMap

/-- The number operator in canonical polynomial coordinates. -/
def number (i : ι) : Core ι K →ₗ[K] Core ι K :=
  (create i).comp (annihilate i)

/-- The canonical bosonic commutation relation on a genuine common domain. -/
theorem annihilate_create [DecidableEq ι] (i j : ι) (f : Core ι K) :
    annihilate i (create j f) =
      create j (annihilate i f) + (if i = j then f else 0) := by
  classical
  by_cases h : i = j
  · subst j
    simp [annihilate, create, MvPolynomial.pderiv_mul, add_comm]
  · simp [annihilate, create, MvPolynomial.pderiv_mul, h, Ne.symm h]

theorem bosonic_ccr [DecidableEq ι] (i j : ι) (f : Core ι K) :
    annihilate i (create j f) - create j (annihilate i f) =
      (if i = j then f else 0) := by
  classical
  rw [annihilate_create]
  simp

theorem create_commute (i j : ι) (f : Core ι K) :
    create i (create j f) = create j (create i f) := by
  simp [create, mul_assoc, mul_comm, mul_left_comm]

theorem annihilate_commute (i j : ι) (f : Core ι K) :
    annihilate i (annihilate j f) = annihilate j (annihilate i f) := by
  classical
  change MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f)
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  by_cases h : i = j
  · subst j
    rfl
  · simp [Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h,
      add_assoc, add_comm, add_left_comm]
    ring

theorem number_monomial (i : ι) (n : ι →₀ ℕ) (r : K) :
    number i (MvPolynomial.monomial n r) = n i • MvPolynomial.monomial n r := by
  exact MvPolynomial.X_mul_pderiv_monomial

/-- Pair removal is a two-particle differential operator on the same core. -/
def pairAnnihilate (i j : ι) : Core ι K →ₗ[K] Core ι K :=
  (annihilate i).comp (annihilate j)

/-- Four removals can be reordered as two commuting bosonic pair removals. -/
theorem pairAnnihilate_commute (i j k l : ι) (f : Core ι K) :
    pairAnnihilate i j (pairAnnihilate k l f) =
      pairAnnihilate k l (pairAnnihilate i j f) := by
  change annihilate i (annihilate j (annihilate k (annihilate l f))) =
    annihilate k (annihilate l (annihilate i (annihilate j f)))
  rw [annihilate_commute j k, annihilate_commute i k,
    annihilate_commute j l, annihilate_commute i l]

/-- The single contraction in a row square uses a plus sign (CCR). -/
theorem row_single_contraction [DecidableEq ι] (i j k : ι) (f : Core ι K) :
    annihilate i (create j (annihilate k f)) =
      create j (annihilate i (annihilate k f)) +
        (if i = j then annihilate k f else 0) :=
  annihilate_create i j (annihilate k f)

/-- The paper's ordered rational pair sum `Bhat_p = sum_(a+b=p) ∂a ∂b`.
No extra factorial is included; `κ_p` is a separate physical normalization. -/
def rationalPair (p : ℕ) : Core ℕ K →ₗ[K] Core ℕ K :=
  ∑ ab ∈ Finset.antidiagonal p, pairAnnihilate ab.1 ab.2

theorem rationalPair_commute (p q : ℕ) (f : Core ℕ K) :
    rationalPair p (rationalPair q f) = rationalPair q (rationalPair p f) := by
  classical
  simp only [rationalPair, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab hab
  apply Finset.sum_congr rfl
  intro cd hcd
  exact pairAnnihilate_commute ab.1 ab.2 cd.1 cd.2 f

#print axioms annihilate_create
#print axioms bosonic_ccr
#print axioms create_commute
#print axioms annihilate_commute
#print axioms number_monomial
#print axioms pairAnnihilate_commute
#print axioms row_single_contraction
#print axioms rationalPair_commute

end

end TorusLean.Boson
