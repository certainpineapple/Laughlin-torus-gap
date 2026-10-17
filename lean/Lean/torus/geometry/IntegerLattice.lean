import torus.geometry.RealLatticeCoordinates
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# The actual integer lattice, with discreteness derived from magnetic area

The integer submodule is exactly the image of the period map. Its discrete
topology and full real span are proved from the explicit real period basis,
which was constructed from the legal positive magnetic area. None of these
properties is an additional physical input or a model field.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

noncomputable section

/-- The actual lattice of all integer combinations of the physical periods. -/
def integerLattice (omega1 omega2 : ℂ) : Submodule ℤ ℂ :=
  Submodule.span ℤ ({omega1, omega2} : Set ℂ)

theorem integerLattice_mem_iff (omega1 omega2 z : ℂ) :
    z ∈ integerLattice omega1 omega2 ↔
      ∃ p : ℤ × ℤ, latticePeriod omega1 omega2 p = z := by
  rw [integerLattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m, n), by simpa only [latticePeriod, zsmul_eq_mul] using h⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, by simpa only [latticePeriod, zsmul_eq_mul] using hp⟩

theorem latticeRealBasis_range (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    Set.range (latticeRealBasis M hM omega1 omega2 harea) = {omega1, omega2} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [latticeRealBasis_zero, latticeRealBasis_one]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · refine ⟨0, ?_⟩
      rw [latticeRealBasis_zero]
      exact hz.symm
    · refine ⟨1, ?_⟩
      rw [latticeRealBasis_one]
      exact hz.symm

theorem integerLattice_eq_basis_span (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    integerLattice omega1 omega2 =
      Submodule.span ℤ (Set.range (latticeRealBasis M hM omega1 omega2 harea)) := by
  rw [latticeRealBasis_range]
  rfl

/-- Discreteness is obtained from legal geometry, not assumed. -/
theorem integerLattice_discrete (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    DiscreteTopology (integerLattice omega1 omega2) := by
  rw [integerLattice_eq_basis_span M hM omega1 omega2 harea]
  infer_instance

theorem integerLattice_real_span (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    Submodule.span ℝ (integerLattice omega1 omega2 : Set ℂ) = ⊤ := by
  rw [integerLattice_eq_basis_span M hM omega1 omega2 harea]
  exact ZSpan.span_top (latticeRealBasis M hM omega1 omega2 harea)

/-- An explicit derived instance for library consumers. The discrete topology
in the result has already been proved from the same legal physical inputs. -/
theorem integerLattice_isZLattice (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    letI := integerLattice_discrete M hM omega1 omega2 harea
    IsZLattice ℝ (integerLattice omega1 omega2) := by
  letI := integerLattice_discrete M hM omega1 omega2 harea
  exact ⟨integerLattice_real_span M hM omega1 omega2 harea⟩

/-- This is the rank of the actual integer lattice, not a physical LLL
dimension claim. -/
theorem integerLattice_rank_two (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    Module.finrank ℤ (integerLattice omega1 omega2) = 2 := by
  letI := integerLattice_discrete M hM omega1 omega2 harea
  letI := integerLattice_isZLattice M hM omega1 omega2 harea
  rw [ZLattice.rank ℝ (integerLattice omega1 omega2), Complex.finrank_real_complex]

#print axioms integerLattice_mem_iff
#print axioms latticeRealBasis_range
#print axioms integerLattice_eq_basis_span
#print axioms integerLattice_discrete
#print axioms integerLattice_real_span
#print axioms integerLattice_isZLattice
#print axioms integerLattice_rank_two

end

end TorusLean.Geometry
