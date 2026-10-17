import torus.shared.BosonNatFourUnnormalizedTrace

/-! The existing true complex COM trace expressed in the actual full-L4 cell
matrix form. Off-diagonal relative entries and all unnormalized factorials
are retained; only distinct COM levels are eliminated. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourMatrixCOMTrace
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonNatFourUnnormalizedTrace
open MeasureTheory
open scoped BigOperators
local instance matrixTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem complex_density_integrable (G : Geometry) (theta : Twist) (k : ℕ)
    {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ∑ i, ∑ j, C i j * ip
      (natFourAnnihilator G theta R (p i) f)
      (natFourAnnihilator G theta R (p j) f)) (cellMeasure G k) := by
  simp_rw [natFourAnnihilator_ground G theta _ (hp _)]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (natFourRemoval_cross_integrable G theta k (p i) (p j)
    (hp i) (hp j) 0 0 f f).const_mul (C i j)

private theorem matrixCell_eq_integral_re (G : Geometry) (theta : Twist) (k : ℕ)
    {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta k p hp C f =
      (∫ R, ∑ i, ∑ j, C i j * ip (natFourAnnihilator G theta R (p i) f)
        (natFourAnnihilator G theta R (p j) f) ∂cellMeasure G k).re := by
  rw [natFourMatrixCellLiftForm_eq_annihilator]
  have h := integral_re (complex_density_integrable G theta k p hp C f)
  change (∫ R, (∑ i, ∑ j, C i j * ip (natFourAnnihilator G theta R (p i) f)
    (natFourAnnihilator G theta R (p j) f)).re ∂cellMeasure G k) =
    (∫ R, ∑ i, ∑ j, C i j * ip (natFourAnnihilator G theta R (p i) f)
      (natFourAnnihilator G theta R (p j) f) ∂cellMeasure G k).re at h
  exact h

/-- All finite matrix coefficients may be separated from true ground-cell
cross integrals, with their actual L1 domains proved first. -/
theorem natFourMatrixCellLiftForm_integrated_cross (G : Geometry) (theta : Twist) (k : ℕ)
    {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta k p hp C f =
      (∑ i, ∑ j, C i j * (∫ R, ip
        (natFourRemoval G theta (p i) (hp i) 0 R f)
        (natFourRemoval G theta (p j) (hp j) 0 R f) ∂cellMeasure G k)).re := by
  rw [matrixCell_eq_integral_re]
  simp_rw [natFourAnnihilator_ground G theta _ (hp _)]
  have hi (i j : Fin r) := (natFourRemoval_cross_integrable G theta k
    (p i) (p j) (hp i) (hp j) 0 0 f f).const_mul (C i j)
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j),integral_const_mul]

/-- A genuine family of unnormalized COM columns is traced without altering
its relative Gram or its full matrix of cross coefficients. -/
theorem natFourMatrixCellLiftForm_COM_trace (G : Geometry) (theta : Twist)
    {r : ℕ} (p v : Fin r → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 4) (hv : ∀ i, (v i).IsHomogeneous 4)
    (hL : ∀ i, canonicalCOMLowerNat (p i)=0) (n : Fin r → ℕ)
    (he : ∀ i, v i=(canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n i] (p i))
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 2 v hv C f =
      ((2/4:ℂ)*∑ i, ∑ j, if n i=n j then
        (4^(n i)*((n i).factorial:ℂ))*C i j *
          (∫ R, ip (natFourRemoval G theta (p i) (hp i) 0 R f)
            (natFourRemoval G theta (p j) (hp j) 0 R f) ∂cellMeasure G 4)
        else 0).re := by
  rw [matrixCell_eq_integral_re]
  simp_rw [he]
  exact congrArg Complex.re (finite_unnormalized_COM_matrix_trace G theta
    Finset.univ Finset.univ p p hp hp hL hL n n C f f)

#print axioms natFourMatrixCellLiftForm_integrated_cross
#print axioms natFourMatrixCellLiftForm_COM_trace
end TorusLean.Shared.BosonNatFourMatrixCOMTrace
