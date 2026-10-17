import torus.shared.BosonNatThreeRemovalTrace

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeMatrixTrace
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatThreeRemovalTrace
open MeasureTheory
open scoped BigOperators

/-- Arbitrary finite matrix combinations of actual all-core source rows.
The complex coefficients and both input vectors are retained. -/
theorem finite_matrix_row_trace {ι κ : Type*} (G : Geometry) (theta : Twist)
    (s : Finset ι) (t : Finset κ) (p : ι → Core ℕ ℂ) (r : κ → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 3) (hr : ∀ j, (r j).IsHomogeneous 3)
    (hpL : ∀ i, canonicalCOMLowerNat (p i)=0) (hrL : ∀ j, canonicalCOMLowerNat (r j)=0)
    (n : ι → ℕ) (m : κ → ℕ) (M : ι → κ → ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i ∈ s, ∑ j ∈ t, M i j *
      ip (natThreeRemoval G theta (p i) (hp i) (n i) R f)
        (natThreeRemoval G theta (r j) (hr j) (m j) R g) ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i ∈ s, ∑ j ∈ t, if n i=m j then M i j *
      (∫ R, ip (natThreeRemoval G theta (p i) (hp i) 0 R f)
        (natThreeRemoval G theta (r j) (hr j) 0 R g) ∂cellMeasure G 3) else 0 := by
  have hi (i : ι) (j : κ) := (natThreeRemoval_cross_integrable G theta 2 _ _
    (hp i) (hr j) (n i) (m j) f g).const_mul (M i j)
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum t (fun j _ => hi i j))]
  simp_rw [integral_finsetSum t (fun j _ => hi _ j),integral_const_mul,
    natThreeRemoval_com_integral G theta _ _ (hp _) (hr _) (hpL _) (hrL _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  apply Finset.sum_congr rfl
  intro j hjt
  split_ifs <;> ring

/-- The genuine finite COM partial trace for original all-N L3 row forms.
There is no Hermitian, orthogonality, Gram-inverse or matrix-order premise. -/
theorem finite_COM_matrix_partial_trace {A B : Type*} [Fintype A] [Fintype B]
    (G : Geometry) (theta : Twist) (H : ℕ)
    (p : A → Core ℕ ℂ) (r : B → Core ℕ ℂ)
    (hp : ∀ a, (p a).IsHomogeneous 3) (hr : ∀ b, (r b).IsHomogeneous 3)
    (hpL : ∀ a, canonicalCOMLowerNat (p a)=0) (hrL : ∀ b, canonicalCOMLowerNat (r b)=0)
    (M : (A × Fin (H+1)) → (B × Fin (H+1)) → ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ a, ∑ n : Fin (H+1), ∑ b, ∑ m : Fin (H+1), M (a,n) (b,m) *
      ip (natThreeRemoval G theta (p a) (hp a) n.val R f)
        (natThreeRemoval G theta (r b) (hr b) m.val R g) ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ a, ∑ b, (∑ n : Fin (H+1), M (a,n) (b,n)) *
      (∫ R, ip (natThreeRemoval G theta (p a) (hp a) 0 R f)
        (natThreeRemoval G theta (r b) (hr b) 0 R g) ∂cellMeasure G 3) := by
  classical
  have h := finite_matrix_row_trace G theta (Finset.univ : Finset (A × Fin (H+1)))
    (Finset.univ : Finset (B × Fin (H+1))) (fun an => p an.1) (fun bm => r bm.1)
    (fun an => hp an.1) (fun bm => hr bm.1) (fun an => hpL an.1) (fun bm => hrL bm.1)
    (fun an => an.2.val) (fun bm => bm.2.val) M f g
  simp only [Fintype.sum_prod_type,Fin.val_inj] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp [Finset.sum_mul]

end TorusLean.Shared.BosonNatThreeMatrixTrace
