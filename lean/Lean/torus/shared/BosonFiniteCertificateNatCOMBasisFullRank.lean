import torus.shared.BosonFiniteCertificateNatCOMBasisRank300
import torus.shared.BosonFiniteCertificateNatCOMBasisRank301
import torus.shared.BosonFiniteCertificateNatCOMBasisRank302
import torus.shared.BosonFiniteCertificateNatCOMBasisRank303
import torus.shared.BosonFiniteCertificateNatCOMBasisRank304
import torus.shared.BosonFiniteCertificateNatCOMBasisRank305
import torus.shared.BosonFiniteCertificateNatCOMBasisRank306
import torus.shared.BosonFiniteCertificateNatCOMBasisRank307
import torus.shared.BosonFiniteCertificateNatCOMBasisRank308
import torus.shared.BosonFiniteCertificateNatCOMBasisSourceForm

/-! The true finite source kernel on all finite N3 inputs. The original
M3 form equals nine full descendant-family rank forms, with the actual
inverse Gram on both sides and every source cross entry retained. The
weighted projectors are removed using actual occupation inner products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators

theorem natFamilyAnalysis_orbitalComponent {r d : ℕ}
    (w : Fin r → Core ℕ ℂ)
    (hw : ∀ i, (w i).IsWeightedHomogeneous id d) (f : Core ℕ ℂ) :
    natFamilyAnalysis w (natOrbitalComponent d f) = natFamilyAnalysis w f := by
  funext i
  exact natOccupationInner_orbitalComponent_right d (w i) f (hw i)

theorem natFamilyRankForm_orbitalComponent {r d : ℕ}
    (w : Fin r → Core ℕ ℂ) (C : Matrix (Fin r) (Fin r) ℂ)
    (hw : ∀ i, (w i).IsWeightedHomogeneous id d) (f g : Core ℕ ℂ) :
    natFamilyRankForm w C (natOrbitalComponent d f) (natOrbitalComponent d g) =
      natFamilyRankForm w C f g := by
  unfold natFamilyRankForm
  rw [natFamilyAnalysis_orbitalComponent w hw f,
    natFamilyAnalysis_orbitalComponent w hw g]

private theorem natCOMBasis_column_weighted {n r d : ℕ}
    (occ : Fin n → (Fin 9 →₀ ℕ))
    (hN : ∀ i, (occ i).degree = 3)
    (hd : ∀ i, Finsupp.weight Fin.val (occ i) = d)
    (S : Matrix (Fin n) (Fin r) ℂ) (w : Fin r → Core ℕ ℂ)
    (hw : ∀ j, w j = MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) occ (fun i => S i j)))
    (j : Fin r) : (w j).IsWeightedHomogeneous id d := by
  rw [hw j]
  exact (rename_canonicalBlock_bihomogeneous d occ hN hd _).2

/-- A finite rank cross form using the actual complete descendant family of each block. -/
def natCOMOriginalM3RankBlock (d : Fin 9) (f g : Core ℕ ℂ) : ℂ :=
  ![natFamilyRankForm k300COMDescendantFamily k300COMRankCoefficient f g,
    natFamilyRankForm k301COMDescendantFamily k301COMRankCoefficient f g,
    natFamilyRankForm k302COMDescendantFamily k302COMRankCoefficient f g,
    natFamilyRankForm k303COMDescendantFamily k303COMRankCoefficient f g,
    natFamilyRankForm k304COMDescendantFamily k304COMRankCoefficient f g,
    natFamilyRankForm k305COMDescendantFamily k305COMRankCoefficient f g,
    natFamilyRankForm k306COMDescendantFamily k306COMRankCoefficient f g,
    natFamilyRankForm k307COMDescendantFamily k307COMRankCoefficient f g,
    natFamilyRankForm k308COMDescendantFamily k308COMRankCoefficient f g] d

theorem natCOMOriginalM3RankBlock_eq_component (d : Fin 9) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    natCOMOriginalM3RankBlock d f g = canonicalNatOriginalM3Form
      (natOrbitalComponent d.val f) (natOrbitalComponent d.val g) := by
  fin_cases d
  · change natFamilyRankForm k300COMDescendantFamily k300COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 0 f) (natOrbitalComponent 0 g)
    rw [← natFamilyRankForm_orbitalComponent k300COMDescendantFamily
      k300COMRankCoefficient (natCOMBasis_column_weighted k300occ
        k300_particle_degree k300_orbital_degree (complexify k300COMBasis)
        k300COMDescendantFamily k300_COMDescendantFamily_column) f g]
    exact k300_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 0 f hNf) (natOrbitalComponent_weighted 0 f)
      (natOrbitalComponent_particle 3 0 g hNg) (natOrbitalComponent_weighted 0 g)
  · change natFamilyRankForm k301COMDescendantFamily k301COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 1 f) (natOrbitalComponent 1 g)
    rw [← natFamilyRankForm_orbitalComponent k301COMDescendantFamily
      k301COMRankCoefficient (natCOMBasis_column_weighted k301occ
        k301_particle_degree k301_orbital_degree (complexify k301COMBasis)
        k301COMDescendantFamily k301_COMDescendantFamily_column) f g]
    exact k301_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 1 f hNf) (natOrbitalComponent_weighted 1 f)
      (natOrbitalComponent_particle 3 1 g hNg) (natOrbitalComponent_weighted 1 g)
  · change natFamilyRankForm k302COMDescendantFamily k302COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 2 f) (natOrbitalComponent 2 g)
    rw [← natFamilyRankForm_orbitalComponent k302COMDescendantFamily
      k302COMRankCoefficient (natCOMBasis_column_weighted k302occ
        k302_particle_degree k302_orbital_degree (complexify k302COMBasis)
        k302COMDescendantFamily k302_COMDescendantFamily_column) f g]
    exact k302_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 2 f hNf) (natOrbitalComponent_weighted 2 f)
      (natOrbitalComponent_particle 3 2 g hNg) (natOrbitalComponent_weighted 2 g)
  · change natFamilyRankForm k303COMDescendantFamily k303COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 3 f) (natOrbitalComponent 3 g)
    rw [← natFamilyRankForm_orbitalComponent k303COMDescendantFamily
      k303COMRankCoefficient (natCOMBasis_column_weighted k303occ
        k303_particle_degree k303_orbital_degree (complexify k303COMBasis)
        k303COMDescendantFamily k303_COMDescendantFamily_column) f g]
    exact k303_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 3 f hNf) (natOrbitalComponent_weighted 3 f)
      (natOrbitalComponent_particle 3 3 g hNg) (natOrbitalComponent_weighted 3 g)
  · change natFamilyRankForm k304COMDescendantFamily k304COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 4 f) (natOrbitalComponent 4 g)
    rw [← natFamilyRankForm_orbitalComponent k304COMDescendantFamily
      k304COMRankCoefficient (natCOMBasis_column_weighted k304occ
        k304_particle_degree k304_orbital_degree (complexify k304COMBasis)
        k304COMDescendantFamily k304_COMDescendantFamily_column) f g]
    exact k304_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 4 f hNf) (natOrbitalComponent_weighted 4 f)
      (natOrbitalComponent_particle 3 4 g hNg) (natOrbitalComponent_weighted 4 g)
  · change natFamilyRankForm k305COMDescendantFamily k305COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 5 f) (natOrbitalComponent 5 g)
    rw [← natFamilyRankForm_orbitalComponent k305COMDescendantFamily
      k305COMRankCoefficient (natCOMBasis_column_weighted k305occ
        k305_particle_degree k305_orbital_degree (complexify k305COMBasis)
        k305COMDescendantFamily k305_COMDescendantFamily_column) f g]
    exact k305_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 5 f hNf) (natOrbitalComponent_weighted 5 f)
      (natOrbitalComponent_particle 3 5 g hNg) (natOrbitalComponent_weighted 5 g)
  · change natFamilyRankForm k306COMDescendantFamily k306COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 6 f) (natOrbitalComponent 6 g)
    rw [← natFamilyRankForm_orbitalComponent k306COMDescendantFamily
      k306COMRankCoefficient (natCOMBasis_column_weighted k306occ
        k306_particle_degree k306_orbital_degree (complexify k306COMBasis)
        k306COMDescendantFamily k306_COMDescendantFamily_column) f g]
    exact k306_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 6 f hNf) (natOrbitalComponent_weighted 6 f)
      (natOrbitalComponent_particle 3 6 g hNg) (natOrbitalComponent_weighted 6 g)
  · change natFamilyRankForm k307COMDescendantFamily k307COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 7 f) (natOrbitalComponent 7 g)
    rw [← natFamilyRankForm_orbitalComponent k307COMDescendantFamily
      k307COMRankCoefficient (natCOMBasis_column_weighted k307occ
        k307_particle_degree k307_orbital_degree (complexify k307COMBasis)
        k307COMDescendantFamily k307_COMDescendantFamily_column) f g]
    exact k307_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 7 f hNf) (natOrbitalComponent_weighted 7 f)
      (natOrbitalComponent_particle 3 7 g hNg) (natOrbitalComponent_weighted 7 g)
  · change natFamilyRankForm k308COMDescendantFamily k308COMRankCoefficient f g =
      canonicalNatOriginalM3Form (natOrbitalComponent 8 f) (natOrbitalComponent 8 g)
    rw [← natFamilyRankForm_orbitalComponent k308COMDescendantFamily
      k308COMRankCoefficient (natCOMBasis_column_weighted k308occ
        k308_particle_degree k308_orbital_degree (complexify k308COMBasis)
        k308COMDescendantFamily k308_COMDescendantFamily_column) f g]
    exact k308_COM_originalM3_rank_form _ _
      (natOrbitalComponent_particle 3 8 f hNf) (natOrbitalComponent_weighted 8 f)
      (natOrbitalComponent_particle 3 8 g hNg) (natOrbitalComponent_weighted 8 g)

/-- Original M3 on arbitrary finite N3 inputs equals the actual finite rank kernel.
No lowering-vacuum, degree-cutoff or coefficient-span premise remains. -/
theorem canonicalNatOriginalM3Form_fullN3_rank_sum (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatOriginalM3Form f g = ∑ d : Fin 9, natCOMOriginalM3RankBlock d f g := by
  rw [canonicalNatOriginalM3Form_fullN3_finite_blocks f g hNf hNg]
  symm
  calc
    _ = ∑ d : Fin 9, canonicalNatOriginalM3Form
        (natOrbitalComponent d.val f) (natOrbitalComponent d.val g) := by
      apply Finset.sum_congr rfl
      intro d _
      exact natCOMOriginalM3RankBlock_eq_component d f g hNf hNg
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun d : ℕ => canonicalNatOriginalM3Form (natOrbitalComponent d f)
        (natOrbitalComponent d g)) 9

#print axioms natFamilyAnalysis_orbitalComponent
#print axioms natFamilyRankForm_orbitalComponent
#print axioms natCOMOriginalM3RankBlock_eq_component
#print axioms canonicalNatOriginalM3Form_fullN3_rank_sum
end TorusLean.BosonFiniteCertificate
