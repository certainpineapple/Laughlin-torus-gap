import torus.shared.ThermalCoherentBosonRowRankSource
import torus.shared.ThermalCoherentBosonRowSourceTransport
import torus.shared.BosonFiniteCertificateNatCOMBasisFullRank
import torus.shared.BosonNatThreeActualCOMCellLift

/-! Original M3 source coefficients, separated by genuine finite occupation
Riesz tests and transported through the actual full-core annihilator. The
original canonical row form is used, rather than an assumed physical lift
identity. No periodization isometry or independence of source images enters. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowOriginalThree
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowSourceTransport
open TorusLean.Shared.BosonNatThreeActualCOMCellLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.M2 Matrix
open scoped BigOperators
local instance originalThree_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem sum_three (F : Fin 3 → ℂ) : (∑ i, F i)=F 0+F 1+F 2 := by
  simp [Fin.sum_univ_succ,add_assoc]

private abbrev SourceIndex := RowIndex × Fin 9 × Fin 3
private def sourceLeft (z : SourceIndex) : Core ℕ ℂ :=
  if z.2.2=0 then rowThreePairSeed z.1 z.2.1 else rowThreeAuxiliarySeed z.1 z.2.1
private def sourceRight (z : SourceIndex) : Core ℕ ℂ :=
  if z.2.2=1 then rowThreePairSeed z.1 z.2.1 else rowThreeAuxiliarySeed z.1 z.2.1

private theorem sourceLeft_particle (z : SourceIndex) : (sourceLeft z).IsHomogeneous 3 := by
  unfold sourceLeft
  split_ifs <;> first | exact rowThreePairSeed_sector _ _ | exact rowThreeAuxiliarySeed_sector _ _
private theorem sourceRight_particle (z : SourceIndex) : (sourceRight z).IsHomogeneous 3 := by
  unfold sourceRight
  split_ifs <;> first | exact rowThreePairSeed_sector _ _ | exact rowThreeAuxiliarySeed_sector _ _

private theorem source_dyad_sum (B : Core ℕ ℂ → Core ℕ ℂ → ℂ) :
    (∑ z : SourceIndex, B (sourceLeft z) (sourceRight z)) =
      ∑ ρ : RowIndex,
        ((∑ i : Fin 9, B (rowThreePairSeed ρ i) (rowThreeAuxiliarySeed ρ i)) +
        (∑ i : Fin 9, B (rowThreeAuxiliarySeed ρ i) (rowThreePairSeed ρ i)) +
        ∑ i : Fin 9, B (rowThreeAuxiliarySeed ρ i) (rowThreeAuxiliarySeed ρ i)) := by
  simp only [SourceIndex,Fintype.sum_prod_type,sum_three,sourceLeft,sourceRight]
  norm_num [Finset.sum_add_distrib]

private abbrev OriginalIndex := (Fin 1 × Fin 1) ⊕ (Fin 1 × Fin 1) ⊕ (Fin 2 × Fin 2) ⊕ (Fin 3 × Fin 3) ⊕ (Fin 4 × Fin 4) ⊕ (Fin 5 × Fin 5) ⊕ (Fin 7 × Fin 7) ⊕ (Fin 8 × Fin 8) ⊕ (Fin 10 × Fin 10)

private def originalLeft : OriginalIndex → Core ℕ ℂ :=
  Sum.elim (fun ij : Fin 1 × Fin 1 => k300COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 1 × Fin 1 => k301COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 2 × Fin 2 => k302COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 3 × Fin 3 => k303COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 4 × Fin 4 => k304COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 5 × Fin 5 => k305COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 7 × Fin 7 => k306COMDescendantFamily ij.1) (Sum.elim (fun ij : Fin 8 × Fin 8 => k307COMDescendantFamily ij.1) (fun ij : Fin 10 × Fin 10 => k308COMDescendantFamily ij.1))))))))

private def originalRight : OriginalIndex → Core ℕ ℂ :=
  Sum.elim (fun ij : Fin 1 × Fin 1 => k300COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 1 × Fin 1 => k301COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 2 × Fin 2 => k302COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 3 × Fin 3 => k303COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 4 × Fin 4 => k304COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 5 × Fin 5 => k305COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 7 × Fin 7 => k306COMDescendantFamily ij.2) (Sum.elim (fun ij : Fin 8 × Fin 8 => k307COMDescendantFamily ij.2) (fun ij : Fin 10 × Fin 10 => k308COMDescendantFamily ij.2))))))))

private def originalCoefficient : OriginalIndex → ℂ :=
  Sum.elim (fun ij : Fin 1 × Fin 1 => k300COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 1 × Fin 1 => k301COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 2 × Fin 2 => k302COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 3 × Fin 3 => k303COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 4 × Fin 4 => k304COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 5 × Fin 5 => k305COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 7 × Fin 7 => k306COMRankCoefficient ij.1 ij.2) (Sum.elim (fun ij : Fin 8 × Fin 8 => k307COMRankCoefficient ij.1 ij.2) (fun ij : Fin 10 × Fin 10 => k308COMRankCoefficient ij.1 ij.2))))))))

private theorem original_0_particle (i : Fin 1) :
    (k300COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k300occ k300_particle_degree (complexify k300COMBasis)
    k300COMDescendantFamily k300_COMDescendantFamily_column i

private theorem original_1_particle (i : Fin 1) :
    (k301COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k301occ k301_particle_degree (complexify k301COMBasis)
    k301COMDescendantFamily k301_COMDescendantFamily_column i

private theorem original_2_particle (i : Fin 2) :
    (k302COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k302occ k302_particle_degree (complexify k302COMBasis)
    k302COMDescendantFamily k302_COMDescendantFamily_column i

private theorem original_3_particle (i : Fin 3) :
    (k303COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k303occ k303_particle_degree (complexify k303COMBasis)
    k303COMDescendantFamily k303_COMDescendantFamily_column i

private theorem original_4_particle (i : Fin 4) :
    (k304COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k304occ k304_particle_degree (complexify k304COMBasis)
    k304COMDescendantFamily k304_COMDescendantFamily_column i

private theorem original_5_particle (i : Fin 5) :
    (k305COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k305occ k305_particle_degree (complexify k305COMBasis)
    k305COMDescendantFamily k305_COMDescendantFamily_column i

private theorem original_6_particle (i : Fin 7) :
    (k306COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k306occ k306_particle_degree (complexify k306COMBasis)
    k306COMDescendantFamily k306_COMDescendantFamily_column i

private theorem original_7_particle (i : Fin 8) :
    (k307COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k307occ k307_particle_degree (complexify k307COMBasis)
    k307COMDescendantFamily k307_COMDescendantFamily_column i

private theorem original_8_particle (i : Fin 10) :
    (k308COMDescendantFamily i).IsHomogeneous 3 :=
  actual_COM_family_particle k308occ k308_particle_degree (complexify k308COMBasis)
    k308COMDescendantFamily k308_COMDescendantFamily_column i

private theorem originalLeft_particle (z : OriginalIndex) :
    (originalLeft z).IsHomogeneous 3 := by
  rcases z with z | z | z | z | z | z | z | z | z
  · exact original_0_particle z.1
  · exact original_1_particle z.1
  · exact original_2_particle z.1
  · exact original_3_particle z.1
  · exact original_4_particle z.1
  · exact original_5_particle z.1
  · exact original_6_particle z.1
  · exact original_7_particle z.1
  · exact original_8_particle z.1

private theorem originalRight_particle (z : OriginalIndex) :
    (originalRight z).IsHomogeneous 3 := by
  rcases z with z | z | z | z | z | z | z | z | z
  · exact original_0_particle z.2
  · exact original_1_particle z.2
  · exact original_2_particle z.2
  · exact original_3_particle z.2
  · exact original_4_particle z.2
  · exact original_5_particle z.2
  · exact original_6_particle z.2
  · exact original_7_particle z.2
  · exact original_8_particle z.2

private theorem original_dyad_sum (B : Core ℕ ℂ → Core ℕ ℂ → ℂ) :
    (∑ z : OriginalIndex, originalCoefficient z * B (originalLeft z) (originalRight z)) =
      (∑ i, ∑ j, k300COMRankCoefficient i j * B (k300COMDescendantFamily i) (k300COMDescendantFamily j)) +
      (∑ i, ∑ j, k301COMRankCoefficient i j * B (k301COMDescendantFamily i) (k301COMDescendantFamily j)) +
      (∑ i, ∑ j, k302COMRankCoefficient i j * B (k302COMDescendantFamily i) (k302COMDescendantFamily j)) +
      (∑ i, ∑ j, k303COMRankCoefficient i j * B (k303COMDescendantFamily i) (k303COMDescendantFamily j)) +
      (∑ i, ∑ j, k304COMRankCoefficient i j * B (k304COMDescendantFamily i) (k304COMDescendantFamily j)) +
      (∑ i, ∑ j, k305COMRankCoefficient i j * B (k305COMDescendantFamily i) (k305COMDescendantFamily j)) +
      (∑ i, ∑ j, k306COMRankCoefficient i j * B (k306COMDescendantFamily i) (k306COMDescendantFamily j)) +
      (∑ i, ∑ j, k307COMRankCoefficient i j * B (k307COMDescendantFamily i) (k307COMDescendantFamily j)) +
      (∑ i, ∑ j, k308COMRankCoefficient i j * B (k308COMDescendantFamily i) (k308COMDescendantFamily j)) := by
  simp only [OriginalIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,
    originalCoefficient,originalLeft,originalRight,Sum.elim_inl,Sum.elim_inr,add_assoc]

private theorem canonical_original_nine (f g : Core ℕ ℂ)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    canonicalNatOriginalM3Form f g =
      natFamilyRankForm k300COMDescendantFamily k300COMRankCoefficient f g +
      natFamilyRankForm k301COMDescendantFamily k301COMRankCoefficient f g +
      natFamilyRankForm k302COMDescendantFamily k302COMRankCoefficient f g +
      natFamilyRankForm k303COMDescendantFamily k303COMRankCoefficient f g +
      natFamilyRankForm k304COMDescendantFamily k304COMRankCoefficient f g +
      natFamilyRankForm k305COMDescendantFamily k305COMRankCoefficient f g +
      natFamilyRankForm k306COMDescendantFamily k306COMRankCoefficient f g +
      natFamilyRankForm k307COMDescendantFamily k307COMRankCoefficient f g +
      natFamilyRankForm k308COMDescendantFamily k308COMRankCoefficient f g := by
  have h := canonicalNatOriginalM3Form_fullN3_rank_sum f g hf hg
  simpa only [natCOMOriginalM3RankBlock,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,add_assoc] using h

private theorem original_source_rank_identity (f g : Core ℕ ℂ)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    (∑ z : SourceIndex, (1:ℂ) * star (natOccupationInner (sourceLeft z) f) *
      natOccupationInner (sourceRight z) g) =
      ∑ z : OriginalIndex, originalCoefficient z * star (natOccupationInner (originalLeft z) f) *
        natOccupationInner (originalRight z) g := by
  simp only [one_mul,mul_assoc]
  rw [source_dyad_sum (fun p q => star (natOccupationInner p f)*natOccupationInner q g),
    original_dyad_sum (fun p q => star (natOccupationInner p f)*natOccupationInner q g)]
  change (∑ ρ : RowIndex, rowRankThreeForm ρ f g) = _
  rw [←canonicalNatOriginalM3Form_rank_source f g hf hg,canonical_original_nine f g hf hg]
  simp only [natFamilyRankForm_eq_sum,mul_assoc]

/-- Complete COM-family cross form with each original rank coefficient retained. -/
def originalM3COMCross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  ∑ z : OriginalIndex, originalCoefficient z *
    ip (natThreeAnnihilator G theta R (originalLeft z) f)
      (natThreeAnnihilator G theta R (originalRight z) g)

/-- Genuine original M3 coefficient identity on all physical polynomial cores.
The N3 restriction is used only after finite Riesz separation, so no allN
operator identity is taken as an extra premise. -/
theorem actualRows_three_original_cross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ ρ : RowIndex, actualRowThreeCross G theta ρ R f g) = originalM3COMCross G theta R f g := by
  have h := finite_source_form_actual_cross G theta sourceLeft sourceRight
    originalLeft originalRight (fun _ => (1:ℂ)) originalCoefficient
    sourceLeft_particle sourceRight_particle originalLeft_particle originalRight_particle
    original_source_rank_identity R f g
  simp only [one_mul] at h
  rw [source_dyad_sum (fun p q => ip (natThreeAnnihilator G theta R p f)
    (natThreeAnnihilator G theta R q g))] at h
  simpa only [actualRowThreeCross_eq_source,originalM3COMCross] using h

/-- Expanded endpoint keeps all nine original full descendant matrices. -/
theorem originalM3COMCross_eq_nine (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    originalM3COMCross G theta R f g =
      (∑ i, ∑ j, k300COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k300COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k300COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k301COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k301COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k301COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k302COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k302COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k302COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k303COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k303COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k303COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k304COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k304COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k304COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k305COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k305COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k305COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k306COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k306COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k306COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k307COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k307COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k307COMDescendantFamily j) g)) +
      (∑ i, ∑ j, k308COMRankCoefficient i j * ip (natThreeAnnihilator G theta R (k308COMDescendantFamily i) f) (natThreeAnnihilator G theta R (k308COMDescendantFamily j) g)) := by
  exact original_dyad_sum (fun p q => ip (natThreeAnnihilator G theta R p f)
    (natThreeAnnihilator G theta R q g))

end TorusLean.Shared.ThermalCoherentBosonRowOriginalThree
