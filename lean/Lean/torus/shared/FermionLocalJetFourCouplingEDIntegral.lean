import torus.shared.FermionLocalJetFourCouplingFullIntegral
import torus.shared.FermionLocalJetFourCouplingDegreeReindex
import torus.shared.FermionLocalJetFourCouplingOriginalCOMIntegral

/-! Original ordered rows, both full Gamma factors and the actual COM cell
integral recombine into the original E_D definition. No diagonal-copy or
positivity assumption is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open scoped BigOperators ComplexConjugate

def groundFourUnitIntegral (G : Geometry) (theta : Twist)
    (u v : FourCopy) (x : Space (physicalQ G theta)) : ℂ :=
  ∫ R, occupationInner (physicalQ G theta)
    (coupledFourAmplitude G theta (u.1.val+1) u.2 R x)
    (coupledFourAmplitude G theta (v.1.val+1) v.2 R x) ∂cellMeasure G 2

def rowFourCoefficient (rho : CertificateRow) (a b : CertificateEntry rho)
    (u v : FourCopy) : ℂ :=
  (certificateAlpha rho a:ℂ)*(certificateAlpha rho b:ℂ)*
    paperS45 u.2.val.val (u.1.val+1) (certificateFourTotal rho a b)
      (certificateEntryData rho a).1 (certificateEntryData rho a).2.1 (certificateJetIndex rho b)*
    paperS45 v.2.val.val (v.1.val+1) (certificateFourTotal rho a b)
      (certificateEntryData rho b).1 (certificateEntryData rho b).2.1 (certificateJetIndex rho a)

theorem fullFourDescendantUnit_cell (G : Geometry) (theta : Twist)
    (T : ℕ) (hT : T≤23) (c e : HalfInputIndex T) (x : Space (physicalQ G theta)) :
    (∫ R, fullFourDescendantUnit G theta T c e R x ∂cellMeasure G 2) =
      if (fullCopyToBelow T hT c).val.1=(fullCopyToBelow T hT e).val.1 then
        groundFourUnitIntegral G theta (fullCopyToBelow T hT c).val
          (fullCopyToBelow T hT e).val x else 0 := by
  have h := original_fullT_mixed_cell G theta ⟨T,by omega⟩
    (fullCopyToBelow T hT c).val.1 (fullCopyToBelow T hT e).val.1
    (fullCopyToBelow T hT c).val.2 (fullCopyToBelow T hT e).val.2
    (fullCopyToBelow T hT c).property (fullCopyToBelow T hT e).property x x
  simpa only [fullFourDescendantUnit,groundFourUnitIntegral,
    fullCopyToBelow_degree,fullCopyToBelow_relative] using h

/-- One ordered row-entry pair, with its complete two-sided coupling matrix. -/
theorem original_row_COM_reindex (G : Geometry) (theta : Twist)
    (rho : CertificateRow) (a b : CertificateEntry rho) (x : Space (physicalQ G theta)) :
    (∑ c : HalfInputIndex (certificateFourTotal rho a b),
      ∑ e : HalfInputIndex (certificateFourTotal rho a b),
        fullFourCoupledCoefficient rho a b c e *
          (∫ R, fullFourDescendantUnit G theta (certificateFourTotal rho a b) c e R x
            ∂cellMeasure G 2)) =
    ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      if d.val+1≤certificateFourTotal rho a b then
        rowFourCoefficient rho a b ⟨d,r⟩ ⟨d,s⟩ *
          groundFourUnitIntegral G theta ⟨d,r⟩ ⟨d,s⟩ x else 0 := by
  classical
  simp_rw [fullFourDescendantUnit_cell G theta _ (certificateFourTotal_le rho a b),
    mul_ite,mul_zero]
  have h := fullCopy_double_sum_degree_diagonal (certificateFourTotal rho a b)
    (certificateFourTotal_le rho a b)
    (fun u v => rowFourCoefficient rho a b u v * groundFourUnitIntegral G theta u v x)
  simpa only [rowFourCoefficient,fullFourCoupledCoefficient,
    fullCopyToBelow_degree,fullCopyToBelow_relative] using h

/-- Finite dependent Fubini with every original ordered a,b and every r,s. -/
theorem original_rows_degree_fubini
    (F : (rho : CertificateRow) → CertificateEntry rho → CertificateEntry rho →
      (d : Fin 23) → OddMode (d.val+1) → OddMode (d.val+1) → ℂ) :
    (∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
      ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1), F rho a b d r s) =
    ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      ∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        F rho a b d r s := by
  classical
  let A := (rho : CertificateRow) × (CertificateEntry rho × CertificateEntry rho)
  let B := (d : Fin 23) × (OddMode (d.val+1) × OddMode (d.val+1))
  have h : (∑ a : A, ∑ b : B, F a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2) =
      ∑ b : B, ∑ a : A, F a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2 := Finset.sum_comm
  simpa only [A,B,Fintype.sum_sigma,Fintype.sum_prod_type] using h

/-- The ordered negative coefficient is exactly the previously defined E_D. -/
theorem original_integrated_rows_eq_ED (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    -(∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
      ∑ c : HalfInputIndex (certificateFourTotal rho a b),
      ∑ e : HalfInputIndex (certificateFourTotal rho a b),
        fullFourCoupledCoefficient rho a b c e *
          (∫ R, fullFourDescendantUnit G theta (certificateFourTotal rho a b) c e R x
            ∂cellMeasure G 2)) =
    ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      certificateFourMatrix (d.val+1) r.val.val s.val.val *
        groundFourUnitIntegral G theta ⟨d,r⟩ ⟨d,s⟩ x := by
  classical
  simp_rw [original_row_COM_reindex G theta]
  rw [original_rows_degree_fubini]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [certificateFourMatrix,neg_mul,Finset.sum_mul,ite_mul,zero_mul,rowFourCoefficient]


/-- Finite Bochner sums and real part are exchanged only after the actual
matrix units have been proved integrable on the original cell measure. -/
theorem certificateFourEnergy_eq_integrated_rows (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x =
      (-(∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        ∑ c : HalfInputIndex (certificateFourTotal rho a b),
        ∑ e : HalfInputIndex (certificateFourTotal rho a b),
          fullFourCoupledCoefficient rho a b c e *
            (∫ R, fullFourDescendantUnit G theta (certificateFourTotal rho a b) c e R x
              ∂cellMeasure G 2))).re := by
  classical
  let F (rho : CertificateRow) (a b : CertificateEntry rho)
      (c e : HalfInputIndex (certificateFourTotal rho a b)) (R : ℂ) :=
    fullFourCoupledCoefficient rho a b c e *
      fullFourDescendantUnit G theta (certificateFourTotal rho a b) c e R x
  have hi (rho : CertificateRow) (a b : CertificateEntry rho)
      (c e : HalfInputIndex (certificateFourTotal rho a b)) :
      Integrable (F rho a b c e) (cellMeasure G 2) :=
    (fullFourDescendantUnit_integrable G theta _ 2 c e x).const_mul _
  let H (R : ℂ) := -(∑ rho : CertificateRow, ∑ a : CertificateEntry rho,
    ∑ b : CertificateEntry rho, ∑ c : HalfInputIndex (certificateFourTotal rho a b),
    ∑ e : HalfInputIndex (certificateFourTotal rho a b), F rho a b c e R)
  have hH : Integrable H (cellMeasure G 2) :=
    (integrable_finsetSum _ (fun rho _ => integrable_finsetSum _ (fun a _ =>
      integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ =>
        integrable_finsetSum _ (fun e _ => hi rho a b c e)))))).neg
  have hc : (∫ R, H R ∂cellMeasure G 2) =
      -(∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        ∑ c : HalfInputIndex (certificateFourTotal rho a b),
        ∑ e : HalfInputIndex (certificateFourTotal rho a b),
          fullFourCoupledCoefficient rho a b c e *
            (∫ R, fullFourDescendantUnit G theta (certificateFourTotal rho a b) c e R x
              ∂cellMeasure G 2)) := by
    unfold H
    rw [integral_neg,integral_finsetSum _ (fun rho _ =>
      integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
        integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun e _ => hi rho a b c e)))))]
    congr 1
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
      integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun e _ => hi rho a b c e))))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ =>
      integrable_finsetSum _ (fun e _ => hi rho a b c e)))]
    apply Finset.sum_congr rfl
    intro b hb
    rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun e _ => hi rho a b c e))]
    apply Finset.sum_congr rfl
    intro c hcc
    rw [integral_finsetSum _ (fun e _ => hi rho a b c e)]
    apply Finset.sum_congr rfl
    intro e he
    exact integral_const_mul _ _
  calc
    _ = ∫ R, (H R).re ∂cellMeasure G 2 := by
      rw [certificateFourEnergy_eq_full_coupled_integral G theta x]
      apply integral_congr_ae
      filter_upwards [] with R
      simp only [H,F,Complex.re_sum,Complex.neg_re,Finset.sum_neg_distrib]
    _ = (∫ R, H R ∂cellMeasure G 2).re := integral_re hH
    _ = _ := congrArg Complex.re hc

/-- Exact original K4 as the full E_D matrix integral, for all whole-Fock x.
The signed matrix is the original independently defined F-E expression. -/
theorem certificateFourEnergy_eq_ED_integrals (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x =
      (∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
        certificateFourMatrix (d.val+1) r.val.val s.val.val *
          groundFourUnitIntegral G theta ⟨d,r⟩ ⟨d,s⟩ x).re := by
  rw [certificateFourEnergy_eq_integrated_rows G theta x,
    original_integrated_rows_eq_ED G theta x]


end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.fullFourDescendantUnit_cell
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_row_COM_reindex
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_rows_degree_fubini
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_integrated_rows_eq_ED
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.certificateFourEnergy_eq_integrated_rows
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.certificateFourEnergy_eq_ED_integrals
