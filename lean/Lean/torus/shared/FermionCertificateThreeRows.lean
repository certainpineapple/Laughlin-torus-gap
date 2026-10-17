import torus.shared.FermionCertificateThreeInsertion
import torus.shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
import torus.shared.FermionLocalJetNormalOrder

/-! Original seven-row physical outputs at fixed auxiliary index i.
The total input degree is exactly T=i+t, including each lambda-cross input.
All physical substitutions use actual CAR removal of the full exterior source. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open scoped BigOperators ComplexConjugate

def coupledThreeRemoval (G : Geometry) (theta : Twist) (T : ℕ) (z : Fin (T+1))
    (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  formalRemoval G theta R (formalJacobiColumn (T-z.val) z.val) x

/-- Full inverse source transform applied to the genuine c_j B_p. -/
theorem localTriple_full_coupling (G : Geometry) (theta : Twist) (T p j : ℕ)
    (hT : p+j=T) (R : ℂ) (x : Space (physicalQ G theta)) :
    localJetAnnihilate G theta j R (pairDescendant G theta p R x)=
      ∑ z : Fin (T+1), (sThree z.val T p:ℂ) • coupledThreeRemoval G theta T z R x := by
  let p' : Fin (T+1) := ⟨p,by omega⟩
  have hj : T-p=j := by omega
  have he := congrArg (fun v => formalRemoval G theta R v x)
    (formalThreeSeed_full_coupling T p')
  simp only [formalRemoval_sum_smul,formalRemoval_three,Complex.conj_ofReal,
    p',hj,coupledThreeRemoval] at he
  exact he

def degreeRowOutput (G : Geometry) (theta : Twist) (r : CertificateRow)
    (T : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  ∑ a : CertificateEntry r,
    if (certificateEntryData r a).1+(certificateEntryData r a).2.1=T then
      (certificateAlpha r a:ℂ) • certificateAmplitude G theta r a R x
    else 0

/-- The original grouped auxiliary index equals total input degree minus t. -/
theorem certificate_entry_degree_iff (r : CertificateRow) (a : CertificateEntry r)
    (i : Fin 9) :
    certificateEntryJet r a=i ↔
      (certificateEntryData r a).1+(certificateEntryData r a).2.1=
        (certificateRowData r).1+i.val := by
  have hs := certificate_row_support r a
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [certificateEntryJet,certificateJetIndex] at hv
    omega
  · intro h
    apply Fin.ext
    change certificateJetIndex r a=i.val
    unfold certificateJetIndex
    omega

/-- Exact original row output, not a new row definition substituted by fiat. -/
theorem certificateRowOutput_eq_degree (G : Geometry) (theta : Twist)
    (r : CertificateRow) (i : Fin 9) (R : ℂ) (x : Space (physicalQ G theta)) :
    certificateRowOutput G theta r R x i=
      degreeRowOutput G theta r ((certificateRowData r).1+i.val) R x := by
  unfold certificateRowOutput degreeRowOutput
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [certificate_entry_degree_iff]

/-- Each full original row is transformed at fixed T, with all entries retained. -/
theorem degreeRowOutput_coupled (G : Geometry) (theta : Twist)
    (r : CertificateRow) (T : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    degreeRowOutput G theta r T R x=
      ∑ z : Fin (T+1), (rowCoupledCoefficient r z.val T:ℂ) •
        coupledThreeRemoval G theta T z R x := by
  classical
  have he (a : CertificateEntry r) :
      (if (certificateEntryData r a).1+(certificateEntryData r a).2.1=T then
        (certificateAlpha r a:ℂ) • certificateAmplitude G theta r a R x else 0)=
      ∑ z : Fin (T+1),
        (if (certificateEntryData r a).1+(certificateEntryData r a).2.1=T then
          (certificateAlpha r a:ℂ)*(sThree z.val T (certificateEntryData r a).1:ℂ)
        else 0) • coupledThreeRemoval G theta T z R x := by
    by_cases hT : (certificateEntryData r a).1+(certificateEntryData r a).2.1=T
    · simp only [if_pos hT,certificateAmplitude]
      rw [localTriple_full_coupling G theta T _ _ hT]
      simp only [Finset.smul_sum,smul_smul]
    · simp only [if_neg hT,zero_smul,Finset.sum_const_zero]
  unfold degreeRowOutput
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_smul]
  congr 1
  unfold rowCoupledCoefficient
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hT : (certificateEntryData r a).1+(certificateEntryData r a).2.1=T
  <;> simp [hT]

/-- Lambda-cross input has precisely the same total degree T=t+i. -/
theorem certificateLambdaInput_coupled (G : Geometry) (theta : Twist)
    (r : CertificateRow) (i : Fin 9) (R : ℂ) (x : Space (physicalQ G theta)) :
    localJetAnnihilate G theta i.val R (pairDescendant G theta (certificateRowData r).1 R x)=
      ∑ z : Fin ((certificateRowData r).1+i.val+1),
        (sThree z.val ((certificateRowData r).1+i.val) (certificateRowData r).1:ℂ) •
          coupledThreeRemoval G theta ((certificateRowData r).1+i.val) z R x :=
  localTriple_full_coupling G theta _ _ _ rfl R x

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
