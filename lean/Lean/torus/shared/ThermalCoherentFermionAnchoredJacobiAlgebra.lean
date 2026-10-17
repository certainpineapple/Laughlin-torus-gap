import torus.shared.ThermalCoherentFermionAnchoredJacobiInsertion
import torus.shared.ThermalCoherentJacobiWeights

/-! The actual finite two-column fermion Jacobi expansion. All source vectors
are images of an explicit finite marked polynomial under exterior insertion.
The diagonal coefficient comes from a differential identity. No spectral or
orthogonality hypothesis is supplied, and the insertion can have a kernel. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentJacobiWeights
open scoped BigOperators

/-- Normalized marked Jacobi column in the *actual* Nat exterior source.
Identification with unbounded COM descendants is a subsequent interface. -/
def formalJacobiColumn (n d : ℕ) : FormalExterior :=
  ((Real.sqrt ((3:ℝ)^n*(n.factorial:ℝ)):ℂ)⁻¹ *
    (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹) •
      fermionMarkedW3 (fermionMarkedCOM^n*fermionMarkedRelative^d)

def fermionAnchorJacobiAmplitude (n d : ℕ) : ℝ :=
  (-1:ℝ)^d * jacobiAmplitude n d

def fermionConnectedJacobiAmplitude (n d : ℕ) : ℝ :=
  (3*(d:ℝ)-1) / (2:ℝ)^d * jacobiAmplitude n d

theorem markedFermionPair_inverse : markedPair =
    (3:ℂ)⁻¹ • (fermionMarkedRelative+(2:ℂ) • fermionMarkedCOM) := by
  simp only [fermionMarkedCOM,fermionMarkedRelative]
  module

theorem markedFermionSpectator_inverse : markedSpectator =
    (3:ℂ)⁻¹ • (-fermionMarkedRelative+fermionMarkedCOM) := by
  simp only [fermionMarkedCOM,fermionMarkedRelative]
  module

theorem markedFermionPair_power (l : ℕ) :
    markedPair^l = (3:ℂ)⁻¹^l •
      ∑ d ∈ Finset.range (l+1), ((l.choose d:ℂ)*(2:ℂ)^(l-d)) •
        (fermionMarkedCOM^(l-d)*fermionMarkedRelative^d) := by
  rw [markedFermionPair_inverse,smul_pow,add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [smul_pow,MvPolynomial.smul_eq_C_mul,map_mul,map_natCast,map_pow,map_ofNat]
  ring

theorem markedFermionSpectator_power (l : ℕ) :
    markedSpectator^l = (3:ℂ)⁻¹^l •
      ∑ d ∈ Finset.range (l+1), ((l.choose d:ℂ)*(-1:ℂ)^d) •
        (fermionMarkedCOM^(l-d)*fermionMarkedRelative^d) := by
  rw [markedFermionSpectator_inverse,smul_pow,add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [neg_pow]
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_natCast,map_pow,map_neg,map_one]
  ring

private theorem fermionMarkedEuler_sum {I : Type*} (s : Finset I)
    (f : I → FermionMarkedOscillator) :
    fermionMarkedEuler (∑ i∈s, f i)=∑ i∈s, fermionMarkedEuler (f i) := by
  simp only [fermionMarkedEuler,map_sum,Finset.mul_sum,Finset.sum_sub_distrib]

private theorem fermionMarkedEuler_smul (c : ℂ) (f : FermionMarkedOscillator) :
    fermionMarkedEuler (c • f)=c • fermionMarkedEuler f := by
  simp only [fermionMarkedEuler,map_smul,mul_smul_comm,smul_sub]

/-- The second polynomial is obtained from the first pair power by the
proved differential operator; its eigenvalues are not inserted by definition. -/
theorem markedFermionConnected_power (l : ℕ) :
    fermionMarkedEuler (markedPair^l) = (3:ℂ)⁻¹^l •
      ∑ d ∈ Finset.range (l+1),
        ((l.choose d:ℂ)*(2:ℂ)^(l-d)*(3*(d:ℂ)-1)) •
          (fermionMarkedCOM^(l-d)*fermionMarkedRelative^d) := by
  rw [markedFermionPair_power,fermionMarkedEuler_smul,fermionMarkedEuler_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [fermionMarkedEuler_smul,fermionMarkedEuler_jacobi,smul_smul]

private theorem fermionJacobi_normalization (l d : ℕ) (hd : d≤l) :
    (jacobiAmplitude (l-d) d:ℂ) *
      ((Real.sqrt ((3:ℝ)^(l-d)*((l-d).factorial:ℝ)):ℂ)⁻¹ *
       (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹) =
      (Real.sqrt (l.factorial:ℝ):ℂ)⁻¹*(3:ℂ)⁻¹^l*(l.choose d:ℂ) := by
  have h3 : (Real.sqrt ((3:ℝ)^(l-d)*((l-d).factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h6 : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hl : (Real.sqrt (l.factorial:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  simp only [jacobiAmplitude,Nat.sub_add_cancel hd,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,inv_pow]
  field_simp [h3,h6,hl]
  <;> ring

/-- Original v_0 wedge e_l, with the correct (-1)^d Jacobi sign. -/
theorem formalAnchoredSeed_jacobi (l : ℕ) :
    formalAnchoredSeed l = ∑ d ∈ Finset.range (l+1),
      (fermionAnchorJacobiAmplitude (l-d) d:ℂ) • formalJacobiColumn (l-d) d := by
  rw [formalAnchoredSeed_eq_marked,markedFermionSpectator_power,map_smul,map_sum]
  simp only [Finset.smul_sum,map_smul,formalJacobiColumn,smul_smul]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d≤l := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  congr 1
  simp only [fermionAnchorJacobiAmplitude,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]
  calc
    _ = (-1:ℂ)^d*((Real.sqrt (l.factorial:ℝ):ℂ)⁻¹*(3:ℂ)⁻¹^l*(l.choose d:ℂ)) := by ring
    _ = _ := by rw [← fermionJacobi_normalization l d hle]; ring

/-- The exact second column has coefficient (3d−1)2^(−d), derived from
both original CAR contractions, rather than an assumed relative eigenvector. -/
theorem formalConnectedAnchoredSeed_jacobi (l : ℕ) :
    formalConnectedAnchoredSeed l = ∑ d ∈ Finset.range (l+1),
      (fermionConnectedJacobiAmplitude (l-d) d:ℂ) • formalJacobiColumn (l-d) d := by
  rw [formalConnectedAnchoredSeed,markedFermionConnected_power,map_smul,map_sum]
  simp only [Finset.smul_sum,map_smul,formalJacobiColumn,smul_smul]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d≤l := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  have hl : (Real.sqrt (l.factorial:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hpow : (2:ℂ)^l=(2:ℂ)^(l-d)*(2:ℂ)^d := by
    rw [← pow_add,Nat.sub_add_cancel hle]
  congr 1
  simp only [fermionConnectedJacobiAmplitude,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  calc
    _ = ((3*(d:ℂ)-1)/(2:ℂ)^d) *
        ((Real.sqrt (l.factorial:ℝ):ℂ)⁻¹*(3:ℂ)⁻¹^l*(l.choose d:ℂ)) := by
      rw [hpow]
      field_simp [hl]
      <;> ring
    _ = _ := by rw [← fermionJacobi_normalization l d hle]; ring

end TorusLean.Shared.ThermalCoherentFermionAnchored
