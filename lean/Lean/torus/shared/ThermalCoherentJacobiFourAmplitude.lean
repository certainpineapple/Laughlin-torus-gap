import torus.shared.ThermalCoherentJacobiFourWeights

/-! Exact normalization of the second, equal-charge W4 Jacobi step. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourWeights
open TorusLean.Shared.ThermalCoherentMoments

/-- Unsigned amplitude for spectator-COM level n+e into COM n and relative e.
The inverse coordinate has a minus sign, retained separately below. -/
def fourJacobiAmplitude (n e : ℕ) : ℝ :=
  ((n+e).choose e:ℝ) * Real.sqrt ((4:ℝ)^e*(e.factorial:ℝ)) *
    Real.sqrt ((4:ℝ)^n*(n.factorial:ℝ)) /
      ((2:ℝ)^(n+e)*Real.sqrt ((2:ℝ)^(n+e)*((n+e).factorial:ℝ)))

def fourSignedAmplitude (n e : ℕ) : ℝ := (-1:ℝ)^e * fourJacobiAmplitude n e

theorem fourJacobiAmplitude_nonneg (n e : ℕ) : 0≤fourJacobiAmplitude n e := by
  unfold fourJacobiAmplitude
  positivity

theorem fourJacobiAmplitude_sq (n e : ℕ) :
    (fourJacobiAmplitude n e)^2=((n+e).choose e:ℝ)*(1/2:ℝ)^(n+e) := by
  have hf : ((n+e).choose e:ℝ)*(e.factorial:ℝ)*(n.factorial:ℝ)=((n+e).factorial:ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n e
    have hc : ((n+e).choose e:ℝ)*(n.factorial:ℝ)*(e.factorial:ℝ)=((n+e).factorial:ℝ) := by
      exact_mod_cast h
    simpa only [mul_right_comm] using hc
  have hnum : ((n+e).choose e:ℝ)^2*((4:ℝ)^e*(e.factorial:ℝ))*
      ((4:ℝ)^n*(n.factorial:ℝ)) =
        ((n+e).choose e:ℝ)*((n+e).factorial:ℝ)*(4:ℝ)^(n+e) := by
    rw [pow_add]
    calc
      _ = (((n+e).choose e:ℝ)*(e.factorial:ℝ)*(n.factorial:ℝ))*
        ((n+e).choose e:ℝ)*(4:ℝ)^n*(4:ℝ)^e := by ring
      _ = _ := by rw [hf];ring
  have ht : (2:ℝ)^(n+e)≠0 := by positivity
  have hfact : ((n+e).factorial:ℝ)≠0 := by positivity
  unfold fourJacobiAmplitude
  rw [div_pow,mul_pow,mul_pow,mul_pow,
    Real.sq_sqrt (by positivity : 0≤(4:ℝ)^e*(e.factorial:ℝ)),
    Real.sq_sqrt (by positivity : 0≤(4:ℝ)^n*(n.factorial:ℝ)),
    Real.sq_sqrt (by positivity : 0≤(2:ℝ)^(n+e)*((n+e).factorial:ℝ)),hnum]
  rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
  simp only [div_pow,one_pow]
  field_simp [ht,hfact] <;> ring

theorem fourSignedAmplitude_sq (n e : ℕ) :
    (fourSignedAmplitude n e)^2=((n+e).choose e:ℝ)*(1/2:ℝ)^(n+e) := by
  rw [fourSignedAmplitude,mul_pow,← pow_mul, mul_comm e 2,pow_mul]
  norm_num [fourJacobiAmplitude_sq]

theorem fourCOMWeight_eq_amplitude_sq (a : ℝ) (e n : ℕ) :
    fourCOMWeight a e n=(1/2:ℝ)*thermalEigenvalue a (n+e)*(fourSignedAmplitude n e)^2 := by
  rw [fourSignedAmplitude_sq]
  unfold fourCOMWeight
  ring

theorem hasSum_fourSignedAmplitude_sq (a : ℝ) (ha : 0<a) (e : ℕ) :
    HasSum (fun n => (1/2:ℝ)*thermalEigenvalue a (n+e)*(fourSignedAmplitude n e)^2)
      ((1/(1+2*a))^(e+1)) := by
  simpa only [← fourCOMWeight_eq_amplitude_sq] using hasSum_fourCOMWeight a ha e

end TorusLean.Shared.ThermalCoherentJacobiFourWeights
