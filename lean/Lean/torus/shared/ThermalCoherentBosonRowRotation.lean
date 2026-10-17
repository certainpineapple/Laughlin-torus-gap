import torus.shared.ThermalCoherentJacobiFourParseval

/-! The genuine charge-two pair / charge-one spectator Jacobi unitary on the
complete two-oscillator degree sector. The already proved general finite
second-quantization Parseval theorem is reused, including all degree labels. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowRotation
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

private def a : ℂ := (Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ)
private def b : ℂ := (Real.sqrt (3:ℝ):ℂ)⁻¹

private theorem ab_square : a^2+b^2=1 := by
  have h2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h3 : (Real.sqrt (3:ℝ):ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  simp only [a,b,div_pow,inv_pow,h2,h3]
  norm_num

private def jacobiLinear : Orbital (Fin 2) →ₗ[ℂ] Orbital (Fin 2) where
  toFun v := (a*v 0-b*v 1) • EuclideanSpace.single 0 1 +
    (b*v 0+a*v 1) • EuclideanSpace.single 1 1
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

private def jacobiInverse : Orbital (Fin 2) →ₗ[ℂ] Orbital (Fin 2) where
  toFun v := (a*v 0+b*v 1) • EuclideanSpace.single 0 1 +
    (-b*v 0+a*v 1) • EuclideanSpace.single 1 1
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

private theorem jacobiLinear_apply (v : Orbital (Fin 2)) :
    jacobiLinear v 0=a*v 0-b*v 1 ∧ jacobiLinear v 1=b*v 0+a*v 1 := by
  simp [jacobiLinear]
private theorem jacobiInverse_apply (v : Orbital (Fin 2)) :
    jacobiInverse v 0=a*v 0+b*v 1 ∧ jacobiInverse v 1= -b*v 0+a*v 1 := by
  simp [jacobiInverse]

private theorem jacobiLinear_zero (v : Orbital (Fin 2)) : jacobiLinear v 0=a*v 0-b*v 1 := (jacobiLinear_apply v).1
private theorem jacobiLinear_one (v : Orbital (Fin 2)) : jacobiLinear v 1=b*v 0+a*v 1 := (jacobiLinear_apply v).2
private theorem jacobiInverse_zero (v : Orbital (Fin 2)) : jacobiInverse v 0=a*v 0+b*v 1 := (jacobiInverse_apply v).1
private theorem jacobiInverse_one (v : Orbital (Fin 2)) : jacobiInverse v 1= -b*v 0+a*v 1 := (jacobiInverse_apply v).2

private theorem jacobi_left_inverse : Function.LeftInverse jacobiInverse jacobiLinear := by
  intro v
  ext i
  fin_cases i
  · change jacobiInverse (jacobiLinear v) 0 = v 0
    simp only [jacobiInverse_zero,jacobiLinear_zero,jacobiLinear_one]
    calc
      _ = (a^2+b^2)*v 0 := by ring
      _ = _ := by rw [ab_square,one_mul]
  · change jacobiInverse (jacobiLinear v) 1 = v 1
    simp only [jacobiInverse_one,jacobiLinear_zero,jacobiLinear_one]
    calc
      _ = (a^2+b^2)*v 1 := by ring
      _ = _ := by rw [ab_square,one_mul]

private theorem jacobi_right_inverse : Function.RightInverse jacobiInverse jacobiLinear := by
  intro v
  ext i
  fin_cases i
  · change jacobiLinear (jacobiInverse v) 0 = v 0
    simp only [jacobiLinear_zero,jacobiInverse_zero,jacobiInverse_one]
    calc
      _ = (a^2+b^2)*v 0 := by ring
      _ = _ := by rw [ab_square,one_mul]
  · change jacobiLinear (jacobiInverse v) 1 = v 1
    simp only [jacobiLinear_one,jacobiInverse_zero,jacobiInverse_one]
    calc
      _ = (a^2+b^2)*v 1 := by ring
      _ = _ := by rw [ab_square,one_mul]

private def jacobiEquiv : Orbital (Fin 2) ≃ₗ[ℂ] Orbital (Fin 2) :=
  { jacobiLinear with
    invFun := jacobiInverse
    left_inv := jacobi_left_inverse
    right_inv := jacobi_right_inverse }

private theorem jacobiLinear_inner (v w : Orbital (Fin 2)) :
    inner ℂ (jacobiLinear v) (jacobiLinear w)=inner ℂ v w := by
  have ha : star a=a := by simp [a,Complex.star_def]
  have hb : star b=b := by simp [b,Complex.star_def]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,
    Pi.star_apply,jacobiLinear_zero,jacobiLinear_one,
    star_mul,star_sub,star_add,ha,hb]
  calc
    _ = (a^2+b^2)*(star (v 0)*w 0+star (v 1)*w 1) := by ring
    _ = _ := by rw [ab_square,one_mul]; ring

def pairSpectatorRotation : Unitary (Fin 2) := jacobiEquiv.isometryOfInner jacobiLinear_inner

theorem pairSpectatorRotation_zero (v : Orbital (Fin 2)) :
    pairSpectatorRotation v 0 = (Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ)*v 0 -
      (Real.sqrt (3:ℝ):ℂ)⁻¹*v 1 := (jacobiLinear_apply v).1

theorem pairSpectatorRotation_one (v : Orbital (Fin 2)) :
    pairSpectatorRotation v 1 = (Real.sqrt (3:ℝ):ℂ)⁻¹*v 0 +
      (Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ)*v 1 := (jacobiLinear_apply v).2

def rotatePairSpectator : Core (Fin 2) ℂ →ₐ[ℂ] Core (Fin 2) ℂ :=
  secondQuantization pairSpectatorRotation

theorem rotatePairSpectator_X_zero : rotatePairSpectator (MvPolynomial.X 0) =
    ((Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ)) • MvPolynomial.X 0 +
      (Real.sqrt (3:ℝ):ℂ)⁻¹ • MvPolynomial.X 1 := by
  simp only [rotatePairSpectator,secondQuantization,MvPolynomial.aeval_X,
    modeLinear,Fin.sum_univ_two,pairSpectatorRotation_zero,pairSpectatorRotation_one]
  simp [MvPolynomial.smul_eq_C_mul]

theorem rotatePairSpectator_X_one : rotatePairSpectator (MvPolynomial.X 1) =
    -(Real.sqrt (3:ℝ):ℂ)⁻¹ • MvPolynomial.X 0 +
      ((Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ)) • MvPolynomial.X 1 := by
  simp only [rotatePairSpectator,secondQuantization,MvPolynomial.aeval_X,
    modeLinear,Fin.sum_univ_two,pairSpectatorRotation_zero,pairSpectatorRotation_one]
  simp [MvPolynomial.smul_eq_C_mul]

/-- Full ordered degree-t trace, valid after arbitrary linear coefficient maps. -/
theorem pairSpectatorRotation_ordered_cross (t : ℕ)
    (F G : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) :
    ∑ j : Fin (t+1), star (F (rotatePairSpectator (normalizedSpectatorWord j.val (t-j.val))))*
      G (rotatePairSpectator (normalizedSpectatorWord j.val (t-j.val))) =
    ∑ j : Fin (t+1), star (F (normalizedSpectatorWord j.val (t-j.val)))*
      G (normalizedSpectatorWord j.val (t-j.val)) := by
  have h := secondQuantization_finite_dual_cross pairSpectatorRotation t F G
  simp_rw [degreeFrame_eq_spectatorWord] at h
  have hsum (H : ℕ → ℕ → ℂ) :
      (∑ j : Fin (t+1), H j.val (t-j.val)) =
        ∑ n : DegreeIndex t, H (n.val 0) (n.val 1) := by
    simpa [degreeIndexEquiv] using
      (Equiv.sum_comp (degreeIndexEquiv t).symm (fun n : DegreeIndex t => H (n.val 0) (n.val 1)))
  rw [hsum (fun j m => star (F (rotatePairSpectator (normalizedSpectatorWord j m)))*
    G (rotatePairSpectator (normalizedSpectatorWord j m))),
    hsum (fun j m => star (F (normalizedSpectatorWord j m))*G (normalizedSpectatorWord j m))]
  exact h

end TorusLean.Shared.ThermalCoherentBosonRowRotation
