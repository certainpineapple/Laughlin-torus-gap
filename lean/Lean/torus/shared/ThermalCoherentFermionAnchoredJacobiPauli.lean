import torus.shared.ThermalCoherentFermionAnchoredJacobiInsertion

/-! Genuine zero vectors in the paper's existing finite Nat exterior source.
These statements concern exterior products, not zero scalar spectral weights. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Fermion
open TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

private theorem formalJet_swap (i j : ℕ) :
    formalJet i*formalJet j=-(formalJet j*formalJet i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

private theorem formalJet_repeat_first (i j : ℕ) :
    formalJet i*formalJet j*formalJet i=0 := by
  rw [mul_assoc,formalJet_swap j i,mul_neg,← mul_assoc]
  simp only [formalJet,ExteriorAlgebra.ι_sq_zero,zero_mul,neg_zero]

private theorem formalJet_repeat_second (i j : ℕ) :
    formalJet i*formalJet j*formalJet j=0 := by
  rw [mul_assoc]
  simp only [formalJet,ExteriorAlgebra.ι_sq_zero,mul_zero]

/-- Genuine three-particle wedges of total orbital degree below three vanish. -/
theorem formalThreeSeed_low_degree_zero (p j : ℕ) (h : p+j≤1) :
    formalThreeSeed p j=0 := by
  classical
  simp only [formalThreeSeed,formalPair,Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i.val≤p+1 := by omega
  have hd : i.val+(p+1-i.val)+j≤2 := by omega
  have he : i.val=p+1-i.val ∨ i.val=j ∨ p+1-i.val=j := by omega
  rcases he with he | he | he
  · rw [← he]
    simp only [formalJet,ExteriorAlgebra.ι_sq_zero,zero_mul,smul_zero]
  · rw [← he,formalJet_repeat_first,smul_zero]
  · rw [← he,formalJet_repeat_second,smul_zero]

/-- z=0 has orbital degree one and is zero before taking any norm. -/
theorem formalRelativeSeed_zero : formalRelativeSeed 0=0 := by
  unfold formalRelativeSeed
  apply Finset.sum_eq_zero
  intro p hp
  have hp0 : p=0 := by have := Finset.mem_range.mp hp; omega
  subst p
  rw [formalThreeSeed_low_degree_zero 0 0 (by omega),smul_zero]

/-- z=1 has orbital degree two and is also an actual zero exterior source. -/
theorem formalRelativeSeed_one : formalRelativeSeed 1=0 := by
  unfold formalRelativeSeed
  apply Finset.sum_eq_zero
  intro p hp
  have hp1 : p≤1 := by have := Finset.mem_range.mp hp; omega
  rw [formalThreeSeed_low_degree_zero p (1-p) (by omega),smul_zero]


private theorem formalJet_swap_tail (i j k : ℕ) :
    formalJet i*formalJet j*formalJet k=-(formalJet i*formalJet k*formalJet j) := by
  rw [mul_assoc,formalJet_swap j k,mul_neg,← mul_assoc]

private theorem formalJet_cycle (i j k : ℕ) :
    formalJet i*formalJet j*formalJet k=formalJet k*formalJet i*formalJet j := by
  rw [formalJet_swap_tail i j k,formalJet_swap i k,neg_mul,neg_neg]

private theorem formalThreeSeed_one_two : formalThreeSeed 1 2=0 := by
  simp only [formalThreeSeed,formalPair,Fin.sum_univ_succ]
  simp only [add_mul,smul_mul_assoc]
  norm_num [pairLeftCoefficient,paperPairWeight,formalJet_repeat_second]

private theorem formalThreeSeed_two_one : formalThreeSeed 2 1=
    (3*Real.sqrt (1/12:ℝ):ℂ) • (formalJet 0*formalJet 1*formalJet 3) := by
  simp only [formalThreeSeed,formalPair,Fin.sum_univ_succ]
  simp only [add_mul,smul_mul_assoc]
  norm_num [pairLeftCoefficient,paperPairWeight,formalJet_repeat_second,
    formalJet_repeat_first]
  rw [formalJet_swap_tail 0 3 1] <;>
    simp only [smul_neg,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat] <;>
    module

private theorem formalThreeSeed_three_zero : formalThreeSeed 3 0=
    (-2*Real.sqrt (1/8:ℝ):ℂ) • (formalJet 0*formalJet 1*formalJet 3) := by
  simp only [formalThreeSeed,formalPair,Fin.sum_univ_succ]
  simp only [add_mul,smul_mul_assoc]
  norm_num [pairLeftCoefficient,paperPairWeight,formalJet_repeat_second,
    formalJet_repeat_first]
  rw [formalJet_cycle 1 3 0] <;>
    simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat] <;>
    module

private theorem pauli_three_scalar_cancellation :
    -paperPauliCoefficient 3 0 +
      paperPauliCoefficient 3 2*(3*Real.sqrt (1/12:ℝ)) +
      paperPauliCoefficient 3 3*(-2*Real.sqrt (1/8:ℝ))=0 := by
  have h2 : Real.sqrt (2:ℝ)≠0 := by positivity
  have h3 : Real.sqrt (3:ℝ)≠0 := by positivity
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt (4:ℝ)=2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  have h12 : Real.sqrt (1/12:ℝ)=1/(2*Real.sqrt (3:ℝ)) := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,
      show (12:ℝ)=4*3 by norm_num,Real.sqrt_mul (by norm_num),hs4]
  have h8 : Real.sqrt (1/8:ℝ)=1/(2*Real.sqrt (2:ℝ)) := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,
      show (8:ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num),hs4]
  norm_num [paperPauliCoefficient,h12,h8,Real.sqrt_div]
  field_simp [h2,h3]
  nlinarith [hs2,hs3]

/-- The paper's z=3 relative source is also literally zero. Unlike z=0,1,
this uses cancellation between its nonzero exterior columns at orbital degree 4. -/
theorem formalRelativeSeed_three : formalRelativeSeed 3=0 := by
  have h0 : formalThreeSeed 0 3=-(formalJet 0*formalJet 1*formalJet 3) := by
    rw [formalThreeSeed,formalPair_ground,neg_mul]
  simp only [formalRelativeSeed,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num only [Nat.reduceSub,Nat.reduceAdd]
  rw [h0,formalThreeSeed_one_two,formalThreeSeed_two_one,formalThreeSeed_three_zero]
  simp only [smul_zero,add_zero,zero_add,smul_neg,smul_smul,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  have hc := congrArg (fun r : ℝ => (r:ℂ)) pauli_three_scalar_cancellation
  simp only [Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_zero,Complex.ofReal_ofNat] at hc
  calc
    _ = ((-(paperPauliCoefficient 3 0:ℂ) +
      (paperPauliCoefficient 3 2:ℂ)*(3*Real.sqrt (1/12:ℝ):ℂ) +
      (paperPauliCoefficient 3 3:ℂ)*(-2*Real.sqrt (1/8:ℝ):ℂ))) •
        (formalJet 0*formalJet 1*formalJet 3) := by module
    _ = 0 := by rw [hc,zero_smul]

end TorusLean.Shared.ThermalCoherentFermionAnchored
