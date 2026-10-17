import torus.shared.ThermalCoherentSeedWord

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredSeedActions
open TorusLean.Boson TorusLean.Shared.BosonPeriodizedSeed
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterRawJetWord
open TorusLean.Shared.ThermalCoherentSeedWord
open scoped BigOperators ContDiff

theorem parameterRaise_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterRaise k (fun z => ∑ i ∈ s, f i z) R = ∑ i ∈ s, parameterRaise k (f i) R := by
  unfold parameterRaise
  rw [wirtingerBar_sum s f hf R]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

theorem parameterLower_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterLower k (fun z => ∑ i ∈ s, f i z) R = ∑ i ∈ s, parameterLower k (f i) R := by
  unfold parameterLower
  rw [wirtinger_sum s f hf R]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, Finset.sum_div]

theorem rawWord_update (G : Geometry) (theta : Twist) (k : ℕ)
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) (i : Fin k) (n : ℕ) (R : ℂ) :
    rawWord G theta k h (Function.update j i n) R =
      dualRawJetScalar G theta (h i) n R *
        ∏ l ∈ Finset.univ.erase i, dualRawJetScalar G theta (h l) (j l) R := by
  unfold rawWord
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

def wordDual (G : Geometry) (theta : Twist) (K k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → Fin K) (R : ℂ) : ℂ :=
  occupationInner (fun _ => 1) q (anchoredSeed G theta K R (canonicalWord k j))

theorem wordDual_expansion (G : Geometry) (theta : Twist) (K k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → Fin K) :
    wordDual G theta K k q j = fun R => ∑ w : Fin k → OrbitalIndex G theta,
      occupationInner (fun _ => 1) q (canonicalWord k w) *
        rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val) R := by
  funext R
  exact anchoredSeed_word_dual_expansion G theta K k j q R

def raiseWord (K k : ℕ) (j : Fin k → Fin K) (i : Fin k) (hi : (j i).val+1<K) : Fin k → Fin K :=
  Function.update j i ⟨(j i).val+1,hi⟩

theorem raiseWord_val (K k : ℕ) (j : Fin k → Fin K) (i : Fin k) (hi : (j i).val+1<K) :
    (fun a => (raiseWord K k j i hi a).val) = Function.update (fun a => (j a).val) i ((j i).val+1) := by
  funext a
  by_cases ha : a=i
  · subst a; simp [raiseWord]
  · simp [raiseWord, Function.update_of_ne ha]

theorem wordDual_raise (G : Geometry) (theta : Twist) (K k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → Fin K)
    (htop : ∀ i, (j i).val+1<K) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (wordDual G theta K k q j) R =
      ∑ i, (Real.sqrt ((j i).val+1:ℝ):ℂ)*wordDual G theta K k q (raiseWord K k j i (htop i)) R := by
  rw [wordDual_expansion]
  rw [parameterRaise_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterRaise_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → OrbitalIndex G theta, ∑ i : Fin k,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          ((Real.sqrt ((j i).val+1:ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (w a))
            (Function.update (fun a => (j a).val) i ((j i).val+1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (fun _ => 1) q (canonicalWord k w)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val)) R) =
        occupationInner (fun _ => 1) q (canonicalWord k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val)) R) by ring,
        rawWord_raise, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [rawWord_update]
      push_cast
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [wordDual_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [raiseWord_val]
      ring

def lowerWord (K k : ℕ) (j : Fin k → Fin K) (i : Fin k) : Fin k → Fin K :=
  Function.update j i ⟨(j i).val-1, by have := (j i).isLt; omega⟩

theorem lowerWord_val (K k : ℕ) (j : Fin k → Fin K) (i : Fin k) :
    (fun a => (lowerWord K k j i a).val) = Function.update (fun a => (j a).val) i ((j i).val-1) := by
  funext a
  by_cases ha : a=i
  · subst a; simp [lowerWord]
  · simp [lowerWord, Function.update_of_ne ha]

theorem wordDual_lower (G : Geometry) (theta : Twist) (K k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → Fin K)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (wordDual G theta K k q j) R =
      ∑ i, (Real.sqrt ((j i).val:ℝ):ℂ)*wordDual G theta K k q (lowerWord K k j i) R := by
  rw [wordDual_expansion]
  rw [parameterLower_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterLower_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → OrbitalIndex G theta, ∑ i : Fin k,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          ((Real.sqrt ((j i).val:ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (w a))
            (Function.update (fun a => (j a).val) i ((j i).val-1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (fun _ => 1) q (canonicalWord k w)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val)) R) =
        occupationInner (fun _ => 1) q (canonicalWord k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val)) R) by ring,
        rawWord_lower, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [rawWord_update]
      push_cast
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [wordDual_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [lowerWord_val]
      ring

#print axioms wordDual_raise
#print axioms wordDual_lower

end TorusLean.Shared.BosonAnchoredSeedActions
