import torus.shared.BosonAnchoredNatActions

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Boson TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.BosonAnchoredSeedActions
open TorusLean.Shared.BosonAnchoredNatActions
open TorusLean.Shared.ThermalCoherentSeedWord TorusLean.Shared.ThermalCoherentSeedDomain
open scoped BigOperators ContDiff

def finiteNatWordSeed {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) : Core ℕ ℂ :=
  ∑ i ∈ s, c i • canonicalWord k (j i)

/-- Exact dual analysis of the actual periodized polynomial, linear in the seed. -/
def seedDualMapNat (G : Geometry) (theta : Twist) 
    (q : Core (OrbitalIndex G theta) ℂ) : Core ℕ ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun p R := occupationInner (fun _ => 1) q (anchoredSeedNat G theta R p)
  map_add' p r := by funext R; simp only [map_add, occupationInner_add_right, Pi.add_apply]
  map_smul' c p := by funext R; simp only [map_smul, occupationInner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem seedDualMapNat_word (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ) :
    seedDualMapNat G theta q (canonicalWord k j) = wordDualNat G theta k q j := rfl

theorem finiteNatWordSeed_sector {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) :
    (finiteNatWordSeed k s c j).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul]
  exact (canonicalWord_sector k (j i)).C_mul _

theorem seedDualMapNat_finiteWord_contDiff {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) (q : Core (OrbitalIndex G theta) ℂ)
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ) :
    ContDiff ℝ ∞ (seedDualMapNat G theta q (finiteNatWordSeed k s c j)) := by
  simp only [finiteNatWordSeed, map_sum, map_smul, seedDualMapNat_word]
  have he : (∑ i ∈ s, c i • wordDualNat G theta k q (j i)) =
      (fun R => ∑ i ∈ s, c i * wordDualNat G theta k q (j i) R) := by
    funext R
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul (wordDualNat_contDiff G theta k q (j i))

theorem seedDualMapNat_finiteWord_boundary {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) (q : Core (OrbitalIndex G theta) ℂ)
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ) :
    HasDualBoundary G theta k (seedDualMapNat G theta q (finiteNatWordSeed k s c j)) := by
  simp only [finiteNatWordSeed, map_sum, map_smul, seedDualMapNat_word]
  have he : (∑ i ∈ s, c i • wordDualNat G theta k q (j i)) =
      (fun R => ∑ i ∈ s, c i * wordDualNat G theta k q (j i) R) := by
    funext R
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  change HasDualBoundary G theta k (fun R => ∑ i ∈ s, c i * wordDualNat G theta k q (j i) R)
  exact hasDualBoundary_finset_linear G theta k s c _ (fun i _ => wordDualNat_boundary G theta k q (j i))

def raiseFiniteNatWordSeed {I : Type*} (k : ℕ) (s : Finset I) (c : I → ℂ)
    (j : I → Fin k → ℕ) : Core ℕ ℂ :=
  ∑ i ∈ s, c i • ∑ a, (Real.sqrt ((j i a)+1:ℝ):ℂ) • canonicalWord k (Function.update (j i) a (j i a+1))

def lowerFiniteNatWordSeed {I : Type*} (k : ℕ) (s : Finset I) (c : I → ℂ)
    (j : I → Fin k → ℕ) : Core ℕ ℂ :=
  ∑ i ∈ s, c i • ∑ a, (Real.sqrt ((j i a):ℝ):ℂ) • canonicalWord k (Function.update (j i) a (j i a-1))

theorem seedDualMapNat_raise_finiteWord {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Core (OrbitalIndex G theta) ℂ)
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (seedDualMapNat G theta q (finiteNatWordSeed k s c j)) R =
      seedDualMapNat G theta q (raiseFiniteNatWordSeed k s c j) R := by
  have hf (i : I) : Differentiable ℝ (wordDualNat G theta k q (j i)) :=
    (wordDualNat_contDiff G theta k q (j i)).differentiable (by simp)
  simp only [finiteNatWordSeed, raiseFiniteNatWordSeed, map_sum, map_smul, seedDualMapNat_word]
  have hsum : (∑ i ∈ s, c i • wordDualNat G theta k q (j i)) =
      (fun z => ∑ i ∈ s, c i*wordDualNat G theta k q (j i) z) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  change (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (fun z => ∑ i ∈ s, c i*wordDualNat G theta k q (j i) z) R = _
  rw [parameterRaise_sum _ _ _ (fun i _ => (hf i).const_mul _), Finset.mul_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [parameterRaise_const_mul k _ _ (hf i)]
  calc
    _ = c i*((Real.sqrt (k:ℝ):ℂ)*parameterRaise k (wordDualNat G theta k q (j i)) R) := by ring
    _ = _ := by rw [wordDualNat_raise G theta k q (j i) R]

theorem seedDualMapNat_lower_finiteWord {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Core (OrbitalIndex G theta) ℂ)
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (seedDualMapNat G theta q (finiteNatWordSeed k s c j)) R =
      seedDualMapNat G theta q (lowerFiniteNatWordSeed k s c j) R := by
  have hf (i : I) : Differentiable ℝ (wordDualNat G theta k q (j i)) :=
    (wordDualNat_contDiff G theta k q (j i)).differentiable (by simp)
  simp only [finiteNatWordSeed, lowerFiniteNatWordSeed, map_sum, map_smul, seedDualMapNat_word]
  have hsum : (∑ i ∈ s, c i • wordDualNat G theta k q (j i)) =
      (fun z => ∑ i ∈ s, c i*wordDualNat G theta k q (j i) z) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  change (Real.sqrt (k:ℝ):ℂ)*parameterLower k (fun z => ∑ i ∈ s, c i*wordDualNat G theta k q (j i) z) R = _
  rw [parameterLower_sum _ _ _ (fun i _ => (hf i).const_mul _), Finset.mul_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [parameterLower_const_mul k _ _ (hf i)]
  calc
    _ = c i*((Real.sqrt (k:ℝ):ℂ)*parameterLower k (wordDualNat G theta k q (j i)) R) := by ring
    _ = _ := by rw [wordDualNat_lower G theta k q (j i) R]

#print axioms seedDualMapNat_raise_finiteWord
#print axioms seedDualMapNat_lower_finiteWord
end TorusLean.Shared.BosonAnchoredNatLinearActions
