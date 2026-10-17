import torus.shared.ThermalCoherentFermionCOMWordsSource
import torus.shared.ParameterLadderCommutator
import torus.shared.ParameterLadderFinite

/-! Exact declaration-prefix split of the unaccepted COMWords first probe. No theorem head or proof body is changed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterLadderCommutator TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterLadderIntegration
open scoped ContDiff BigOperators ComplexConjugate

/-- Each finite marked level remains a finite exterior source.  The total
raise carries the physical normalization sqrt(k), not sqrt of orbital cutoff. -/
def comSource (k : ℕ) (c : WordCoefficients k) : ℕ → WordCoefficients k
  | 0 => c
  | n+1 => (Real.sqrt (k:ℝ):ℂ)⁻¹ • wordRaise k (comSource k c n)

def comDual (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (n : ℕ) : ℂ → ℂ :=
  wordDual G theta k q (comSource k c n)

theorem comDual_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (n : ℕ) :
    ContDiff ℝ ∞ (comDual G theta k q c n) :=
  wordDual_contDiff G theta k q _

theorem comDual_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (n : ℕ) :
    HasDualBoundary G theta k (comDual G theta k q c n) :=
  wordDual_boundary G theta k q _

theorem comDual_raise (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (n : ℕ) :
    parameterRaise k (comDual G theta k q c n) = comDual G theta k q c (n+1) := by
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  funext R
  have h := wordDual_raise G theta k q (comSource k c n) R
  simp only [comDual, comSource, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← h]
  field_simp [hk] <;> ring

/-- Equal actual exterior sources give the same entire COM family.  No
injectivity of the finite word presentation is assumed. -/
theorem comDual_eq_of_realize_eq (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c d : WordCoefficients k)
    (hcd : realize k c = realize k d) (n : ℕ) :
    comDual G theta k q c n = comDual G theta k q d n := by
  induction n with
  | zero =>
    change exteriorSeedDual G theta q (realize k c) =
      exteriorSeedDual G theta q (realize k d)
    rw [hcd]
  | succ n ih =>
    rw [← comDual_raise, ← comDual_raise, ih]

/-- A genuine exterior-algebra annihilation, allowing the cancellations caused
by repeated labels.  It is deliberately weaker than vanishing of the free
ordered-word presentation after lowering. -/
def IsExteriorVacuum (k : ℕ) (c : WordCoefficients k) : Prop :=
  realize k (wordLower k c) = 0

theorem comDual_lower_zero (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (hc : IsExteriorVacuum k c) :
    parameterLower k (comDual G theta k q c 0) = 0 := by
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  funext R
  have h := wordDual_lower G theta k q c R
  have hz : wordDual G theta k q (wordLower k c) = 0 := by
    change exteriorSeedDualLinearMap G theta q (realize k (wordLower k c)) = 0
    rw [hc, map_zero]
  rw [hz] at h
  exact (mul_eq_zero.mp h).resolve_left hk

/-- Lowering all COM levels is proved from the genuine parameter commutator,
not assumed as an abstract oscillator representation. -/
theorem comDual_lower_succ (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (hc : IsExteriorVacuum k c)
    (n : ℕ) :
    parameterLower k (comDual G theta k q c (n+1)) =
      ((n+1:ℕ):ℂ) • comDual G theta k q c n := by
  induction n with
  | zero =>
    funext R
    have h := parameter_commutator k (comDual G theta k q c 0)
      (comDual_contDiff G theta k q c 0) R
    rw [comDual_raise, comDual_lower_zero G theta k q c hc] at h
    simp only [parameterRaise, parameterWirtingerBar, fderiv_zero, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, mul_zero, sub_zero, zero_add, zero_div] at h
    simpa only [Nat.zero_add, Nat.cast_one, one_smul] using h
  | succ n ih =>
    funext R
    have h := parameter_commutator k (comDual G theta k q c (n+1))
      (comDual_contDiff G theta k q c (n+1)) R
    rw [comDual_raise, ih] at h
    change parameterLower k (comDual G theta k q c (n+1+1)) R -
      parameterRaise k (fun z => ((n+1:ℕ):ℂ)*comDual G theta k q c n z) R = _ at h
    rw [parameterRaise_const_mul _ _ _
      ((comDual_contDiff G theta k q c n).differentiable (by simp)), comDual_raise] at h
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one] at h ⊢
    linear_combination h

theorem comDual_isFiniteLadder (G : Geometry) (theta : Twist) (k H : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (hc : IsExteriorVacuum k c) :
    IsFiniteLadderFamily G theta k H (comDual G theta k q c) where
  smooth n _ := (comDual_contDiff G theta k q c n).of_le (by simp)
  boundary n _ := comDual_boundary G theta k q c n
  raise_eq n _ := comDual_raise G theta k q c n
  lower_zero := comDual_lower_zero G theta k q c hc
  lower_succ n _ := comDual_lower_succ G theta k q c hc n


#print axioms comDual_contDiff
#print axioms comDual_boundary
#print axioms comDual_raise
#print axioms comDual_eq_of_realize_eq
#print axioms comDual_lower_zero
#print axioms comDual_lower_succ
#print axioms comDual_isFiniteLadder

end TorusLean.Shared.ThermalCoherentFermionCOMWords
