import torus.shared.ThermalCoherentFermionCOMWords

/-! A concrete exterior vacuum, actual normalized raw-jet descendants,
and the finite marked same-cell trace.  The relative source matrix is retained
in full; no claim of mutual orthogonality of relative labels is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock MeasureTheory
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterLadderFinite
open TorusLean.Shared.ParameterLadderIntegration
open scoped ContDiff BigOperators ComplexConjugate

/-- Lowering the filled exterior word vanishes by repeated-label CAR zeros.
The free ordered-word lowering does not vanish and is not used as a premise. -/
theorem lowerExteriorWord_filled (k : ℕ) :
    lowerExteriorWord k (fun a : Fin k => a.val) = 0 := by
  classical
  unfold lowerExteriorWord
  apply Finset.sum_eq_zero
  intro a ha
  by_cases h0 : a.val = 0
  · simp [h0]
  · have hp : 0 < a.val := Nat.pos_of_ne_zero h0
    let b : Fin k := ⟨a.val-1, lt_trans (Nat.sub_lt hp (by decide)) a.isLt⟩
    have hab : a ≠ b := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [b] at hv
      omega
    have hlabels :
        Function.update (fun i : Fin k => i.val) a (a.val-1) a =
        Function.update (fun i : Fin k => i.val) a (a.val-1) b := by
      simp [Function.update, hab, Ne.symm hab, b]
    rw [formalExteriorWord_repeat k _ a b hab hlabels, smul_zero]

def filledWord (k : ℕ) : WordCoefficients k :=
  Finsupp.single (fun a : Fin k => a.val) 1

theorem filledWord_isExteriorVacuum (k : ℕ) : IsExteriorVacuum k (filledWord k) := by
  change realize k (wordLower k (Finsupp.single (fun a : Fin k => a.val) 1)) = 0
  simp only [wordLower, Finsupp.linearCombination_single, one_smul,
    map_sum, map_smul, realize, Finsupp.linearCombination_single, one_smul]
  exact lowerExteriorWord_filled k

/-- Literal physical exterior output at each normalized COM level. -/
def actualNormalizedCOMSource (G : Geometry) (theta : Twist) (k : ℕ)
    (c : WordCoefficients k) (n : ℕ) (R : ℂ) : Space (physicalQ G theta) :=
  rawJetExteriorMap G theta R
    ((Real.sqrt (n.factorial:ℝ):ℂ)⁻¹ • realize k (comSource k c n))

theorem actualNormalizedCOMSource_dual (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (c : WordCoefficients k) (n : ℕ) (R : ℂ) :
    occupationInner (physicalQ G theta) q (actualNormalizedCOMSource G theta k c n R) =
      normalizedLevel (comDual G theta k q c) n R := by
  simp only [actualNormalizedCOMSource, map_smul, occupationInner_smul_right,
    normalizedLevel, Pi.smul_apply, smul_eq_mul]
  rfl

/-- COM construction preserves every relation among finite formal exterior
words, including the CAR kernel of `realize`.  A relation that holds only after
the physical raw-jet map at one parameter is not a premise of this theorem. -/
theorem actualNormalizedCOMSource_eq_of_realize_eq (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (c d : WordCoefficients k)
    (hcd : realize k c = realize k d) (n : ℕ) (R : ℂ) :
    actualNormalizedCOMSource G theta k c n R =
      actualNormalizedCOMSource G theta k d n R := by
  let x := actualNormalizedCOMSource G theta k c n R
  let y := actualNormalizedCOMSource G theta k d n R
  have he : occupationInner (physicalQ G theta) (x-y) x =
      occupationInner (physicalQ G theta) (x-y) y := by
    change occupationInner (physicalQ G theta) (x-y)
      (actualNormalizedCOMSource G theta k c n R) =
        occupationInner (physicalQ G theta) (x-y)
          (actualNormalizedCOMSource G theta k d n R)
    rw [actualNormalizedCOMSource_dual, actualNormalizedCOMSource_dual,
      normalizedLevel, normalizedLevel, comDual_eq_of_realize_eq G theta k (x-y) c d hcd]
  have hsub (q : Space (physicalQ G theta)) :
      occupationInner (physicalQ G theta) q (x-y) =
        occupationInner (physicalQ G theta) q x - occupationInner (physicalQ G theta) q y := by
    simp [occupationInner, mul_sub, Finset.sum_sub_distrib]
  have hz : occupationInner (physicalQ G theta) (x-y) (x-y) = 0 := by
    rw [hsub, he, sub_self]
  have hn : occupationNormSq (physicalQ G theta) (x-y) = 0 := by
    have hr := congrArg Complex.re hz
    simpa only [occupationInner_self, Complex.ofReal_re, Complex.zero_re] using hr
  exact sub_eq_zero.mp ((occupationNormSq_eq_zero _ _).mp hn)

/-- Both relative labels and COM markers remain explicit in the finite trace.
The source kernel C can in particular be the actual fermionic Jacobi matrix;
this result neither replaces it by eigenvalues nor postulates orthogonality. -/
theorem marked_exterior_same_cell_trace {A B : Type*} [Fintype A] [Fintype B]
    (G : Geometry) (theta : Twist) (k H : ℕ) [NeZero k]
    (q : A → Space (physicalQ G theta)) (r : B → Space (physicalQ G theta))
    (c : A → WordCoefficients k) (d : B → WordCoefficients k)
    (hc : ∀ a, IsExteriorVacuum k (c a)) (hd : ∀ b, IsExteriorVacuum k (d b))
    (C : (A × Fin (H+1)) → (B × Fin (H+1)) → ℂ) :
    (∫ R, ∑ u : A × Fin (H+1), ∑ v : B × Fin (H+1),
      C u v *
        (conj (occupationInner (physicalQ G theta) (q u.1)
          (actualNormalizedCOMSource G theta k (c u.1) u.2 R)) *
         occupationInner (physicalQ G theta) (r v.1)
          (actualNormalizedCOMSource G theta k (d v.1) v.2 R)) ∂cellMeasure G 2) =
    ((2/(k:ℝ):ℝ):ℂ) * ∑ u : A × Fin (H+1), ∑ b : B,
      C u (b,u.2) * cellInner G k
        (wordDual G theta k (q u.1) (c u.1)) (wordDual G theta k (r b) (d b)) := by
  simp_rw [actualNormalizedCOMSource_dual]
  exact finite_ladder_partial_trace_bounded G theta k H
    (fun a => comDual G theta k (q a) (c a))
    (fun b => comDual G theta k (r b) (d b))
    (fun a => comDual_isFiniteLadder G theta k H (q a) (c a) (hc a))
    (fun b => comDual_isFiniteLadder G theta k H (r b) (d b) (hd b)) C

/-- The filled exterior vacuum gives a concrete family without a vacuum premise. -/
theorem filled_com_mu2 (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q r : Space (physicalQ G theta)) (n m : ℕ) :
    cellInner G 2 (normalizedLevel (comDual G theta k q (filledWord k)) n)
      (normalizedLevel (comDual G theta k r (filledWord k)) m) =
      if n = m then ((2/(k:ℝ):ℝ):ℂ) *
        cellInner G k (wordDual G theta k q (filledWord k))
          (wordDual G theta k r (filledWord k)) else 0 :=
  normalized_com_mu2 G theta k q r _ _ (filledWord_isExteriorVacuum k)
    (filledWord_isExteriorVacuum k) n m

#print axioms filledWord_isExteriorVacuum
#print axioms actualNormalizedCOMSource_dual
#print axioms marked_exterior_same_cell_trace
#print axioms filled_com_mu2
#print axioms lowerExteriorWord_filled

#print axioms actualNormalizedCOMSource_eq_of_realize_eq

end TorusLean.Shared.ThermalCoherentFermionCOMWords
