import torus.shared.ParameterCellAdjoint

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderIntegration
open TorusLean.Shared.ParameterCellAdjoint MeasureTheory
open scoped ComplexConjugate BigOperators

/-- Explicit smooth dual-domain and ladder relations. Concrete physical
seed families must separately prove these fields; no CCR is assumed on LLL. -/
structure IsLadderFamily (G : Geometry) (theta : Twist) (k : ℕ)
    (w : ℕ → ℂ → ℂ) : Prop where
  smooth : ∀ n, ContDiff ℝ 1 (w n)
  boundary : ∀ n, HasDualBoundary G theta k (w n)
  raise_eq : ∀ n, parameterRaise k (w n) = w (n+1)
  lower_zero : parameterLower k (w 0) = 0
  lower_succ : ∀ n, parameterLower k (w (n+1)) = ((n+1 : ℕ) : ℂ) • w n

theorem vacuum_descendant_inner_zero (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (w z : ℕ → ℂ → ℂ) (hw : IsLadderFamily G theta k w)
    (hz : IsLadderFamily G theta k z) (m : ℕ) :
    cellInner G k (w 0) (z (m+1)) = 0 := by
  rw [← hz.raise_eq m, ← parameterLower_adjoint G theta k (w 0) (z m)
    (hw.smooth 0) (hz.smooth m) (hw.boundary 0) (hz.boundary m), hw.lower_zero]
  simp [cellInner]

/-- True charge-k cell orthogonality of distinct COM levels, retaining the
full relative matrix unit between the two possibly nonorthogonal vacua. -/
theorem ladder_cellInner (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (w z : ℕ → ℂ → ℂ) (hw : IsLadderFamily G theta k w)
    (hz : IsLadderFamily G theta k z) (n m : ℕ) :
    cellInner G k (w n) (z m) =
      if n = m then (n.factorial : ℂ) * cellInner G k (w 0) (z 0) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m => simpa using vacuum_descendant_inner_zero G theta k w z hw hz m
  | succ n ih =>
    cases m with
    | zero =>
      have h := vacuum_descendant_inner_zero G theta k z w hz hw n
      have hh := congrArg (fun a : ℂ => conj a) h
      simpa only [cellInner_conj_symm, map_zero, Nat.succ_ne_zero, ite_false] using hh
    | succ m =>
      rw [← hz.raise_eq m, ← parameterLower_adjoint G theta k (w (n+1)) (z m)
        (hw.smooth _) (hz.smooth _) (hw.boundary _) (hz.boundary _),
        hw.lower_succ, cellInner_smul_left, ih]
      simp only [map_natCast, Nat.succ.injEq]
      by_cases h : n = m
      · subst m
        simp only [ite_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      · simp [h]

def normalizedLevel (w : ℕ → ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  ((Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹) • w n

/-- Both square-root factorials cancel the actual n! ladder norm. -/
theorem normalized_ladder_cellInner (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (w z : ℕ → ℂ → ℂ) (hw : IsLadderFamily G theta k w)
    (hz : IsLadderFamily G theta k z) (n m : ℕ) :
    cellInner G k (normalizedLevel w n) (normalizedLevel z m) =
      if n = m then cellInner G k (w 0) (z 0) else 0 := by
  rw [normalizedLevel, normalizedLevel, cellInner_smul_left, cellInner_smul_right,
    ladder_cellInner G theta k w z hw hz]
  simp only [map_inv₀, Complex.conj_ofReal]
  by_cases h : n = m
  · subst m
    simp only [ite_true]
    have hs : (Real.sqrt (n.factorial : ℝ) : ℂ)^2 = (n.factorial : ℂ) := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)
    have hn : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    rw [← hs]
    field_simp
  · simp [h]

/-- The original cell measures differ by exactly 2/k. No extra area or
multiplicity factor occurs in the COM partial trace. -/
theorem cellIntegral_two_eq_charge (G : Geometry) (k : ℕ) [NeZero k] (F : ℂ → ℂ) :
    (∫ R, F R ∂cellMeasure G 2) = ((2/(k:ℝ) : ℝ) : ℂ) *
      (∫ R, F R ∂cellMeasure G k) := by
  unfold cellMeasure
  rw [integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  field_simp

/-- Normalized COM-level integration with the paper's mu2 anchor and the
original charge-k vacuum matrix unit; actual seed-family fields remain explicit. -/
theorem normalized_ladder_mu2 (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (w z : ℕ → ℂ → ℂ) (hw : IsLadderFamily G theta k w)
    (hz : IsLadderFamily G theta k z) (n m : ℕ) :
    cellInner G 2 (normalizedLevel w n) (normalizedLevel z m) =
      if n = m then ((2/(k:ℝ) : ℝ) : ℂ) * cellInner G k (w 0) (z 0) else 0 := by
  change (∫ R, conj (normalizedLevel w n R) * normalizedLevel z m R ∂cellMeasure G 2) = _
  rw [cellIntegral_two_eq_charge G k]
  change ((2/(k:ℝ) : ℝ) : ℂ) * cellInner G k (normalizedLevel w n) (normalizedLevel z m) = _
  rw [normalized_ladder_cellInner G theta k w z hw hz]
  split_ifs <;> simp

/-- Finite COM partial-trace algebra after the genuine cell adjoint/ladder
identities. Relative labels are not made orthogonal or scalarized. -/
theorem finite_ladder_partial_trace {A B : Type*} [Fintype A] [Fintype B]
    (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] (L : ℕ)
    (w : A → ℕ → ℂ → ℂ) (z : B → ℕ → ℂ → ℂ)
    (hw : ∀ a, IsLadderFamily G theta k (w a))
    (hz : ∀ b, IsLadderFamily G theta k (z b))
    (C : (A × Fin L) → (B × Fin L) → ℂ) :
    (∫ R, ∑ u : A × Fin L, ∑ v : B × Fin L,
      C u v * (conj (normalizedLevel (w u.1) u.2 R) * normalizedLevel (z v.1) v.2 R)
      ∂cellMeasure G 2) =
    ((2/(k:ℝ) : ℝ) : ℂ) * ∑ u : A × Fin L, ∑ b : B,
      C u (b,u.2) * cellInner G k (w u.1 0) (z b 0) := by
  classical
  have hi (u : A × Fin L) (v : B × Fin L) : Integrable (fun R =>
      C u v * (conj (normalizedLevel (w u.1) u.2 R) * normalizedLevel (z v.1) v.2 R))
      (cellMeasure G 2) := by
    apply continuous_integrable_cellMeasure
    apply Continuous.const_mul
    apply Continuous.mul
    · exact Complex.continuous_conj.comp (((hw u.1).smooth u.2).continuous.const_smul _)
    · exact ((hz v.1).smooth v.2).continuous.const_smul _
  rw [integral_finsetSum Finset.univ (fun u _ => integrable_finsetSum Finset.univ (fun v _ => hi u v))]
  simp_rw [integral_finsetSum Finset.univ (fun v _ => hi _ v), integral_const_mul]
  change (∑ u : A × Fin L, ∑ v : B × Fin L,
    C u v * cellInner G 2 (normalizedLevel (w u.1) u.2) (normalizedLevel (z v.1) v.2)) = _
  simp_rw [normalized_ladder_mu2 G theta k _ _ (hw _) (hz _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_ite, mul_zero, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

#print axioms finite_ladder_partial_trace
#print axioms normalized_ladder_cellInner
#print axioms cellIntegral_two_eq_charge
#print axioms normalized_ladder_mu2
#print axioms vacuum_descendant_inner_zero
#print axioms ladder_cellInner
end TorusLean.Shared.ParameterLadderIntegration
