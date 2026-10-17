import torus.shared.PhysicalFermionCarrier
import torus.shared.NormalJetBridge
import torus.shared.PlaneJetReproducing
import torus.shared.PhysicalBosonContactForm

/-!
# Original first normal derivative contact on actual fermion functions

The map is defined by the original covariant m=1 normal jet, with literal
particle coordinates and unchanged charge-two/spectator cell measures.
Its finite orbital Wronskian formula and integrability are proved below.
The finite contact Gram form is not yet an OAI CAR lift identification.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionM1Contact

open MeasureTheory TorusLean.Geometry
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.NormalJetBridge TorusLean.Shared.PlaneJetReproducing
open scoped ComplexConjugate

/-- Literal insertion of two independent particle positions before coincidence. -/
def insertPair (N : ℕ) (y : Configuration N) (p : ℂ × ℂ) : Configuration (N+2) :=
  Fin.cons p.1 (Fin.cons p.2 y)

/-- The original m=1 covariant derivative, with every spectator retained. -/
def m1Contact (N : ℕ) (f : Configuration (N+2) → ℂ)
    (x : ContactConfiguration N) : ℂ :=
  localNormalJet 1 1 1 (fun p => f (insertPair N x.2 p)) x.1

/-- Canonical entire orbital factor; no arbitrary witness is part of the interface. -/
def orbitalFactor (G : Geometry) (theta : Twist) (i : OrbitalIndex G theta) : ℂ → ℂ :=
  canonicalRawStripped G theta (orbitalBasis G theta i)

theorem orbitalFactor_differentiable (G : Geometry) (theta : Twist)
    (i : OrbitalIndex G theta) : Differentiable ℂ (orbitalFactor G theta i) :=
  canonicalRawStripped_differentiable G theta (orbitalBasis G theta i)

theorem orbitalFactor_eq (G : Geometry) (theta : Twist)
    (i : OrbitalIndex G theta) (z : ℂ) :
    (orbitalBasis G theta i).val z = gaussianFactor 1 z * orbitalFactor G theta i z :=
  canonicalRawStripped_factor G theta (orbitalBasis G theta i) z

/-- Unrescaled physical Wronskian coefficient of an ordered orbital pair. -/
def pairM1 (G : Geometry) (theta : Twist) (i j : OrbitalIndex G theta) (R : ℂ) : ℂ :=
  (jetScale 1 1 1)⁻¹ * gaussianFactor 2 R *
    ((deriv (orbitalFactor G theta i) R * orbitalFactor G theta j R -
       orbitalFactor G theta i R * deriv (orbitalFactor G theta j) R) / 2)

theorem normal_product_derivative (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) :
    deriv (fun r : ℂ => orbitalFactor G theta i (R + r/2) *
      orbitalFactor G theta j (R-r/2)) 0 =
      (deriv (orbitalFactor G theta i) R * orbitalFactor G theta j R -
       orbitalFactor G theta i R * deriv (orbitalFactor G theta j) R) / 2 := by
  have hplus : HasDerivAt (fun r : ℂ => R + r/2) (1/2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_add R
  have hminus : HasDerivAt (fun r : ℂ => R-r/2) (-(1/2)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_sub R
  have hi : HasDerivAt (orbitalFactor G theta i) (deriv (orbitalFactor G theta i) R) (R+0/2) := by
    simpa using (orbitalFactor_differentiable G theta i R).hasDerivAt
  have hj : HasDerivAt (orbitalFactor G theta j) (deriv (orbitalFactor G theta j) R) (R-0/2) := by
    simpa using (orbitalFactor_differentiable G theta j R).hasDerivAt
  have h := ((hi.comp 0 hplus).fun_mul (hj.comp 0 hminus)).deriv
  simp only [Function.comp_apply, zero_div, add_zero, sub_zero] at h
  rw [h]
  ring

/-- Gaussian cancellation makes the corrected pair slice genuinely entire. -/
theorem corrected_word_slice (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N+2)) (x : ContactConfiguration N) (r : ℂ) :
    Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
      wordFunction G theta (N+2) w
        (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r)) =
      (gaussianFactor 2 x.1 * wordFunction G theta N (tailWord G theta N w) x.2) *
        (orbitalFactor G theta (w 0) (x.1+r/2) *
         orbitalFactor G theta (w 1) (x.1-r/2)) := by
  simp only [wordFunction, insertPair, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.succ_zero_eq_one, tailWord]
  rw [orbitalFactor_eq G theta (w 0), orbitalFactor_eq G theta (w 1)]
  have hcancel := jacobi_covariant_gaussian_cancel 1 1 (by norm_num : (1:ℝ)+1 ≠ 0) x.1 r
  norm_num only at hcancel
  rw [show Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
      (gaussianFactor 1 (jacobiFirst 1 1 x.1 r) * orbitalFactor G theta (w 0) (jacobiFirst 1 1 x.1 r) *
       (gaussianFactor 1 (jacobiSecond 1 1 x.1 r) * orbitalFactor G theta (w 1) (jacobiSecond 1 1 x.1 r) *
        ∏ a, (orbitalBasis G theta (w a.succ.succ)).val (x.2 a))) =
    (Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
      (gaussianFactor 1 (jacobiFirst 1 1 x.1 r) * gaussianFactor 1 (jacobiSecond 1 1 x.1 r))) *
      (∏ a, (orbitalBasis G theta (w a.succ.succ)).val (x.2 a)) *
      (orbitalFactor G theta (w 0) (jacobiFirst 1 1 x.1 r) *
       orbitalFactor G theta (w 1) (jacobiSecond 1 1 x.1 r)) by ring]
  rw [hcancel, (equal_charge_coordinates x.1 r).1, (equal_charge_coordinates x.1 r).2]

theorem corrected_word_differentiable (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N+2)) (x : ContactConfiguration N) :
    Differentiable ℂ (fun r : ℂ =>
      Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
        wordFunction G theta (N+2) w
          (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r))) := by
  simp_rw [corrected_word_slice]
  apply Differentiable.const_mul
  exact ((orbitalFactor_differentiable G theta (w 0)).comp
    ((differentiable_const x.1).add (differentiable_id.div_const 2))).mul
      ((orbitalFactor_differentiable G theta (w 1)).comp
        ((differentiable_const x.1).sub (differentiable_id.div_const 2)))

theorem m1Contact_word (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N+2)) (x : ContactConfiguration N) :
    m1Contact N (wordFunction G theta (N+2) w) x =
      pairM1 G theta (w 0) (w 1) x.1 * wordFunction G theta N (tailWord G theta N w) x.2 := by
  unfold m1Contact localNormalJet
  simp only [iteratedDeriv_one]
  simp_rw [corrected_word_slice]
  rw [deriv_const_mul_field, normal_product_derivative]
  unfold pairM1 jetScale
  ring

/-- Actual derivative of the reconstructed physical function equals its finite
orbital derivative expansion; derivative/sum interchange is proved here. -/
theorem m1Contact_tensor (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta (N+2) → ℂ) (x : ContactConfiguration N) :
    m1Contact N (tensorFunction G theta (N+2) c) x =
      ∑ w, c w * (pairM1 G theta (w 0) (w 1) x.1 *
        wordFunction G theta N (tailWord G theta N w) x.2) := by
  classical
  unfold m1Contact localNormalJet
  simp only [iteratedDeriv_one, tensorFunction_apply]
  have hexpand : (fun r : ℂ => Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
      ∑ w, c w * wordFunction G theta (N+2) w
        (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r))) =
      (fun r => ∑ w, c w * (Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
        wordFunction G theta (N+2) w
          (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r)))) := by
    funext r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hexpand, deriv_fun_sum (fun w _ =>
    (corrected_word_differentiable G theta N w x 0).const_mul (c w)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [deriv_const_mul_field]
  have h := m1Contact_word G theta N w x
  unfold m1Contact localNormalJet at h
  simp only [iteratedDeriv_one] at h
  rw [mul_left_comm, h]

theorem pairM1_continuous (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) : Continuous (pairM1 G theta i j) := by
  unfold pairM1
  exact ((gaussianFactor_continuous 2).const_mul _).mul
    (((orbitalFactor_differentiable G theta i).deriv.continuous.mul
       (orbitalFactor_differentiable G theta j).continuous).sub
      ((orbitalFactor_differentiable G theta i).continuous.mul
       (orbitalFactor_differentiable G theta j).deriv.continuous) |>.div_const 2)

theorem pairM1_swap (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) : pairM1 G theta j i R = - pairM1 G theta i j R := by
  unfold pairM1
  ring

theorem m1_word_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N+2)) :
    Integrable (fun x => conj (m1Contact N (wordFunction G theta (N+2) w) x) *
      m1Contact N (wordFunction G theta (N+2) v) x) (contactMeasure G N) := by
  have hi := Integrable.mul_prod
    (continuous_integrable_cellMeasure G 2
      ((Complex.continuous_conj.comp (pairM1_continuous G theta (w 0) (w 1))).mul
        (pairM1_continuous G theta (v 0) (v 1))))
    (wordFunction_inner_integrable G theta N (tailWord G theta N w) (tailWord G theta N v))
  change Integrable _ ((cellMeasure G 2).prod (sectorMeasure G N))
  convert hi using 1
  funext x
  simp only [m1Contact_word, map_mul, Pi.mul_apply, Function.comp_apply]
  ring

/-- Exact m=1 pair Gram in the original contact and spectator measures. -/
theorem m1Contact_word_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N+2)) :
    contactInner G N (m1Contact N (wordFunction G theta (N+2) w))
      (m1Contact N (wordFunction G theta (N+2) v)) =
      cellInner G 2 (pairM1 G theta (w 0) (w 1)) (pairM1 G theta (v 0) (v 1)) *
        (if tailWord G theta N w = tailWord G theta N v then 1 else 0) := by
  classical
  have hF := integral_prod_mul (μ := cellMeasure G 2) (ν := sectorMeasure G N)
    (fun R => conj (pairM1 G theta (w 0) (w 1) R) * pairM1 G theta (v 0) (v 1) R)
    (fun y => conj (wordFunction G theta N (tailWord G theta N w) y) *
      wordFunction G theta N (tailWord G theta N v) y)
  calc
    _ = cellInner G 2 (pairM1 G theta (w 0) (w 1)) (pairM1 G theta (v 0) (v 1)) *
        sectorInner G N (wordFunction G theta N (tailWord G theta N w))
          (wordFunction G theta N (tailWord G theta N v)) := by
      unfold contactInner cellInner sectorInner contactMeasure
      simp only [m1Contact_word, map_mul]
      convert hF using 1
      congr 1
      funext x
      ring
    _ = _ := by rw [wordFunction_inner]

/-- A finite Gram expression is derived for every full physical fermion,
with original covariant derivative and cell measures on the left. -/
theorem fullCarrier_m1_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) (x : ContactConfiguration N) :
    m1Contact N f.val x = ∑ w, ((physicalCoefficientEquiv G theta (N+2)).symm f).val w *
      (pairM1 G theta (w 0) (w 1) x.1 * wordFunction G theta N (tailWord G theta N w) x.2) := by
  have hf : tensorFunction G theta (N+2) ((physicalCoefficientEquiv G theta (N+2)).symm f).val = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta (N+2)).apply_symm_apply f)
  rw [← hf, m1Contact_tensor]

/-- The actual integrated finite m=1 Gram matrix, including spectator identity. -/
def m1Gram (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N+2)) : ℂ :=
  cellInner G 2 (pairM1 G theta (w 0) (w 1)) (pairM1 G theta (v 0) (v 1)) *
    (if tailWord G theta N w = tailWord G theta N v then 1 else 0)

theorem scaled_m1_word_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N+2)) (c d : ℂ) :
    Integrable (fun x => conj (c * m1Contact N (wordFunction G theta (N+2) w) x) *
      (d * m1Contact N (wordFunction G theta (N+2) v) x)) (contactMeasure G N) := by
  have h := (m1_word_cross_integrable G theta N w v).const_mul (conj c*d)
  convert h using 1
  funext x
  simp only [map_mul]
  ring

theorem m1Contact_tensor_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (c d : Word G theta (N+2) → ℂ) :
    contactInner G N (m1Contact N (tensorFunction G theta (N+2) c))
      (m1Contact N (tensorFunction G theta (N+2) d)) =
      ∑ w, ∑ v, conj (c w) * d v * m1Gram G theta N w v := by
  classical
  have heq (a : Word G theta (N+2) → ℂ) :
      m1Contact N (tensorFunction G theta (N+2) a) =
        fun x => ∑ w, a w * m1Contact N (wordFunction G theta (N+2) w) x := by
    funext x
    simp only [m1Contact_tensor, m1Contact_word]
  rw [heq c, heq d, contactInner_finiteSums G N Finset.univ Finset.univ _ _
    (fun w _ v _ => scaled_m1_word_cross_integrable G theta N w v (c w) (d v))]
  simp only [contactInner_const_mul, m1Contact_word_inner, m1Gram]

theorem m1Contact_tensor_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (c d : Word G theta (N+2) → ℂ) :
    Integrable (fun x => conj (m1Contact N (tensorFunction G theta (N+2) c) x) *
      m1Contact N (tensorFunction G theta (N+2) d) x) (contactMeasure G N) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun w _ =>
    integrable_finsetSum Finset.univ (fun v _ =>
      scaled_m1_word_cross_integrable G theta N w v (c w) (d v)))
  convert hi using 1
  funext x
  simp only [m1Contact_tensor, m1Contact_word, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem fullCarrier_m1_normSq_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    Integrable (fun x => ‖m1Contact N f.val x‖^2) (contactMeasure G N) := by
  let c := ((physicalCoefficientEquiv G theta (N+2)).symm f).val
  have hf : tensorFunction G theta (N+2) c = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta (N+2)).apply_symm_apply f)
  have h := (m1Contact_tensor_cross_integrable G theta N c c).re
  rw [hf] at h
  change Integrable (fun x => (conj (m1Contact N f.val x) * m1Contact N f.val x).re) _ at h
  simpa only [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem fullCarrier_m1_energy_gram (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    (∫ x, ‖m1Contact N f.val x‖^2 ∂contactMeasure G N) =
      (∑ w, ∑ v,
        conj (((physicalCoefficientEquiv G theta (N+2)).symm f).val w) *
          ((physicalCoefficientEquiv G theta (N+2)).symm f).val v * m1Gram G theta N w v).re := by
  let c := ((physicalCoefficientEquiv G theta (N+2)).symm f).val
  have hf : tensorFunction G theta (N+2) c = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta (N+2)).apply_symm_apply f)
  have hi : contactInner G N (m1Contact N f.val) (m1Contact N f.val) =
      ((∫ x, ‖m1Contact N f.val x‖^2 ∂contactMeasure G N : ℝ) : ℂ) := by
    simp only [contactInner, Complex.conj_mul', ← Complex.ofReal_pow]
    exact integral_complex_ofReal
  have hg := m1Contact_tensor_inner G theta N c c
  rw [hf, hi] at hg
  simpa only [Complex.ofReal_re] using congrArg Complex.re hg

theorem m1Contact_const_mul (N : ℕ) (a : ℂ) (f : Configuration (N+2) → ℂ)
    (x : ContactConfiguration N) :
    m1Contact N (fun z => a * f z) x = a * m1Contact N f x := by
  unfold m1Contact localNormalJet
  have heq : (fun r : ℂ => Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
      (a * f (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r)))) =
      (fun r => a * (Complex.exp ((relativeCharge 1 1 : ℂ) * (r * conj r) / 2) *
        f (insertPair N x.2 (jacobiFirst 1 1 x.1 r, jacobiSecond 1 1 x.1 r)))) := by
    funext r
    ring
  rw [heq, iteratedDeriv_const_mul_field]
  ring

theorem permutationSign_norm {N : ℕ} (σ : Equiv.Perm (Fin N)) : ‖permutationSign σ‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [permutationSign, h]

/-- The original jet at any actual particle pair a,b, before using statistics. -/
def particlePairM1 (N : ℕ) (a b : Fin (N+2)) (f : Configuration (N+2) → ℂ)
    (x : ContactConfiguration N) : ℂ :=
  localNormalJet 1 1 1 (fun p =>
    f (insertPair N x.2 p ∘ (particlePairPermutation N a b).symm)) x.1

theorem particlePairM1_norm (G : Geometry) (theta : Twist) (N : ℕ)
    (a b : Fin (N+2)) (f : PhysicalFermion G theta (N+2)) (x : ContactConfiguration N) :
    ‖particlePairM1 N a b f.val x‖ = ‖m1Contact N f.val x‖ := by
  have heq : (fun p : ℂ × ℂ => f.val (insertPair N x.2 p ∘
      (particlePairPermutation N a b).symm)) =
      (fun p => permutationSign (particlePairPermutation N a b).symm * f.val (insertPair N x.2 p)) := by
    funext p
    exact f.property.2.2 _ _
  unfold particlePairM1
  rw [heq]
  change ‖m1Contact N (fun z => permutationSign (particlePairPermutation N a b).symm * f.val z) x‖ = _
  rw [m1Contact_const_mul, norm_mul, permutationSign_norm, one_mul]

/-- Actual sum over unordered particle pairs, in the original contact measure. -/
def particleM1Energy (G : Geometry) (N : ℕ) (f : Configuration (N+2) → ℂ) : ℝ :=
  ∑ a : Fin (N+2), ∑ b : Fin (N+2), if a < b then
    ∫ x, ‖particlePairM1 N a b f x‖^2 ∂contactMeasure G N else 0

/-- The pair-count factor is derived from physical antisymmetry and the
literal derivative restriction, not supplied as a Fock normalization. -/
theorem fullCarrier_particleM1Energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    particleM1Energy G N f.val =
      ((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2 *
        (∫ x, ‖m1Contact N f.val x‖^2 ∂contactMeasure G N) := by
  unfold particleM1Energy
  simp_rw [particlePairM1_norm G theta N _ _ f]
  exact sorted_particle_pair_sum (N+2) _

/-- The empty zero- and one-particle pair sums have zero energy. -/
def actualFermionM1Energy (G : Geometry) : (N : ℕ) → (Configuration N → ℂ) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | N+2, f => particleM1Energy G N f

/-- All physical many-body m=1 contact energy is an exact finite orbital
Gram form. Exterior/CAR normal ordering is a separate, still open bridge. -/
theorem fullCarrier_particleM1Energy_gram (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    actualFermionM1Energy G (N+2) f.val =
      ((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2 *
        (∑ w, ∑ v,
          conj (((physicalCoefficientEquiv G theta (N+2)).symm f).val w) *
            ((physicalCoefficientEquiv G theta (N+2)).symm f).val v * m1Gram G theta N w v).re := by
  change particleM1Energy G N f.val = _
  rw [fullCarrier_particleM1Energy, fullCarrier_m1_energy_gram]

/-- Integrability prevents a spurious zero from the totalized Bochner integral. -/
theorem fullCarrier_m1_zero_iff_ae (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    (∫ x, ‖m1Contact N f.val x‖^2 ∂contactMeasure G N) = 0 ↔
      m1Contact N f.val =ᵐ[contactMeasure G N] 0 := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (fullCarrier_m1_normSq_integrable G theta N f)]
  simp only [Filter.EventuallyEq, Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero]

/-- This is only an a.e. contact-kernel characterization. Pointwise analytic
continuation, cubic division, and global zero-mode classification remain separate. -/
theorem fullCarrier_particleM1_zero_iff_ae (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    actualFermionM1Energy G (N+2) f.val = 0 ↔
      m1Contact N f.val =ᵐ[contactMeasure G N] 0 := by
  change particleM1Energy G N f.val = 0 ↔ _
  rw [fullCarrier_particleM1Energy, mul_eq_zero]
  have hcount : ((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2 ≠ 0 := by
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    push_cast
    apply ne_of_gt
    exact div_pos (mul_pos (by positivity) (by linarith)) (by norm_num)
  simp only [hcount, false_or]
  exact fullCarrier_m1_zero_iff_ae G theta N f

#print axioms fullCarrier_m1_zero_iff_ae
#print axioms fullCarrier_particleM1_zero_iff_ae

#print axioms m1Contact_tensor_inner
#print axioms fullCarrier_m1_normSq_integrable
#print axioms fullCarrier_m1_energy_gram
#print axioms m1Contact_const_mul
#print axioms permutationSign_norm
#print axioms particlePairM1_norm
#print axioms fullCarrier_particleM1Energy
#print axioms fullCarrier_particleM1Energy_gram

#print axioms normal_product_derivative
#print axioms corrected_word_slice
#print axioms corrected_word_differentiable
#print axioms m1Contact_word
#print axioms m1Contact_tensor
#print axioms pairM1_continuous
#print axioms pairM1_swap
#print axioms m1_word_cross_integrable
#print axioms m1Contact_word_inner
#print axioms fullCarrier_m1_expansion

end TorusLean.Shared.PhysicalFermionM1Contact
