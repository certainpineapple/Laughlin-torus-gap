import torus.geometry.LatticePhase
import torus.shared.Inputs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import LaguerreEnvelope

/-! Concrete plane-square packing for the actual magnetic period map.
The systole is the infimum prescribed by torus/INTERFACE.md. No jet norm,
oscillator displacement identity or cell-inner-product identity is assumed. -/

set_option autoImplicit false

namespace TorusLean.Fermion.LatticePacking

open scoped BigOperators
open TorusLean.Geometry

noncomputable section

def period (G : TorusLean.Shared.Geometry) (p : ℤ × ℤ) : ℂ :=
  latticePeriod G.omega1 G.omega2 p

def nonzeroLengths (G : TorusLean.Shared.Geometry) : Set ℝ :=
  {r | ∃ p : ℤ × ℤ, p ≠ 0 ∧ ‖period G p‖ = r}

/-- Physical systole: infimum over every nonzero integer period, not just the basis. -/
def systole (G : TorusLean.Shared.Geometry) : ℝ := sInf (nonzeroLengths G)

theorem legal_area_pos (G : TorusLean.Shared.Geometry) :
    0 < latticeArea G.omega1 G.omega2 := by
  unfold latticeArea
  rw [G.area]
  exact mul_pos Real.pi_pos (Nat.cast_pos.mpr G.flux_pos)

theorem systole_ge_iff (G : TorusLean.Shared.Geometry) (L : ℝ) :
    L ≤ systole G ↔ ∀ p : ℤ × ℤ, p ≠ 0 → L ≤ ‖period G p‖ := by
  have hb : BddBelow (nonzeroLengths G) := ⟨0, by
    rintro r ⟨p, hp, rfl⟩
    exact norm_nonneg _⟩
  have hn : (nonzeroLengths G).Nonempty :=
    ⟨‖period G (1, 0)‖, (1, 0), by simp, rfl⟩
  constructor
  · intro h p hp
    exact h.trans (csInf_le hb ⟨p, hp, rfl⟩)
  · intro h
    exact le_csInf hn (by rintro r ⟨p, hp, rfl⟩; exact h p hp)

theorem period_separated (G : TorusLean.Shared.Geometry) (hG : 1 ≤ systole G)
    (p q : ℤ × ℤ) (hpq : p ≠ q) : 1 ≤ ‖period G p - period G q‖ := by
  have h := (systole_ge_iff G 1).mp hG (p - q) (sub_ne_zero.mpr hpq)
  have he : period G (p - q) = period G p - period G q := by
    simp only [period, latticePeriod, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring
  rwa [he] at h

/-- Axis-aligned squares in physical coordinates, of side 1/2. -/
def squareCode (z : ℂ) : ℤ × ℤ := (⌊2 * z.re⌋, ⌊2 * z.im⌋)

private theorem same_floor_close (x y : ℝ) (h : ⌊2*x⌋ = ⌊2*y⌋) :
    |x - y| < 1 / 2 := by
  have hx := Int.floor_le (2*x)
  have hy := Int.floor_le (2*y)
  have hx' := Int.lt_floor_add_one (2*x)
  have hy' := Int.lt_floor_add_one (2*y)
  rw [h] at hx hx'
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem squareCode_injective (G : TorusLean.Shared.Geometry) (hG : 1 ≤ systole G)
    (z : ℂ) : Function.Injective (fun p : ℤ × ℤ => squareCode (period G p - z)) := by
  intro p q h
  by_contra hpq
  have hr := same_floor_close (period G p - z).re (period G q - z).re
    (congrArg Prod.fst h)
  have hi := same_floor_close (period G p - z).im (period G q - z).im
    (congrArg Prod.snd h)
  simp only [Complex.sub_re, Complex.sub_im, sub_sub_sub_cancel_right] at hr hi
  have hr2 : ((period G p).re - (period G q).re)^2 < (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mpr hr
  have hi2 : ((period G p).im - (period G q).im)^2 < (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mpr hi
  have hs := period_separated G hG p q hpq
  have hn := norm_sq (period G p - period G q)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  nlinarith [sq_nonneg (‖period G p - period G q‖ - 1)]

private theorem floor_in_interval (x R : ℝ) (_hR : 0 ≤ R) (hx : |x| ≤ R) :
    ⌊2*x⌋ ∈ Finset.Icc (-⌈2*R⌉) ⌈2*R⌉ := by
  rw [Finset.mem_Icc]
  have hb := abs_le.mp hx
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith [Int.le_ceil (2*R)]
  · apply Int.floor_le_iff.mpr
    linarith [Int.le_ceil (2*R)]

theorem finite_ball_count (G : TorusLean.Shared.Geometry) (hG : 1 ≤ systole G)
    (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, ‖period G p - z‖ ≤ R) :
    (s.card : ℝ) ≤ 64 * (1 + R^2) := by
  classical
  let I := Finset.Icc (-⌈2*R⌉) ⌈2*R⌉
  have hin : s.image (fun p => squareCode (period G p - z)) ⊆ I ×ˢ I := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr
      ⟨floor_in_interval _ R hR ((Complex.abs_re_le_norm _).trans (hs p hp)),
       floor_in_interval _ R hR ((Complex.abs_im_le_norm _).trans (hs p hp))⟩
  have hc := Finset.card_le_card hin
  rw [Finset.card_image_of_injective _ (squareCode_injective G hG z),
    Finset.card_product] at hc
  have hI : (I.card : ℝ) = 2 * (⌈2*R⌉ : ℝ) + 1 := by
    have hceil : (0 : ℤ) ≤ ⌈2*R⌉ := Int.ceil_nonneg (by positivity)
    have hcard := Int.card_Icc_of_le (a := -⌈2*R⌉) (b := ⌈2*R⌉) (by omega)
    have hcardR : (I.card : ℝ) = (⌈2*R⌉ : ℝ) + 1 - (-(⌈2*R⌉ : ℝ)) := by
      exact_mod_cast hcard
    linarith
  have hcast : (s.card : ℝ) ≤ (I.card : ℝ)*(I.card : ℝ) := by exact_mod_cast hc
  rw [← pow_two] at hcast
  rw [hI] at hcast
  have hceil := Int.ceil_lt_add_one (2*R)
  have hceil0 : (0 : ℝ) ≤ (⌈2*R⌉ : ℝ) :=
    le_trans (by positivity : (0 : ℝ) ≤ 2*R) (Int.le_ceil _)
  have hcsq : (2*(⌈2*R⌉ : ℝ)+1)^2 ≤ (4*R+3)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    linarith
  nlinarith [sq_nonneg (R - 1)]

/-- Fixed geometric weight on the ambient square grid. No geometry parameter. -/
def axisWeight (k : ℤ) : ℝ := Real.exp (-((k.natAbs : ℕ) : ℝ) / 32)

def gridWeight (c : ℤ × ℤ) : ℝ :=
  Real.exp (1/8) * (axisWeight c.1 * axisWeight c.2)

def gaussianConstant : ℝ := ∑' c : ℤ × ℤ, gridWeight c

theorem axisWeight_summable : Summable axisWeight := by
  have hq : |Real.exp (-1/32 : ℝ)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hnat : Summable (fun n : ℕ => axisWeight (n : ℤ)) := by
    convert summable_geometric_of_abs_lt_one hq using 1
    funext n
    simp only [axisWeight, Int.natAbs_natCast]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply Summable.of_nat_of_neg hnat
  simpa only [axisWeight, Int.natAbs_neg] using hnat

theorem gridWeight_summable : Summable gridWeight :=
  (axisWeight_summable.mul_of_nonneg axisWeight_summable
    (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)).mul_left _

theorem gaussianConstant_nonneg : 0 ≤ gaussianConstant :=
  tsum_nonneg (fun _ => mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))

private theorem floor_abs_bound (x : ℝ) : (⌊2*x⌋.natAbs : ℝ) ≤ 4*x^2 + 2 := by
  have hf := Int.floor_le (2*x)
  have hf' := Int.lt_floor_add_one (2*x)
  have hx := abs_le.mp (le_refl |x|)
  have ha : |(⌊2*x⌋ : ℝ)| ≤ 2*|x| + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : (⌊2*x⌋.natAbs : ℝ) = |(⌊2*x⌋ : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [he]
  nlinarith [sq_nonneg (2*|x| - 1), sq_abs x, abs_nonneg x]

theorem gaussian_le_gridWeight (w : ℂ) :
    Real.exp (-‖w‖^2 / 8) ≤ gridWeight (squareCode w) := by
  have hr := floor_abs_bound w.re
  have hi := floor_abs_bound w.im
  rw [gridWeight, axisWeight, axisWeight, squareCode, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [norm_sq]
  dsimp
  linarith

theorem lattice_gaussian_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-‖period G p - z‖^2 / 8)) := by
  exact (gridWeight_summable.comp_injective (squareCode_injective G hG z)).of_nonneg_of_le
    (fun _ => Real.exp_nonneg _) (fun _ => gaussian_le_gridWeight _)

theorem lattice_gaussian_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) :
    (∑' p : ℤ × ℤ, Real.exp (-‖period G p - z‖^2 / 8)) ≤ gaussianConstant := by
  exact (lattice_gaussian_summable G hG z).tsum_le_tsum_of_inj
    (fun p => squareCode (period G p - z)) (squareCode_injective G hG z)
    (fun _ _ => mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
    (fun _ => gaussian_le_gridWeight _) gridWeight_summable

theorem finite_gaussian_tail (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (s : Finset (ℤ × ℤ)) (hs : ∀ p ∈ s, R ≤ ‖period G p - z‖) :
    (∑ p ∈ s, Real.exp (-‖period G p - z‖^2 / 4)) ≤
      Real.exp (-R^2 / 8) * gaussianConstant := by
  have hpoint (p : ℤ × ℤ) (hp : p ∈ s) :
      Real.exp (-‖period G p - z‖^2 / 4) ≤
        Real.exp (-R^2 / 8) * Real.exp (-‖period G p - z‖^2 / 8) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ hR (hs p hp) 2
    linarith
  calc
    _ ≤ ∑ p ∈ s, Real.exp (-R^2 / 8) * Real.exp (-‖period G p - z‖^2 / 8) :=
      Finset.sum_le_sum hpoint
    _ = Real.exp (-R^2 / 8) * ∑ p ∈ s, Real.exp (-‖period G p - z‖^2 / 8) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-R^2 / 8) * gaussianConstant := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact ((lattice_gaussian_summable G hG z).sum_le_tsum s
        (fun _ _ => Real.exp_nonneg _)).trans (lattice_gaussian_bound G hG z)

/-- Gaussian tail outside the actual radius R, with equality assigned to the tail. -/
def gaussianTail (G : TorusLean.Shared.Geometry) (z : ℂ) (R : ℝ) (p : ℤ × ℤ) : ℝ :=
  if R ≤ ‖period G p - z‖ then Real.exp (-‖period G p - z‖^2 / 4) else 0

private theorem gaussianTail_finite_sum (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, gaussianTail G z R p) ≤ Real.exp (-R^2 / 8) * gaussianConstant := by
  classical
  have h := finite_gaussian_tail G hG z R hR
    (s.filter (fun p => R ≤ ‖period G p - z‖))
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)
  simpa only [gaussianTail, ← Finset.sum_filter] using h

theorem gaussianTail_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (gaussianTail G z R) := by
  apply summable_of_sum_le (fun p => by unfold gaussianTail; split_ifs <;> positivity)
  exact gaussianTail_finite_sum G hG z R hR

theorem gaussianTail_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∑' p : ℤ × ℤ, gaussianTail G z R p) ≤
      Real.exp (-R^2 / 8) * gaussianConstant := by
  exact (gaussianTail_summable G hG z R hR).tsum_le_of_sum_le
    (gaussianTail_finite_sum G hG z R hR)

theorem inner_ball_count (G : TorusLean.Shared.Geometry) (hG : 1 ≤ systole G)
    (z : ℂ) (j : ℕ) (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, ‖period G p - z‖^2 < 64*(j : ℝ)) :
    (s.card : ℝ) ≤ 4096*(1 + (j : ℝ)) := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have h := finite_ball_count G hG z (8 * Real.sqrt (j : ℝ))
    (by positivity) s (by
      intro p hp
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      nlinarith [hs p hp])
  nlinarith

/-- Actual Laguerre diagonal factor on the outer region; zero on the inner region. -/
def farLaguerreTerm (G : TorusLean.Shared.Geometry) (z : ℂ) (j : ℕ) (p : ℤ × ℤ) : ℝ :=
  if 64*(j : ℝ) ≤ ‖period G p - z‖^2 then
    |Real.exp (-‖period G p - z‖^2 / 2) * JetEnvelope.paperLaguerre j (‖period G p - z‖^2)|
  else 0

private theorem farLaguerreTerm_le (G : TorusLean.Shared.Geometry) (z : ℂ)
    (j : ℕ) (p : ℤ × ℤ) :
    farLaguerreTerm G z j p ≤
      Real.exp (-8*(j : ℝ)) * Real.exp (-‖period G p - z‖^2 / 8) := by
  unfold farLaguerreTerm
  split_ifs with h
  · apply (JetEnvelope.laguerre_displacement_factor_far_bound j _ h).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  · exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)

theorem farLaguerre_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    Summable (farLaguerreTerm G z j) := by
  apply ((lattice_gaussian_summable G hG z).mul_left (Real.exp (-8*(j : ℝ)))).of_nonneg_of_le
  · intro p
    unfold farLaguerreTerm
    split_ifs <;> positivity
  · exact farLaguerreTerm_le G z j

theorem farLaguerre_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    (∑' p : ℤ × ℤ, farLaguerreTerm G z j p) ≤
      Real.exp (-8*(j : ℝ)) * gaussianConstant := by
  calc
    _ ≤ ∑' p : ℤ × ℤ,
        Real.exp (-8*(j : ℝ)) * Real.exp (-‖period G p - z‖^2 / 8) :=
      (farLaguerre_summable G hG z j).tsum_le_tsum (farLaguerreTerm_le G z j)
        ((lattice_gaussian_summable G hG z).mul_left _)
    _ = Real.exp (-8*(j : ℝ)) *
        ∑' p : ℤ × ℤ, Real.exp (-‖period G p - z‖^2 / 8) :=
      (lattice_gaussian_summable G hG z).tsum_mul_left _
    _ ≤ _ := mul_le_mul_of_nonneg_left (lattice_gaussian_bound G hG z) (Real.exp_nonneg _)

/-- Count one for every inner-region lattice point, including arbitrary center.
This is an indicator, not an assumed bound on a physical oscillator matrix element. -/
def innerIndicator (G : TorusLean.Shared.Geometry) (z : ℂ) (j : ℕ) (p : ℤ × ℤ) : ℝ :=
  if ‖period G p - z‖^2 < 64*(j : ℝ) then 1 else 0

private theorem innerIndicator_finite_sum (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, innerIndicator G z j p) ≤ 4096*(1 + (j : ℝ)) := by
  classical
  have h := inner_ball_count G hG z j
    (s.filter (fun p => ‖period G p - z‖^2 < 64*(j : ℝ)))
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)
  simpa only [innerIndicator, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one] using h

theorem innerIndicator_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) : Summable (innerIndicator G z j) := by
  apply summable_of_sum_le (fun p => by unfold innerIndicator; split_ifs <;> norm_num)
  exact innerIndicator_finite_sum G hG z j

theorem innerIndicator_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    (∑' p : ℤ × ℤ, innerIndicator G z j p) ≤ 4096*(1 + (j : ℝ)) := by
  exact (innerIndicator_summable G hG z j).tsum_le_of_sum_le
    (innerIndicator_finite_sum G hG z j)

/-- Concrete inner/outer scalar envelope. The actual inner unitary/Laguerre
modulus input is proved in PlaneJetDisplacement and consumed in LatticeLaguerreSum.
The actual torus jet cell-inner expansion remains open. -/
def splitLaguerreEnvelope (G : TorusLean.Shared.Geometry) (z : ℂ) (j : ℕ)
    (p : ℤ × ℤ) : ℝ := innerIndicator G z j p + farLaguerreTerm G z j p

theorem splitLaguerreEnvelope_summable (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) : Summable (splitLaguerreEnvelope G z j) :=
  (innerIndicator_summable G hG z j).add (farLaguerre_summable G hG z j)

theorem splitLaguerreEnvelope_bound (G : TorusLean.Shared.Geometry)
    (hG : 1 ≤ systole G) (z : ℂ) (j : ℕ) :
    (∑' p : ℤ × ℤ, splitLaguerreEnvelope G z j p) ≤
      (4096 + gaussianConstant)*(1 + (j : ℝ)) := by
  unfold splitLaguerreEnvelope
  rw [(innerIndicator_summable G hG z j).tsum_add
    (farLaguerre_summable G hG z j)]
  have hf := farLaguerre_bound G hG z j
  have hi := innerIndicator_bound G hG z j
  have he : Real.exp (-8*(j : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))])
  have hc := mul_le_mul_of_nonneg_right he gaussianConstant_nonneg
  have hj : 0 ≤ (j : ℝ) * gaussianConstant := mul_nonneg (Nat.cast_nonneg _) gaussianConstant_nonneg
  nlinarith

end
end TorusLean.Fermion.LatticePacking
