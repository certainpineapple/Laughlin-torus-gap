import torus.shared.PlaneJetMembership
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Fixed-order differentiation of the original entire image series.
All convergence hypotheses below are discharged for the actual stripped
images. No bound uniform in derivative order or lattice geometry is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetDerivativeSum

open Filter TorusLean.Geometry TorusLean.Shared.PlaneJetMembership

/-- Locally uniform convergence of entire functions survives every fixed
number of derivatives. -/
theorem locallyUniform_iteratedDeriv {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, Differentiable ℂ (F i))
    (hlim : TendstoLocallyUniformlyOn F f l Set.univ) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i))
      (iteratedDeriv n f) l Set.univ := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hlim
  | succ n ih =>
    have hd : ∀ i, Differentiable ℂ (iteratedDeriv n (F i)) :=
      fun i => (hF i).contDiff.differentiable_iteratedDeriv' n
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall fun i => (hd i).differentiableOn) isOpen_univ

/-- A fixed derivative commutes with an entire, locally uniformly convergent
series. This conclusion includes actual summability, not a bare `tsum` equality. -/
theorem hasSum_iteratedDeriv_of_locallyUniform {ι : Type*}
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i))
    (hlim : TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun z => ∑ i ∈ s, F i z) f atTop Set.univ)
    (n : ℕ) (z : ℂ) :
    HasSum (fun i => iteratedDeriv n (F i) z) (iteratedDeriv n f z) := by
  have hs : ∀ s : Finset ι, Differentiable ℂ (fun z => ∑ i ∈ s, F i z) :=
    fun s => Differentiable.fun_sum fun i _ => hF i
  have ht := (locallyUniform_iteratedDeriv hs hlim n).tendsto_at (Set.mem_univ z)
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, iteratedDeriv n (F i) z) atTop _
  convert ht using 1
  ext s
  exact (iteratedDeriv_fun_sum fun i _ => (hF i).contDiff.contDiffAt).symm

theorem planeJetStrippedImages_tendstoLocallyUniformlyOn
    (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (ℤ × ℤ) => fun z => ∑ p ∈ s, planeJetStrippedImage G theta j R p z)
      (fun z => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p z)
      atTop Set.univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z _
  refine ⟨Metric.closedBall (0 : ℂ) (‖z‖ + 1), ?_,
    planeJetStrippedImages_tendstoUniformlyOn G theta j R (‖z‖ + 1) (by positivity)⟩
  apply mem_nhdsWithin_of_mem_nhds
  apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ?_) Metric.ball_subset_closedBall
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-- Actual all-natural-order image derivative exchange, at every point,
with original inverse character, magnetic translations, and sqrt(j!) seed. -/
theorem planeJetStrippedImages_hasSum_iteratedDeriv
    (G : Geometry) (theta : Twist) (j n : ℕ) (R z : ℂ) :
    HasSum (fun p : ℤ × ℤ => iteratedDeriv n (planeJetStrippedImage G theta j R p) z)
      (iteratedDeriv n (fun w => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p w) z) :=
  hasSum_iteratedDeriv_of_locallyUniform _ _
    (planeJetStrippedImage_differentiable G theta j R)
    (planeJetStrippedImages_tendstoLocallyUniformlyOn G theta j R) n z

#print axioms locallyUniform_iteratedDeriv
#print axioms hasSum_iteratedDeriv_of_locallyUniform
#print axioms planeJetStrippedImages_tendstoLocallyUniformlyOn
#print axioms planeJetStrippedImages_hasSum_iteratedDeriv

end TorusLean.Shared.PlaneJetDerivativeSum
