import torus.shared.BosonFiniteCertificateActualThree
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonThreeBodyLift

noncomputable def k300occ : Fin 1 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 0 1]

def k300counts : Matrix (Fin 1) (Fin 9) ℕ := !![3, 0, 0, 0, 0, 0, 0, 0, 0]

theorem k300_occupation_apply : ∀ a j, k300occ a j = k300counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k300occ, k300counts, Finsupp.single_apply]

theorem k300_occupation_source_word : ∀ a j, k300occ a j = (p300basis a).count j.val := by
  intro a j
  rw [k300_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k300counts, p300basis]

theorem k300_occupation_injective : Function.Injective k300occ := by
  have hi : Function.Injective (fun a : Fin 1 => k300counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k300_occupation_apply] using hh

theorem k300_particle_degree : ∀ a, (k300occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k300occ, map_add, Finsupp.degree_single]

noncomputable def k300metricRaw : Fin 1 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k300occ a)

def k300metric : Fin 1 → ℕ := ![6]

theorem k300_metric_reconstructed : k300metricRaw = k300metric := by
  funext a
  fin_cases a <;> norm_num [k300metricRaw, occupationMetricWeight, k300occ, k300metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k300F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![6]

def k300J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/6)]

theorem k300_gram_reconstructed :
    b300relativeᵀ * Matrix.diagonal (fun a => (k300metric a : ℚ)) * b300relative = k300F := by decide +kernel

theorem k300_inverse_left : k300J * k300F = 1 := by decide +kernel

theorem k300_inverse_right : k300F * k300J = 1 := by decide +kernel

theorem k300_inverse_symmetric : k300Jᵀ = k300J := by decide +kernel

noncomputable def k300family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k300occ k300_particle_degree
    (fun a => (b300relative a j : ℂ))

#print axioms k300_occupation_source_word
#print axioms k300_occupation_injective
#print axioms k300_particle_degree
#print axioms k300_metric_reconstructed
#print axioms k300_gram_reconstructed
#print axioms k300_inverse_left
#print axioms k300_inverse_right
#print axioms k300_inverse_symmetric

noncomputable def k301occ : Fin 1 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 1 1]

def k301counts : Matrix (Fin 1) (Fin 9) ℕ := !![2, 1, 0, 0, 0, 0, 0, 0, 0]

theorem k301_occupation_apply : ∀ a j, k301occ a j = k301counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k301occ, k301counts, Finsupp.single_apply]

theorem k301_occupation_source_word : ∀ a j, k301occ a j = (p301basis a).count j.val := by
  intro a j
  rw [k301_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k301counts, p301basis]

theorem k301_occupation_injective : Function.Injective k301occ := by
  have hi : Function.Injective (fun a : Fin 1 => k301counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k301_occupation_apply] using hh

theorem k301_particle_degree : ∀ a, (k301occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k301occ, map_add, Finsupp.degree_single]

noncomputable def k301metricRaw : Fin 1 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k301occ a)

def k301metric : Fin 1 → ℕ := ![2]

theorem k301_metric_reconstructed : k301metricRaw = k301metric := by
  funext a
  fin_cases a <;> norm_num [k301metricRaw, occupationMetricWeight, k301occ, k301metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k301F : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

def k301J : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

theorem k301_gram_reconstructed :
    b301relativeᵀ * Matrix.diagonal (fun a => (k301metric a : ℚ)) * b301relative = k301F := by decide +kernel

theorem k301_inverse_left : k301J * k301F = 1 := by decide +kernel

theorem k301_inverse_right : k301F * k301J = 1 := by decide +kernel

theorem k301_inverse_symmetric : k301Jᵀ = k301J := by decide +kernel

noncomputable def k301family : Fin 0 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k301occ k301_particle_degree
    (fun a => (b301relative a j : ℂ))

#print axioms k301_occupation_source_word
#print axioms k301_occupation_injective
#print axioms k301_particle_degree
#print axioms k301_metric_reconstructed
#print axioms k301_gram_reconstructed
#print axioms k301_inverse_left
#print axioms k301_inverse_right
#print axioms k301_inverse_symmetric

noncomputable def k302occ : Fin 2 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 1 1]

def k302counts : Matrix (Fin 2) (Fin 9) ℕ := !![2, 0, 1, 0, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0, 0]

theorem k302_occupation_apply : ∀ a j, k302occ a j = k302counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k302occ, k302counts, Finsupp.single_apply]

theorem k302_occupation_source_word : ∀ a j, k302occ a j = (p302basis a).count j.val := by
  intro a j
  rw [k302_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k302counts, p302basis]

theorem k302_occupation_injective : Function.Injective k302occ := by
  have hi : Function.Injective (fun a : Fin 2 => k302counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k302_occupation_apply] using hh

theorem k302_particle_degree : ∀ a, (k302occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k302occ, map_add, Finsupp.degree_single]

noncomputable def k302metricRaw : Fin 2 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k302occ a)

def k302metric : Fin 2 → ℕ := ![4, 2]

theorem k302_metric_reconstructed : k302metricRaw = k302metric := by
  funext a
  fin_cases a <;> norm_num [k302metricRaw, occupationMetricWeight, k302occ, k302metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k302F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![6]

def k302J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/6)]

theorem k302_gram_reconstructed :
    b302relativeᵀ * Matrix.diagonal (fun a => (k302metric a : ℚ)) * b302relative = k302F := by decide +kernel

theorem k302_inverse_left : k302J * k302F = 1 := by decide +kernel

theorem k302_inverse_right : k302F * k302J = 1 := by decide +kernel

theorem k302_inverse_symmetric : k302Jᵀ = k302J := by decide +kernel

noncomputable def k302family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k302occ k302_particle_degree
    (fun a => (b302relative a j : ℂ))

#print axioms k302_occupation_source_word
#print axioms k302_occupation_injective
#print axioms k302_particle_degree
#print axioms k302_metric_reconstructed
#print axioms k302_gram_reconstructed
#print axioms k302_inverse_left
#print axioms k302_inverse_right
#print axioms k302_inverse_symmetric

noncomputable def k303occ : Fin 3 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 3 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 1 1]

def k303counts : Matrix (Fin 3) (Fin 9) ℕ := !![2, 0, 0, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0, 0; 0, 3, 0, 0, 0, 0, 0, 0, 0]

theorem k303_occupation_apply : ∀ a j, k303occ a j = k303counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k303occ, k303counts, Finsupp.single_apply]

theorem k303_occupation_source_word : ∀ a j, k303occ a j = (p303basis a).count j.val := by
  intro a j
  rw [k303_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k303counts, p303basis]

theorem k303_occupation_injective : Function.Injective k303occ := by
  have hi : Function.Injective (fun a : Fin 3 => k303counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k303_occupation_apply] using hh

theorem k303_particle_degree : ∀ a, (k303occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k303occ, map_add, Finsupp.degree_single]

noncomputable def k303metricRaw : Fin 3 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k303occ a)

def k303metric : Fin 3 → ℕ := ![12, 2, 6]

theorem k303_metric_reconstructed : k303metricRaw = k303metric := by
  funext a
  fin_cases a <;> norm_num [k303metricRaw, occupationMetricWeight, k303occ, k303metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k303F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(27/2)]

def k303J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(2/27)]

theorem k303_gram_reconstructed :
    b303relativeᵀ * Matrix.diagonal (fun a => (k303metric a : ℚ)) * b303relative = k303F := by decide +kernel

theorem k303_inverse_left : k303J * k303F = 1 := by decide +kernel

theorem k303_inverse_right : k303F * k303J = 1 := by decide +kernel

theorem k303_inverse_symmetric : k303Jᵀ = k303J := by decide +kernel

noncomputable def k303family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k303occ k303_particle_degree
    (fun a => (b303relative a j : ℂ))

#print axioms k303_occupation_source_word
#print axioms k303_occupation_injective
#print axioms k303_particle_degree
#print axioms k303_metric_reconstructed
#print axioms k303_gram_reconstructed
#print axioms k303_inverse_left
#print axioms k303_inverse_right
#print axioms k303_inverse_symmetric

noncomputable def k304occ : Fin 4 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 4 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 2 1]

def k304counts : Matrix (Fin 4) (Fin 9) ℕ := !![2, 0, 0, 0, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0, 0]

theorem k304_occupation_apply : ∀ a j, k304occ a j = k304counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k304occ, k304counts, Finsupp.single_apply]

theorem k304_occupation_source_word : ∀ a j, k304occ a j = (p304basis a).count j.val := by
  intro a j
  rw [k304_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k304counts, p304basis]

theorem k304_occupation_injective : Function.Injective k304occ := by
  have hi : Function.Injective (fun a : Fin 4 => k304counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k304_occupation_apply] using hh

theorem k304_particle_degree : ∀ a, (k304occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k304occ, map_add, Finsupp.degree_single]

noncomputable def k304metricRaw : Fin 4 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k304occ a)

def k304metric : Fin 4 → ℕ := ![48, 6, 8, 4]

theorem k304_metric_reconstructed : k304metricRaw = k304metric := by
  funext a
  fin_cases a <;> norm_num [k304metricRaw, occupationMetricWeight, k304occ, k304metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k304F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![24]

def k304J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/24)]

theorem k304_gram_reconstructed :
    b304relativeᵀ * Matrix.diagonal (fun a => (k304metric a : ℚ)) * b304relative = k304F := by decide +kernel

theorem k304_inverse_left : k304J * k304F = 1 := by decide +kernel

theorem k304_inverse_right : k304F * k304J = 1 := by decide +kernel

theorem k304_inverse_symmetric : k304Jᵀ = k304J := by decide +kernel

noncomputable def k304family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k304occ k304_particle_degree
    (fun a => (b304relative a j : ℂ))

#print axioms k304_occupation_source_word
#print axioms k304_occupation_injective
#print axioms k304_particle_degree
#print axioms k304_metric_reconstructed
#print axioms k304_gram_reconstructed
#print axioms k304_inverse_left
#print axioms k304_inverse_right
#print axioms k304_inverse_symmetric

noncomputable def k305occ : Fin 5 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 5 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 4 1,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 3 1,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 2 1]

def k305counts : Matrix (Fin 5) (Fin 9) ℕ := !![2, 0, 0, 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0, 0]

theorem k305_occupation_apply : ∀ a j, k305occ a j = k305counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k305occ, k305counts, Finsupp.single_apply]

theorem k305_occupation_source_word : ∀ a j, k305occ a j = (p305basis a).count j.val := by
  intro a j
  rw [k305_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k305counts, p305basis]

theorem k305_occupation_injective : Function.Injective k305occ := by
  have hi : Function.Injective (fun a : Fin 5 => k305counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k305_occupation_apply] using hh

theorem k305_particle_degree : ∀ a, (k305occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k305occ, map_add, Finsupp.degree_single]

noncomputable def k305metricRaw : Fin 5 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k305occ a)

def k305metric : Fin 5 → ℕ := ![240, 24, 12, 12, 8]

theorem k305_metric_reconstructed : k305metricRaw = k305metric := by
  funext a
  fin_cases a <;> norm_num [k305metricRaw, occupationMetricWeight, k305occ, k305metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k305F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![54]

def k305J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/54)]

theorem k305_gram_reconstructed :
    b305relativeᵀ * Matrix.diagonal (fun a => (k305metric a : ℚ)) * b305relative = k305F := by decide +kernel

theorem k305_inverse_left : k305J * k305F = 1 := by decide +kernel

theorem k305_inverse_right : k305F * k305J = 1 := by decide +kernel

theorem k305_inverse_symmetric : k305Jᵀ = k305J := by decide +kernel

noncomputable def k305family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k305occ k305_particle_degree
    (fun a => (b305relative a j : ℂ))

#print axioms k305_occupation_source_word
#print axioms k305_occupation_injective
#print axioms k305_particle_degree
#print axioms k305_metric_reconstructed
#print axioms k305_gram_reconstructed
#print axioms k305_inverse_left
#print axioms k305_inverse_right
#print axioms k305_inverse_symmetric

noncomputable def k306occ : Fin 7 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 6 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 5 1,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 4 1,
    Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 3 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 4 1,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1,
    Finsupp.single 2 1 + Finsupp.single 2 1 + Finsupp.single 2 1]

def k306counts : Matrix (Fin 7) (Fin 9) ℕ := !![2, 0, 0, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0, 0; 0, 0, 3, 0, 0, 0, 0, 0, 0]

theorem k306_occupation_apply : ∀ a j, k306occ a j = k306counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k306occ, k306counts, Finsupp.single_apply]

theorem k306_occupation_source_word : ∀ a j, k306occ a j = (p306basis a).count j.val := by
  intro a j
  rw [k306_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k306counts, p306basis]

theorem k306_occupation_injective : Function.Injective k306occ := by
  have hi : Function.Injective (fun a : Fin 7 => k306counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k306_occupation_apply] using hh

theorem k306_particle_degree : ∀ a, (k306occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k306occ, map_add, Finsupp.degree_single]

noncomputable def k306metricRaw : Fin 7 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k306occ a)

def k306metric : Fin 7 → ℕ := ![1440, 120, 48, 72, 48, 12, 48]

theorem k306_metric_reconstructed : k306metricRaw = k306metric := by
  funext a
  fin_cases a <;> norm_num [k306metricRaw, occupationMetricWeight, k306occ, k306metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k306F : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1188/5), (-468/5);
    (-468/5), (1068/5)]

def k306J : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(89/17496), (13/5832);
    (13/5832), (11/1944)]

theorem k306_gram_reconstructed :
    b306relativeᵀ * Matrix.diagonal (fun a => (k306metric a : ℚ)) * b306relative = k306F := by decide +kernel

theorem k306_inverse_left : k306J * k306F = 1 := by decide +kernel

theorem k306_inverse_right : k306F * k306J = 1 := by decide +kernel

theorem k306_inverse_symmetric : k306Jᵀ = k306J := by decide +kernel

noncomputable def k306family : Fin 2 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k306occ k306_particle_degree
    (fun a => (b306relative a j : ℂ))

#print axioms k306_occupation_source_word
#print axioms k306_occupation_injective
#print axioms k306_particle_degree
#print axioms k306_metric_reconstructed
#print axioms k306_gram_reconstructed
#print axioms k306_inverse_left
#print axioms k306_inverse_right
#print axioms k306_inverse_symmetric

noncomputable def k307occ : Fin 8 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 7 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 6 1,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 5 1,
    Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 5 1,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 4 1,
    Finsupp.single 1 1 + Finsupp.single 3 1 + Finsupp.single 3 1,
    Finsupp.single 2 1 + Finsupp.single 2 1 + Finsupp.single 3 1]

def k307counts : Matrix (Fin 8) (Fin 9) ℕ := !![2, 0, 0, 0, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 1, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0, 0]

theorem k307_occupation_apply : ∀ a j, k307occ a j = k307counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k307occ, k307counts, Finsupp.single_apply]

theorem k307_occupation_source_word : ∀ a j, k307occ a j = (p307basis a).count j.val := by
  intro a j
  rw [k307_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k307counts, p307basis]

theorem k307_occupation_injective : Function.Injective k307occ := by
  have hi : Function.Injective (fun a : Fin 8 => k307counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k307_occupation_apply] using hh

theorem k307_particle_degree : ∀ a, (k307occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k307occ, map_add, Finsupp.degree_single]

noncomputable def k307metricRaw : Fin 8 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k307occ a)

def k307metric : Fin 8 → ℕ := ![10080, 720, 240, 144, 240, 48, 72, 48]

theorem k307_metric_reconstructed : k307metricRaw = k307metric := by
  funext a
  fin_cases a <;> norm_num [k307metricRaw, occupationMetricWeight, k307occ, k307metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k307F : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(2187/5)]

def k307J : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(5/2187)]

theorem k307_gram_reconstructed :
    b307relativeᵀ * Matrix.diagonal (fun a => (k307metric a : ℚ)) * b307relative = k307F := by decide +kernel

theorem k307_inverse_left : k307J * k307F = 1 := by decide +kernel

theorem k307_inverse_right : k307F * k307J = 1 := by decide +kernel

theorem k307_inverse_symmetric : k307Jᵀ = k307J := by decide +kernel

noncomputable def k307family : Fin 1 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k307occ k307_particle_degree
    (fun a => (b307relative a j : ℂ))

#print axioms k307_occupation_source_word
#print axioms k307_occupation_injective
#print axioms k307_particle_degree
#print axioms k307_metric_reconstructed
#print axioms k307_gram_reconstructed
#print axioms k307_inverse_left
#print axioms k307_inverse_right
#print axioms k307_inverse_symmetric

noncomputable def k308occ : Fin 10 → (Fin 9 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 8 1,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 7 1,
    Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 6 1,
    Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 5 1,
    Finsupp.single 0 1 + Finsupp.single 4 1 + Finsupp.single 4 1,
    Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 6 1,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 5 1,
    Finsupp.single 1 1 + Finsupp.single 3 1 + Finsupp.single 4 1,
    Finsupp.single 2 1 + Finsupp.single 2 1 + Finsupp.single 4 1,
    Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 3 1]

def k308counts : Matrix (Fin 10) (Fin 9) ℕ := !![2, 0, 0, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0, 0]

theorem k308_occupation_apply : ∀ a j, k308occ a j = k308counts a j := by
  intro a j
  fin_cases a <;> fin_cases j <;> norm_num [k308occ, k308counts, Finsupp.single_apply]

theorem k308_occupation_source_word : ∀ a j, k308occ a j = (p308basis a).count j.val := by
  intro a j
  rw [k308_occupation_apply]
  fin_cases a <;> fin_cases j <;> norm_num [k308counts, p308basis]

theorem k308_occupation_injective : Function.Injective k308occ := by
  have hi : Function.Injective (fun a : Fin 10 => k308counts a) := by decide +kernel
  intro a b h
  apply hi
  funext j
  have hh := congrArg (fun q : Fin 9 →₀ ℕ => q j) h
  simpa only [k308_occupation_apply] using hh

theorem k308_particle_degree : ∀ a, (k308occ a).degree = 3 := by
  intro a
  fin_cases a <;> norm_num [k308occ, map_add, Finsupp.degree_single]

noncomputable def k308metricRaw : Fin 10 → ℕ := fun a => occupationMetricWeight (factorialScale 8) (k308occ a)

def k308metric : Fin 10 → ℕ := ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144]

theorem k308_metric_reconstructed : k308metricRaw = k308metric := by
  funext a
  fin_cases a <;> norm_num [k308metricRaw, occupationMetricWeight, k308occ, k308metric, factorialScale, Fin.prod_univ_succ, Nat.factorial]

def k308F : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(148608/35), (-27648/35);
    (-27648/35), (69228/35)]

def k308J : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(641/2519424), (2/19683);
    (2/19683), (43/78732)]

theorem k308_gram_reconstructed :
    b308relativeᵀ * Matrix.diagonal (fun a => (k308metric a : ℚ)) * b308relative = k308F := by decide +kernel

theorem k308_inverse_left : k308J * k308F = 1 := by decide +kernel

theorem k308_inverse_right : k308F * k308J = 1 := by decide +kernel

theorem k308_inverse_symmetric : k308Jᵀ = k308J := by decide +kernel

noncomputable def k308family : Fin 2 → ThreeSector (Fin 9) := fun j =>
  canonicalThreeBlock (factorialScale 8) k308occ k308_particle_degree
    (fun a => (b308relative a j : ℂ))

#print axioms k308_occupation_source_word
#print axioms k308_occupation_injective
#print axioms k308_particle_degree
#print axioms k308_metric_reconstructed
#print axioms k308_gram_reconstructed
#print axioms k308_inverse_left
#print axioms k308_inverse_right
#print axioms k308_inverse_symmetric

end TorusLean.BosonFiniteCertificate
