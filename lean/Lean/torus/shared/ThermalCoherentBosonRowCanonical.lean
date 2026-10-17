import torus.shared.ThermalCoherentBosonRowDecode

/-! The literal decoded physical row on the full Nat-labelled polynomial core.
This is conjugation of the original differential words, with the factorial
variable metric and positive pair-COM normalization both retained. No finite
occupation compression or reconstructed matrix defines the operator. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.BosonFiniteCertificate TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR
open scoped BigOperators

private theorem one_body_source (i j : ℕ) :
    normalWord (K := ℂ) [i] [j] = (create i).comp (annihilate j) := by
  apply LinearMap.ext
  intro f
  simp only [normalWord,wordPolynomial,annihilateWord,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,LinearMap.comp_apply,
    LinearMap.id_apply,LinearMap.mulLeft_apply,create]

private theorem spectator_column_source (t p j : ℕ) :
    (paperColumnWordOperator t (some (p,j)) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) =
      (normalWord [p+j-t] [j]).comp (paperColumnWordOperator p none) := by
  apply LinearMap.ext
  intro f
  simp only [paperColumnWordOperator,LinearMap.comp_apply,nat_linear_list_sum_apply,
    map_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  simp only [normalWord,wordPolynomial,annihilateWord,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,one_mul,LinearMap.comp_apply,
    LinearMap.id_apply,LinearMap.mulLeft_apply]
  rw [annihilate_commute a j,annihilate_commute (p-a) j]

private theorem conjugate_smul (c : ℂ) (A : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero (c • A) =
      c • conjugateOperator factorialRootNat factorialRootNat_ne_zero A := by
  apply LinearMap.ext
  intro f
  simp [conjugateOperator]

private theorem alpha_scale (t p j : ℕ) (c : ℤ) :
    (alphaOf t p j c : ℂ) * natPairNormalization p =
      ((c:ℂ)/1000000000000) * (factorialRootNat (p+j-t) / factorialRootNat j) := by
  rw [← pairScale_cast]
  have h : alphaOf t p j c * pairScale p =
      ((c:ℝ)/1000000000000) *
        (Real.sqrt ((p+j-t).factorial:ℝ) / Real.sqrt (j.factorial:ℝ)) := by
    unfold alphaOf
    have hp := ne_of_gt (pairScale_pos p)
    have hj : Real.sqrt (j.factorial:ℝ) ≠ 0 := by positivity
    field_simp [hp,hj]
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [factorialRootNat] using hc

/-- The decoded pure pair is the actual normalized planar COM pair operator. -/
theorem canonical_pair_decode (t : ℕ) (c : ℤ) :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero
      (((c:ℂ)/1000000000000) • paperColumnWordOperator t none) =
      (lambdaOf t c : ℂ) • (natPairNormalization t • canonicalPairNat t) := by
  rw [conjugate_smul,← canonicalPairNat_eq_conjugate,smul_smul]
  congr 1
  have h := congrArg (fun x : ℝ => (x:ℂ)) (lambdaOf_decode t c)
  push_cast at h
  rw [pairScale_cast] at h
  exact h.symm

/-- Exact created/annihilated spectator, with the true i!/j! scale and CCR order. -/
theorem canonical_spectator_decode (t p j : ℕ) (c : ℤ) :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero
      (((c:ℂ)/1000000000000) • paperColumnWordOperator t (some (p,j))) =
      (alphaOf t p j c : ℂ) •
        (create (p+j-t)).comp ((annihilate j).comp
          (natPairNormalization p • canonicalPairNat p)) := by
  rw [conjugate_smul,spectator_column_source,conjugateOperator_comp,
    conjugateOperator_one_body,← canonicalPairNat_eq_conjugate,
    one_body_source]
  simp only [LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,
    LinearMap.comp_assoc]
  rw [alpha_scale]

/-- Physical decoded column with its original signed integer, used only to
state the exact source sum. The pair operators are the previously defined ones. -/
def decodedCanonicalColumn (t : ℕ) (term : Option (ℕ × ℕ) × ℤ) :
    Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  match term.1 with
  | none => (lambdaOf t term.2 : ℂ) •
      (natPairNormalization t • canonicalPairNat t)
  | some (p,j) => (alphaOf t p j term.2 : ℂ) •
      (create (p+j-t)).comp ((annihilate j).comp
        (natPairNormalization p • canonicalPairNat p))

theorem canonicalNatRow_decoded_zip (t : ℕ) (row : List ℤ) :
    canonicalNatRow t row =
      (((columns t).zip row).map (decodedCanonicalColumn t)).sum := by
  rw [canonicalNatRow,paperRowWordOperator,conjugateOperator_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨col,c⟩ _
  cases col with
  | none => exact canonical_pair_decode t c
  | some q => exact canonical_spectator_decode t q.1 q.2 c

private theorem zip_sum_get {A B V : Type*} [AddCommMonoid V]
    (l : List A) (r : List B) (h : l.length = r.length) (F : A × B → V) :
    ((l.zip r).map F).sum =
      ∑ a : Fin l.length, F (l.get a,r.get ⟨a.val,by rw [← h]; exact a.isLt⟩) := by
  have hz : l.zip r = List.ofFn (fun a : Fin l.length =>
      (l.get a,r.get ⟨a.val,by rw [← h]; exact a.isLt⟩)) := by
    apply List.ext_getElem
    · simp [h]
    · intro n hn hm
      simp only [List.getElem_zip,List.getElem_ofFn,List.get_eq_getElem]
  rw [hz,List.map_ofFn,Fin.sum_ofFn]
  simp only [Function.comp_def]

/-- Every original row, now in the exact canonical creation/annihilation form
used by the physical substitution; all finite particle numbers are included. -/
theorem canonicalNatRow_decoded (ρ : RowIndex) :
    canonicalNatRow ρ.1.val (rowData ρ) =
      (rowLambda ρ : ℂ) • (natPairNormalization ρ.1.val • canonicalPairNat ρ.1.val) +
      ∑ a : EntryIndex ρ, (rowAlpha ρ a : ℂ) •
        (create (entryJet ρ a)).comp ((annihilate (entryPair ρ a).2).comp
          (natPairNormalization (entryPair ρ a).1 • canonicalPairNat (entryPair ρ a).1)) := by
  have hc : columns ρ.1.val = none :: (columns ρ.1.val).tail := rfl
  have hz : (columns ρ.1.val).zip (rowData ρ) =
      (none,rowInteger (rowData ρ) 0) ::
        ((columns ρ.1.val).tail.zip (rowData ρ).tail) := by
    rw [hc]
    cases hr : rowData ρ with
    | nil =>
      have h := rowData_length ρ
      rw [hr,hc] at h
      simp at h
    | cons c rest => simp [rowInteger]
  rw [canonicalNatRow_decoded_zip,hz,List.map_cons,List.sum_cons]
  change (rowLambda ρ : ℂ) • (natPairNormalization ρ.1.val • canonicalPairNat ρ.1.val) +
      (((columns ρ.1.val).tail.zip (rowData ρ).tail).map
        (decodedCanonicalColumn ρ.1.val)).sum = _
  congr 1
  have hl : (columns ρ.1.val).tail.length = (rowData ρ).tail.length := by
    simp only [List.length_tail,rowData_length]
  rw [zip_sum_get _ _ hl]
  apply Finset.sum_congr rfl
  intro a _
  have ha : a.val+1 < (rowData ρ).length := by
    have h := a.isLt
    simp only [List.length_tail] at h
    rw [rowData_length]
    omega
  have hi : (rowData ρ).tail.get ⟨a.val,by rw [← hl]; exact a.isLt⟩ =
      entryInteger ρ a := by
    simp only [entryInteger,rowInteger,List.get_eq_getElem,List.getElem_tail,
      List.getElem?_eq_getElem ha,Option.getD_some]
  rw [(entry_support ρ a).1,hi]
  rfl

#print axioms canonical_pair_decode
#print axioms canonical_spectator_decode
#print axioms canonicalNatRow_decoded_zip
#print axioms canonicalNatRow_decoded
end TorusLean.Shared.ThermalCoherentBosonRows
