import torus.shared.BosonFiniteCertificateNatCOMBasis300
import torus.shared.BosonFiniteCertificateNatCOMBasis301
import torus.shared.BosonFiniteCertificateNatCOMBasis302
import torus.shared.BosonFiniteCertificateNatCOMBasis303
import torus.shared.BosonFiniteCertificateNatCOMBasis304
import torus.shared.BosonFiniteCertificateNatCOMBasis305
import torus.shared.BosonFiniteCertificateNatCOMBasis306
import torus.shared.BosonFiniteCertificateNatCOMBasis307
import torus.shared.BosonFiniteCertificateNatCOMBasis308

/-! Exact indexing of the complete descendant families by original relative
column and COM level. The degree-one relative family is empty and remains
present in the dependent index type. No Gram or cross-source entry is removed. -/
set_option autoImplicit false
set_option maxRecDepth 32768
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate

def natCOMRelativeDimension : Fin 9 → ℕ := ![1,0,1,1,1,1,2,1,2]

/-- Starting position of each original relative fiber in a complete COM family. -/
def natCOMRelativeOffset : Fin 9 → ℕ := ![0,1,1,2,3,4,5,7,8]

def natCOMRelativeColumn (z : Fin 9) : Fin (natCOMRelativeDimension z) → Core ℕ ℂ := by
  refine Fin.cases ?_ ?_ z
  · exact fun a => MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ Pi.single a 1))
  · intro z
    refine Fin.cases ?_ ?_ z
    · exact fun a => MvPolynomial.rename Fin.val
        (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ Pi.single a 1))
    · intro z
      refine Fin.cases ?_ ?_ z
      · exact fun a => MvPolynomial.rename Fin.val
          (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ Pi.single a 1))
      · intro z
        refine Fin.cases ?_ ?_ z
        · exact fun a => MvPolynomial.rename Fin.val
            (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ Pi.single a 1))
        · intro z
          refine Fin.cases ?_ ?_ z
          · exact fun a => MvPolynomial.rename Fin.val
              (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ Pi.single a 1))
          · intro z
            refine Fin.cases ?_ ?_ z
            · exact fun a => MvPolynomial.rename Fin.val
                (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ Pi.single a 1))
            · intro z
              refine Fin.cases ?_ ?_ z
              · exact fun a => MvPolynomial.rename Fin.val
                  (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ Pi.single a 1))
              · intro z
                refine Fin.cases ?_ ?_ z
                · exact fun a => MvPolynomial.rename Fin.val
                    (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ Pi.single a 1))
                · intro z
                  refine Fin.cases ?_ ?_ z
                  · exact fun a => MvPolynomial.rename Fin.val
                      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ Pi.single a 1))
                  · intro z
                    exact Fin.elim0 z

/-- Bijection including the empty z=1 relative fiber. -/
def k300COMIndexLabel : Fin 1 → Σ z : Fin 1,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩]

theorem k300_COMIndexLabel_bijective : Function.Bijective k300COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 1,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 1) : decode (k300COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩

def k300COMRelativeDegree (i : Fin 1) : Fin 9 :=
  ⟨(k300COMIndexLabel i).1.val,by have h := (k300COMIndexLabel i).1.isLt; omega⟩

def k300COMLevel (i : Fin 1) : ℕ := 0 - (k300COMRelativeDegree i).val

theorem k300_COM_level_add_relative_degree (i : Fin 1) :
    k300COMLevel i + (k300COMRelativeDegree i).val = 0 := by
  have h := (k300COMIndexLabel i).1.isLt
  simp only [k300COMLevel,k300COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k300_COMDescendantFamily_labelled (i : Fin 1) :
    k300COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k300COMLevel i])
        (natCOMRelativeColumn (k300COMRelativeDegree i) (k300COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k300_COMIndexLabel_bijective
#print axioms k300_COM_level_add_relative_degree
#print axioms k300_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k301COMIndexLabel : Fin 1 → Σ z : Fin 2,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩]

theorem k301_COMIndexLabel_bijective : Function.Bijective k301COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 2,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 1) : decode (k301COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a

def k301COMRelativeDegree (i : Fin 1) : Fin 9 :=
  ⟨(k301COMIndexLabel i).1.val,by have h := (k301COMIndexLabel i).1.isLt; omega⟩

def k301COMLevel (i : Fin 1) : ℕ := 1 - (k301COMRelativeDegree i).val

theorem k301_COM_level_add_relative_degree (i : Fin 1) :
    k301COMLevel i + (k301COMRelativeDegree i).val = 1 := by
  have h := (k301COMIndexLabel i).1.isLt
  simp only [k301COMLevel,k301COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k301_COMDescendantFamily_labelled (i : Fin 1) :
    k301COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k301COMLevel i])
        (natCOMRelativeColumn (k301COMRelativeDegree i) (k301COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k301_COMIndexLabel_bijective
#print axioms k301_COM_level_add_relative_degree
#print axioms k301_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k302COMIndexLabel : Fin 2 → Σ z : Fin 3,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩]

theorem k302_COMIndexLabel_bijective : Function.Bijective k302COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 3,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 2) : decode (k302COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩

def k302COMRelativeDegree (i : Fin 2) : Fin 9 :=
  ⟨(k302COMIndexLabel i).1.val,by have h := (k302COMIndexLabel i).1.isLt; omega⟩

def k302COMLevel (i : Fin 2) : ℕ := 2 - (k302COMRelativeDegree i).val

theorem k302_COM_level_add_relative_degree (i : Fin 2) :
    k302COMLevel i + (k302COMRelativeDegree i).val = 2 := by
  have h := (k302COMIndexLabel i).1.isLt
  simp only [k302COMLevel,k302COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k302_COMDescendantFamily_labelled (i : Fin 2) :
    k302COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k302COMLevel i])
        (natCOMRelativeColumn (k302COMRelativeDegree i) (k302COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k302_COMIndexLabel_bijective
#print axioms k302_COM_level_add_relative_degree
#print axioms k302_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k303COMIndexLabel : Fin 3 → Σ z : Fin 4,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩]

theorem k303_COMIndexLabel_bijective : Function.Bijective k303COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 4,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 3) : decode (k303COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩

def k303COMRelativeDegree (i : Fin 3) : Fin 9 :=
  ⟨(k303COMIndexLabel i).1.val,by have h := (k303COMIndexLabel i).1.isLt; omega⟩

def k303COMLevel (i : Fin 3) : ℕ := 3 - (k303COMRelativeDegree i).val

theorem k303_COM_level_add_relative_degree (i : Fin 3) :
    k303COMLevel i + (k303COMRelativeDegree i).val = 3 := by
  have h := (k303COMIndexLabel i).1.isLt
  simp only [k303COMLevel,k303COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k303_COMDescendantFamily_labelled (i : Fin 3) :
    k303COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k303COMLevel i])
        (natCOMRelativeColumn (k303COMRelativeDegree i) (k303COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k303_COMIndexLabel_bijective
#print axioms k303_COM_level_add_relative_degree
#print axioms k303_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k304COMIndexLabel : Fin 4 → Σ z : Fin 5,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩]

theorem k304_COMIndexLabel_bijective : Function.Bijective k304COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 5,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 4) : decode (k304COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨3,rfl⟩

def k304COMRelativeDegree (i : Fin 4) : Fin 9 :=
  ⟨(k304COMIndexLabel i).1.val,by have h := (k304COMIndexLabel i).1.isLt; omega⟩

def k304COMLevel (i : Fin 4) : ℕ := 4 - (k304COMRelativeDegree i).val

theorem k304_COM_level_add_relative_degree (i : Fin 4) :
    k304COMLevel i + (k304COMRelativeDegree i).val = 4 := by
  have h := (k304COMIndexLabel i).1.isLt
  simp only [k304COMLevel,k304COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k304_COMDescendantFamily_labelled (i : Fin 4) :
    k304COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k304COMLevel i])
        (natCOMRelativeColumn (k304COMRelativeDegree i) (k304COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k304_COMIndexLabel_bijective
#print axioms k304_COM_level_add_relative_degree
#print axioms k304_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k305COMIndexLabel : Fin 5 → Σ z : Fin 6,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨5,⟨0,by decide⟩⟩]

theorem k305_COMIndexLabel_bijective : Function.Bijective k305COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 6,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 5) : decode (k305COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨3,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨4,rfl⟩

def k305COMRelativeDegree (i : Fin 5) : Fin 9 :=
  ⟨(k305COMIndexLabel i).1.val,by have h := (k305COMIndexLabel i).1.isLt; omega⟩

def k305COMLevel (i : Fin 5) : ℕ := 5 - (k305COMRelativeDegree i).val

theorem k305_COM_level_add_relative_degree (i : Fin 5) :
    k305COMLevel i + (k305COMRelativeDegree i).val = 5 := by
  have h := (k305COMIndexLabel i).1.isLt
  simp only [k305COMLevel,k305COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k305_COMDescendantFamily_labelled (i : Fin 5) :
    k305COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k305COMLevel i])
        (natCOMRelativeColumn (k305COMRelativeDegree i) (k305COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k305_COMIndexLabel_bijective
#print axioms k305_COM_level_add_relative_degree
#print axioms k305_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k306COMIndexLabel : Fin 7 → Σ z : Fin 7,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨5,⟨0,by decide⟩⟩, ⟨6,⟨0,by decide⟩⟩, ⟨6,⟨1,by decide⟩⟩]

theorem k306_COMIndexLabel_bijective : Function.Bijective k306COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 7,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 7) : decode (k306COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨3,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨4,rfl⟩
    · change Fin 2 at a
      fin_cases a
      · exact ⟨5,rfl⟩
      · exact ⟨6,rfl⟩

def k306COMRelativeDegree (i : Fin 7) : Fin 9 :=
  ⟨(k306COMIndexLabel i).1.val,by have h := (k306COMIndexLabel i).1.isLt; omega⟩

def k306COMLevel (i : Fin 7) : ℕ := 6 - (k306COMRelativeDegree i).val

theorem k306_COM_level_add_relative_degree (i : Fin 7) :
    k306COMLevel i + (k306COMRelativeDegree i).val = 6 := by
  have h := (k306COMIndexLabel i).1.isLt
  simp only [k306COMLevel,k306COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k306_COMDescendantFamily_labelled (i : Fin 7) :
    k306COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k306COMLevel i])
        (natCOMRelativeColumn (k306COMRelativeDegree i) (k306COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k306_COMIndexLabel_bijective
#print axioms k306_COM_level_add_relative_degree
#print axioms k306_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k307COMIndexLabel : Fin 8 → Σ z : Fin 8,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨5,⟨0,by decide⟩⟩, ⟨6,⟨0,by decide⟩⟩, ⟨6,⟨1,by decide⟩⟩, ⟨7,⟨0,by decide⟩⟩]

theorem k307_COMIndexLabel_bijective : Function.Bijective k307COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 8,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 8) : decode (k307COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨3,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨4,rfl⟩
    · change Fin 2 at a
      fin_cases a
      · exact ⟨5,rfl⟩
      · exact ⟨6,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨7,rfl⟩

def k307COMRelativeDegree (i : Fin 8) : Fin 9 :=
  ⟨(k307COMIndexLabel i).1.val,by have h := (k307COMIndexLabel i).1.isLt; omega⟩

def k307COMLevel (i : Fin 8) : ℕ := 7 - (k307COMRelativeDegree i).val

theorem k307_COM_level_add_relative_degree (i : Fin 8) :
    k307COMLevel i + (k307COMRelativeDegree i).val = 7 := by
  have h := (k307COMIndexLabel i).1.isLt
  simp only [k307COMLevel,k307COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k307_COMDescendantFamily_labelled (i : Fin 8) :
    k307COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k307COMLevel i])
        (natCOMRelativeColumn (k307COMRelativeDegree i) (k307COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k307_COMIndexLabel_bijective
#print axioms k307_COM_level_add_relative_degree
#print axioms k307_COMDescendantFamily_labelled

/-- Bijection including the empty z=1 relative fiber. -/
def k308COMIndexLabel : Fin 10 → Σ z : Fin 9,
    Fin (natCOMRelativeDimension ⟨z.val,by omega⟩) :=
  ![⟨0,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩, ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨5,⟨0,by decide⟩⟩, ⟨6,⟨0,by decide⟩⟩, ⟨6,⟨1,by decide⟩⟩, ⟨7,⟨0,by decide⟩⟩, ⟨8,⟨0,by decide⟩⟩, ⟨8,⟨1,by decide⟩⟩]

theorem k308_COMIndexLabel_bijective : Function.Bijective k308COMIndexLabel := by
  constructor
  · let decode (x : Σ z : Fin 9,
        Fin (natCOMRelativeDimension ⟨z.val,by omega⟩)) : ℕ :=
        natCOMRelativeOffset ⟨x.1.val,by have hx := x.1.isLt; omega⟩ + x.2.val
    have hdecode (i : Fin 10) : decode (k308COMIndexLabel i) = i.val := by
      fin_cases i <;> rfl
    intro i j h
    apply Fin.ext
    simpa only [hdecode] using congrArg decode h
  · rintro ⟨z,a⟩
    fin_cases z
    · change Fin 1 at a
      fin_cases a
      · exact ⟨0,rfl⟩
    · change Fin 0 at a
      exact Fin.elim0 a
    · change Fin 1 at a
      fin_cases a
      · exact ⟨1,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨2,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨3,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨4,rfl⟩
    · change Fin 2 at a
      fin_cases a
      · exact ⟨5,rfl⟩
      · exact ⟨6,rfl⟩
    · change Fin 1 at a
      fin_cases a
      · exact ⟨7,rfl⟩
    · change Fin 2 at a
      fin_cases a
      · exact ⟨8,rfl⟩
      · exact ⟨9,rfl⟩

def k308COMRelativeDegree (i : Fin 10) : Fin 9 :=
  ⟨(k308COMIndexLabel i).1.val,by have h := (k308COMIndexLabel i).1.isLt; omega⟩

def k308COMLevel (i : Fin 10) : ℕ := 8 - (k308COMRelativeDegree i).val

theorem k308_COM_level_add_relative_degree (i : Fin 10) :
    k308COMLevel i + (k308COMRelativeDegree i).val = 8 := by
  have h := (k308COMIndexLabel i).1.isLt
  simp only [k308COMLevel,k308COMRelativeDegree]
  omega

/-- The labelled vector is the actual unnormalized COM iterate of the original relative column. -/
theorem k308_COMDescendantFamily_labelled (i : Fin 10) :
    k308COMDescendantFamily i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k308COMLevel i])
        (natCOMRelativeColumn (k308COMRelativeDegree i) (k308COMIndexLabel i).2) := by
  fin_cases i <;> rfl

#print axioms k308_COMIndexLabel_bijective
#print axioms k308_COM_level_add_relative_degree
#print axioms k308_COMDescendantFamily_labelled
end TorusLean.BosonFiniteCertificate
