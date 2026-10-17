import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActual

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

theorem natFourCOMIndex_card (D : Fin 17) :
    Fintype.card (Σ d : Fin (D.val+1), Fin (natFourRelativeDimensionAt D d))=
      natFourOccupationDimension D := by
  fin_cases D <;> decide +kernel

def natFourCOMIndexEquiv (D : Fin 17) :
    Fin (natFourOccupationDimension D) ≃ Σ d : Fin (D.val+1), Fin (natFourRelativeDimensionAt D d) :=
  (Fintype.equivFinOfCardEq (natFourCOMIndex_card D)).symm

/-- Original relative degree carried by a complete COM-family label. -/
def natFourCOMRelativeDegree (D : Fin 17) (i : Fin (natFourOccupationDimension D)) : Fin 17 :=
  natFourRelativeDegreeAt D (natFourCOMIndexEquiv D i).1

/-- Original relative-column label; empty relative fibers remain empty. -/
def natFourCOMRelativeColumn (D : Fin 17) (i : Fin (natFourOccupationDimension D)) :
    Fin (natFourRelativeDimension (natFourCOMRelativeDegree D i)) :=
  (natFourCOMIndexEquiv D i).2

/-- Number of true COM creation operations, with no normalization absorbed. -/
def natFourCOMLevel (D : Fin 17) (i : Fin (natFourOccupationDimension D)) : ℕ :=
  D.val-(natFourCOMIndexEquiv D i).1.val

def natFourCompleteCOMFamily (D : Fin 17) : Fin (natFourOccupationDimension D) → Core ℕ ℂ :=
  fun i => natFourCOMSigmaFamily D.val (natFourRelativeDimensionAt D)
    (fun d => natFourRelativeColumn (natFourRelativeDegreeAt D d)) (natFourCOMIndexEquiv D i)

theorem natFourCompleteCOMFamily_labelled (D : Fin 17)
    (i : Fin (natFourOccupationDimension D)) :
    natFourCompleteCOMFamily D i =
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[natFourCOMLevel D i])
        (natFourRelativeColumn (natFourCOMRelativeDegree D i) (natFourCOMRelativeColumn D i)) := rfl

theorem natFourCOMLevel_add_relative_degree (D : Fin 17)
    (i : Fin (natFourOccupationDimension D)) :
    natFourCOMLevel D i + (natFourCOMRelativeDegree D i).val = D.val := by
  have h := (natFourCOMIndexEquiv D i).1.isLt
  change D.val-(natFourCOMIndexEquiv D i).1.val+(natFourCOMIndexEquiv D i).1.val=D.val
  omega

def natFourCompleteCOMCoordinates (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ :=
  fun i j => natFourCOMFiberCoordinates D (natFourCOMIndexEquiv D j).1 i (natFourCOMIndexEquiv D j).2

theorem natFourCompleteCOMFamily_coordinates (D : Fin 17) (j : Fin (natFourOccupationDimension D)) :
    natFourCompleteCOMFamily D j=natFourWordBlock (natFourOccupationBasis D)
      (fun i => complexify (natFourCompleteCOMCoordinates D) i j) :=
  natFourCOMFiberCoordinates_actual_column D (natFourCOMIndexEquiv D j).1 (natFourCOMIndexEquiv D j).2

theorem natFourCompleteCOMFamily_gram (D : Fin 17) :
    natFamilyGram (natFourCompleteCOMFamily D)=
      (natFourCOMBlockGram D.val (natFourRelativeDimensionAt D)
        (fun d => complexify (natFourRelativeGram (natFourRelativeDegreeAt D d)))).submatrix
          (natFourCOMIndexEquiv D) (natFourCOMIndexEquiv D) := by
  apply natFourCOMSigmaFamily_reindexed_gram
  · intro d a
    exact (natFourRelativeColumn_bihomogeneous _ a).1
  · intro d a
    exact natFourRelativeColumn_lower _ a
  · intro d
    exact natFourRelativeColumn_gram _

#print axioms natFourCOMIndex_card
#print axioms natFourCompleteCOMFamily_labelled
#print axioms natFourCOMLevel_add_relative_degree
#print axioms natFourCompleteCOMFamily_coordinates
#print axioms natFourCompleteCOMFamily_gram
end TorusLean.BosonFiniteCertificate
