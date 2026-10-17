import torus.shared.BosonFiniteCertificateNatCOMBasisLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open scoped BigOperators ComplexConjugate

def natCOMRelativeGram (z : Fin 9) : Matrix (Fin (natCOMRelativeDimension z))
    (Fin (natCOMRelativeDimension z)) ℚ := by
  refine Fin.cases ?_ ?_ z
  · exact k300F
  · intro z
    refine Fin.cases ?_ ?_ z
    · exact k301F
    · intro z
      refine Fin.cases ?_ ?_ z
      · exact k302F
      · intro z
        refine Fin.cases ?_ ?_ z
        · exact k303F
        · intro z
          refine Fin.cases ?_ ?_ z
          · exact k304F
          · intro z
            refine Fin.cases ?_ ?_ z
            · exact k305F
            · intro z
              refine Fin.cases ?_ ?_ z
              · exact k306F
              · intro z
                refine Fin.cases ?_ ?_ z
                · exact k307F
                · intro z
                  refine Fin.cases ?_ ?_ z
                  · exact k308F
                  · intro z
                    exact Fin.elim0 z

def natCOMRelativeGramInverse (z : Fin 9) : Matrix (Fin (natCOMRelativeDimension z))
    (Fin (natCOMRelativeDimension z)) ℚ := by
  refine Fin.cases ?_ ?_ z
  · exact k300J
  · intro z
    refine Fin.cases ?_ ?_ z
    · exact k301J
    · intro z
      refine Fin.cases ?_ ?_ z
      · exact k302J
      · intro z
        refine Fin.cases ?_ ?_ z
        · exact k303J
        · intro z
          refine Fin.cases ?_ ?_ z
          · exact k304J
          · intro z
            refine Fin.cases ?_ ?_ z
            · exact k305J
            · intro z
              refine Fin.cases ?_ ?_ z
              · exact k306J
              · intro z
                refine Fin.cases ?_ ?_ z
                · exact k307J
                · intro z
                  refine Fin.cases ?_ ?_ z
                  · exact k308J
                  · intro z
                    exact Fin.elim0 z

abbrev NatCOMRelativeLabel := Σ z : Fin 9, Fin (natCOMRelativeDimension z)

def natCOMDescendantGramEntry (m : ℕ) (x y : NatCOMRelativeLabel) : ℚ :=
  if h : x.1 = y.1 then
    ((3 : ℚ) ^ (m - x.1.val) * (m - x.1.val).factorial) *
      natCOMRelativeGram x.1 x.2
        (Eq.mp (congrArg (fun z => Fin (natCOMRelativeDimension z)) h.symm) y.2)
  else 0

def natCOMDescendantDualEntry (m : ℕ) (x y : NatCOMRelativeLabel) : ℚ :=
  if h : x.1 = y.1 then
    ((3 : ℚ) ^ (m - x.1.val) * (m - x.1.val).factorial)⁻¹ *
      natCOMRelativeGramInverse x.1 x.2
        (Eq.mp (congrArg (fun z => Fin (natCOMRelativeDimension z)) h.symm) y.2)
  else 0

theorem natCOMDescendantGramEntry_same (m : ℕ) (z : Fin 9)
    (a b : Fin (natCOMRelativeDimension z)) :
    natCOMDescendantGramEntry m ⟨z,a⟩ ⟨z,b⟩ =
      ((3 : ℚ) ^ (m-z.val) * (m-z.val).factorial) * natCOMRelativeGram z a b := by
  simp [natCOMDescendantGramEntry]

theorem natCOMDescendantDualEntry_same (m : ℕ) (z : Fin 9)
    (a b : Fin (natCOMRelativeDimension z)) :
    natCOMDescendantDualEntry m ⟨z,a⟩ ⟨z,b⟩ =
      ((3 : ℚ) ^ (m-z.val) * (m-z.val).factorial)⁻¹ * natCOMRelativeGramInverse z a b := by
  simp [natCOMDescendantDualEntry]

theorem natCOMDescendantGramEntry_ne (m : ℕ) (x y : NatCOMRelativeLabel)
    (h : x.1 ≠ y.1) : natCOMDescendantGramEntry m x y = 0 := by
  simp [natCOMDescendantGramEntry,h]

theorem natCOMDescendantDualEntry_ne (m : ℕ) (x y : NatCOMRelativeLabel)
    (h : x.1 ≠ y.1) : natCOMDescendantDualEntry m x y = 0 := by
  simp [natCOMDescendantDualEntry,h]

#print axioms natCOMDescendantGramEntry_same
#print axioms natCOMDescendantDualEntry_same
#print axioms natCOMDescendantGramEntry_ne
#print axioms natCOMDescendantDualEntry_ne
end TorusLean.BosonFiniteCertificate
