import torus.shared.BosonFiniteCertificateNatFourComputable

/-! Source-only predecoded column positions. Literal lists below are checked
against the original columns, then used only as an equivalent evaluator.
The source operator and all original integer rows remain unchanged. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateConjugation

def natFourDecodedColumns : ℕ → List (Option (ℕ × ℕ) × ℕ)
  | 0 => [(none,0), (some (0,0),1), (some (0,1),2), (some (1,0),3), (some (0,2),4), (some (1,1),5), (some (2,0),6), (some (0,3),7), (some (1,2),8), (some (2,1),9), (some (3,0),10), (some (0,4),11), (some (1,3),12), (some (2,2),13), (some (3,1),14), (some (4,0),15), (some (0,5),16), (some (1,4),17), (some (2,3),18), (some (3,2),19), (some (4,1),20), (some (5,0),21), (some (0,6),22), (some (1,5),23), (some (2,4),24), (some (3,3),25), (some (4,2),26), (some (5,1),27), (some (6,0),28), (some (0,7),29), (some (1,6),30), (some (2,5),31), (some (3,4),32), (some (4,3),33), (some (5,2),34), (some (6,1),35), (some (7,0),36), (some (0,8),37), (some (1,7),38), (some (2,6),39), (some (3,5),40), (some (4,4),41), (some (5,3),42), (some (6,2),43), (some (7,1),44), (some (8,0),45)]
  | 1 => [(none,0), (some (0,1),1), (some (1,0),2), (some (0,2),3), (some (1,1),4), (some (2,0),5), (some (0,3),6), (some (1,2),7), (some (2,1),8), (some (3,0),9), (some (0,4),10), (some (1,3),11), (some (2,2),12), (some (3,1),13), (some (4,0),14), (some (0,5),15), (some (1,4),16), (some (2,3),17), (some (3,2),18), (some (4,1),19), (some (5,0),20), (some (0,6),21), (some (1,5),22), (some (2,4),23), (some (3,3),24), (some (4,2),25), (some (5,1),26), (some (6,0),27), (some (0,7),28), (some (1,6),29), (some (2,5),30), (some (3,4),31), (some (4,3),32), (some (5,2),33), (some (6,1),34), (some (7,0),35), (some (0,8),36), (some (1,7),37), (some (2,6),38), (some (3,5),39), (some (4,4),40), (some (5,3),41), (some (6,2),42), (some (7,1),43), (some (8,0),44)]
  | 2 => [(none,0), (some (0,2),1), (some (1,1),2), (some (2,0),3), (some (0,3),4), (some (1,2),5), (some (2,1),6), (some (3,0),7), (some (0,4),8), (some (1,3),9), (some (2,2),10), (some (3,1),11), (some (4,0),12), (some (0,5),13), (some (1,4),14), (some (2,3),15), (some (3,2),16), (some (4,1),17), (some (5,0),18), (some (0,6),19), (some (1,5),20), (some (2,4),21), (some (3,3),22), (some (4,2),23), (some (5,1),24), (some (6,0),25), (some (0,7),26), (some (1,6),27), (some (2,5),28), (some (3,4),29), (some (4,3),30), (some (5,2),31), (some (6,1),32), (some (7,0),33), (some (0,8),34), (some (1,7),35), (some (2,6),36), (some (3,5),37), (some (4,4),38), (some (5,3),39), (some (6,2),40), (some (7,1),41), (some (8,0),42)]
  | 3 => [(none,0), (some (0,3),1), (some (1,2),2), (some (2,1),3), (some (3,0),4), (some (0,4),5), (some (1,3),6), (some (2,2),7), (some (3,1),8), (some (4,0),9), (some (0,5),10), (some (1,4),11), (some (2,3),12), (some (3,2),13), (some (4,1),14), (some (5,0),15), (some (0,6),16), (some (1,5),17), (some (2,4),18), (some (3,3),19), (some (4,2),20), (some (5,1),21), (some (6,0),22), (some (0,7),23), (some (1,6),24), (some (2,5),25), (some (3,4),26), (some (4,3),27), (some (5,2),28), (some (6,1),29), (some (7,0),30), (some (0,8),31), (some (1,7),32), (some (2,6),33), (some (3,5),34), (some (4,4),35), (some (5,3),36), (some (6,2),37), (some (7,1),38), (some (8,0),39)]
  | _ => []

theorem natFourDecodedColumns_eq (t : Fin 4) :
    natFourDecodedColumns t.val =
      (natFourColumnSlots t.val).map (fun i => (natFourSourceColumn t.val i,i)) := by
  fin_cases t <;> decide +kernel

def natFourIndexedChannelForm (t : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourDecodedColumns t).map fun left => ((natFourDecodedColumns t).map fun right =>
    let F := natFourComputableUnitForm t left.1 right.1 s u
    if F=0 then 0 else (natFourOriginalColumnGram t left.2 right.2 : ℚ)*F).sum).sum

theorem natFourIndexedChannelForm_eq (t : Fin 4) (s u : List ℕ) :
    natFourIndexedChannelForm t.val s u = natFourComputableChannelForm t.val s u := by
  simp only [natFourIndexedChannelForm,natFourComputableChannelForm,
    natFourDecodedColumns_eq t,List.map_map,Function.comp_def]

def natFourIndexedGramForm (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => natFourIndexedChannelForm t s u).sum

theorem natFourIndexedGramForm_eq (s u : List ℕ) :
    natFourIndexedGramForm s u=natFourComputableGramForm s u := by
  unfold natFourIndexedGramForm natFourComputableGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact natFourIndexedChannelForm_eq ⟨t,List.mem_range.mp ht⟩ s u

theorem canonicalNatFourOriginalOperator_indexed_form (s u : List ℕ) (hu : u.length=4) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourIndexedGramForm s u : ℂ) := by
  rw [natFourIndexedGramForm_eq,canonicalNatFourOriginalOperator_computable_form s u hu]

#print axioms natFourDecodedColumns_eq
#print axioms natFourIndexedChannelForm_eq
#print axioms natFourIndexedGramForm_eq
#print axioms canonicalNatFourOriginalOperator_indexed_form
end TorusLean.BosonFiniteCertificate
