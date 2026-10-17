import torus.shared.BosonFiniteCertificateNatFourFactorizedColumn
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourColumnCache406
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificateNatFourActivePairs406

/-! Degree-6 raw M4 form, prior to any COM partial trace.
The target table is independent data. Its equality to the original 138-row
source evaluator is the separately checked theorem below. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f406rawM4Form : Matrix (Fin 9) (Fin 9) ℚ :=
  !![(-1221797020736740933688859/1562500000000000000000), (-7737563585561674807143/78125000000000000000), (6667051199306340801177/1562500000000000000000), (1258798283460159684696207/62500000000000000000000), (-217978778335751996013/48828125000000000000), (18685408642562870253153/5000000000000000000000), (41228303664849552532449/3125000000000000000000), (31131444598380999429957/125000000000000000000000), 0;
    (-7737563585561674807143/78125000000000000000), (-70563890569075080391881/1562500000000000000000), (707043422469682139768151/125000000000000000000000), (17514209173025057320719/62500000000000000000000), (122206142992564600139997/31250000000000000000000), (39509320868066872835443/31250000000000000000000), (241065400341749231909073/125000000000000000000000), (-29477813191054261530687/3906250000000000000000), (-313065887734225367287111/62500000000000000000000);
    (6667051199306340801177/1562500000000000000000), (707043422469682139768151/125000000000000000000000), (-57199470028057428283053/7812500000000000000000), (408508741571322254063511/31250000000000000000000), (152102380531540856237533/31250000000000000000000), (684697926329410253179289/125000000000000000000000), (6442468957341763202007/1250000000000000000000), (-1110157250670909321674643/125000000000000000000000), (1002707484716876679801/15625000000000000000000);
    (1258798283460159684696207/62500000000000000000000), (17514209173025057320719/62500000000000000000000), (408508741571322254063511/31250000000000000000000), (107471067065222830935471/15625000000000000000000), (-62681587941000251400969/15625000000000000000000), (34401124866271192460751/31250000000000000000000), (50134252749772429619541/7812500000000000000000), (72815864751944181662841/62500000000000000000000), (11284232917693315186647/6250000000000000000000);
    (-217978778335751996013/48828125000000000000), (122206142992564600139997/31250000000000000000000), (152102380531540856237533/31250000000000000000000), (-62681587941000251400969/15625000000000000000000), (81538523717157500967/39062500000000000000), (206201535123577844610317/125000000000000000000000), (-34429111155314669796549/31250000000000000000000), (-1367172139527240586713/1953125000000000000000), (-3721679749247917445973/1562500000000000000000);
    (18685408642562870253153/5000000000000000000000), (39509320868066872835443/31250000000000000000000), (684697926329410253179289/125000000000000000000000), (34401124866271192460751/31250000000000000000000), (206201535123577844610317/125000000000000000000000), (355142001562014095188723/62500000000000000000000), (647659692525267155993271/125000000000000000000000), (52472389754274526739883/25000000000000000000000), (259335677717568730970531/62500000000000000000000);
    (41228303664849552532449/3125000000000000000000), (241065400341749231909073/125000000000000000000000), (6442468957341763202007/1250000000000000000000), (50134252749772429619541/7812500000000000000000), (-34429111155314669796549/31250000000000000000000), (647659692525267155993271/125000000000000000000000), (240939645419935662736131/31250000000000000000000), (124107752360358686981529/31250000000000000000000), (26078857554142537764639/3906250000000000000000);
    (31131444598380999429957/125000000000000000000000), (-29477813191054261530687/3906250000000000000000), (-1110157250670909321674643/125000000000000000000000), (72815864751944181662841/62500000000000000000000), (-1367172139527240586713/1953125000000000000000), (52472389754274526739883/25000000000000000000000), (124107752360358686981529/31250000000000000000000), (219692219820293719173699/62500000000000000000000), (115276773185404580121/31250000000000000000);
    0, (-313065887734225367287111/62500000000000000000000), (1002707484716876679801/15625000000000000000000), (11284232917693315186647/6250000000000000000000), (-3721679749247917445973/1562500000000000000000), (259335677717568730970531/62500000000000000000000), (26078857554142537764639/3906250000000000000000), (115276773185404580121/31250000000000000000), (101349115005339943573851/15625000000000000000000)]

/- Each original-source row is checked in a separate kernel invocation to
keep reduction caches bounded; no numerical entry is assumed. -/
private theorem f406_source_row_0 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 0) (f406basis b)=
      f406rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 0) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_0

private theorem f406_source_row_1 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 1) (f406basis b)=
      f406rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 1) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_1

private theorem f406_source_row_2 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 2) (f406basis b)=
      f406rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 2) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_2

private theorem f406_source_row_3 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 3) (f406basis b)=
      f406rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 3) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_3

private theorem f406_source_row_4 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 4) (f406basis b)=
      f406rawM4Form 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 4) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 4 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_4

private theorem f406_source_row_5 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 5) (f406basis b)=
      f406rawM4Form 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 5) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 5 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_5

private theorem f406_source_row_6 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 6) (f406basis b)=
      f406rawM4Form 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 6) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 6 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_6

private theorem f406_source_row_7 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 7) (f406basis b)=
      f406rawM4Form 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 7) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 7 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_7

private theorem f406_source_row_8 : ∀ b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 8) (f406basis b)=
      f406rawM4Form 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 9) =>
      natFourFactorizedCachedGramForm f406sourceGramCache (f406basis 8) (f406basis b))
    (fun (_ : Fin 1) (b : Fin 9) => f406rawM4Form 8 b) (by decide +kernel)
  exact h 0

#print axioms f406_source_row_8

theorem f406_raw_M4_matrix_check : ∀ a b : Fin 9,
    natFourFactorizedCachedGramForm f406sourceGramCache (f406basis a) (f406basis b)=f406rawM4Form a b := by
  intro a
  fin_cases a
  · exact f406_source_row_0
  · exact f406_source_row_1
  · exact f406_source_row_2
  · exact f406_source_row_3
  · exact f406_source_row_4
  · exact f406_source_row_5
  · exact f406_source_row_6
  · exact f406_source_row_7
  · exact f406_source_row_8


theorem f406_actual_raw_M4_matrix (x y : Fin 9 → ℂ) :
    natOccupationInner (natFourWordBlock f406basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f406basis y)) =
      star x ⬝ᵥ (complexify f406rawM4Form *ᵥ y) := by
  have hshape (a : Fin 9) :
      (f406basis a).length=4 ∧ (f406basis a).sum=6 := by
    apply natFourBasis_shape 6
    rw [← f406_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_factorized_matrix_form 6 f406basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f406activePairs
    f406_active_pairs_source_check f406sourceGramCache
    f406_source_gram_cache_check f406rawM4Form f406_raw_M4_matrix_check x y


#print axioms f406_raw_M4_matrix_check
#print axioms f406_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
