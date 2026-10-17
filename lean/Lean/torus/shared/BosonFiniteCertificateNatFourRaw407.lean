import torus.shared.BosonFiniteCertificateNatFourPrefixCollapsedCache
import torus.shared.BosonFiniteCertificateNatFourRowCache407
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourColumnCache407
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificateNatFourActivePairs407

/-! Degree-7 raw M4 form, prior to any COM partial trace.
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

def f407rawM4Form : Matrix (Fin 11) (Fin 11) ℚ :=
  !![(-493911917457645879093951/156250000000000000000), (-443457902492162161547859/1562500000000000000000), (-72356099815449645974649/3125000000000000000000), (399333047809548551577039/15625000000000000000000), (-1520549830634094415269/31250000000000000000), (158005674926738583866793/31250000000000000000000), (4734099154934190230301/3125000000000000000000), (78975867495993894531/39062500000000000000), (13615015226822464774959/6250000000000000000000), 0, 0;
    (-443457902492162161547859/1562500000000000000000), (-139534851540351665909763/1562500000000000000000), (139908739566878495053719/3125000000000000000000), (-69836812194078860432679/5000000000000000000000), (180908738882581592842443/6250000000000000000000), (155409009607470051923637/31250000000000000000000), (-223993769295235728089037/62500000000000000000000), (472701110538471666090099/125000000000000000000000), (-5036097114632579511519/781250000000000000000), (3585697585242529891383/1953125000000000000000), (-2368569804124095553347/3125000000000000000000);
    (-72356099815449645974649/3125000000000000000000), (139908739566878495053719/3125000000000000000000), (-1647695920422935698936053/31250000000000000000000), (710006790345094726307391/31250000000000000000000), (146070311510145944354343/6250000000000000000000), (573409416676480361854761/31250000000000000000000), (74365439777791735818357/7812500000000000000000), (1024551566309582019063/390625000000000000000), (5203791606148749365193/312500000000000000000), (-520768923841567993728089/62500000000000000000000), (262381569447709960124313/31250000000000000000000);
    (399333047809548551577039/15625000000000000000000), (-69836812194078860432679/5000000000000000000000), (710006790345094726307391/31250000000000000000000), (79962442108406043286263/1562500000000000000000), (-30744116066881615420593/6250000000000000000000), (-152072597285597858106669/62500000000000000000000), (615021636785080759290933/62500000000000000000000), (91701798327314019721503/7812500000000000000000), (-2679184530343606983652611/125000000000000000000000), (-13154644552355487781857/12500000000000000000000), (469383090525092062640349/125000000000000000000000);
    (-1520549830634094415269/31250000000000000000), (180908738882581592842443/6250000000000000000000), (146070311510145944354343/6250000000000000000000), (-30744116066881615420593/6250000000000000000000), (1515015570185356951227/156250000000000000000), (288438784453950596923983/31250000000000000000000), (-76637505263591249903169/15625000000000000000000), (-161993387820908879390571/62500000000000000000000), (4192236576139887413937/1562500000000000000000), (-147469445025183683748711/31250000000000000000000), (-77433238671989545611/12500000000000000000);
    (158005674926738583866793/31250000000000000000000), (155409009607470051923637/31250000000000000000000), (573409416676480361854761/31250000000000000000000), (-152072597285597858106669/62500000000000000000000), (288438784453950596923983/31250000000000000000000), (94744918117296488135769/15625000000000000000000), (937555606800926459145291/62500000000000000000000), (399397776604296369742639/62500000000000000000000), (27182826029514012929019/7812500000000000000000), (524106460844275439355647/125000000000000000000000), (69592925374418957280309/62500000000000000000000);
    (4734099154934190230301/3125000000000000000000), (-223993769295235728089037/62500000000000000000000), (74365439777791735818357/7812500000000000000000), (615021636785080759290933/62500000000000000000000), (-76637505263591249903169/15625000000000000000000), (937555606800926459145291/62500000000000000000000), (286191957355820479360653/15625000000000000000000), (114300667244892080716893/7812500000000000000000), (-13749650455496090991651/15625000000000000000000), (245956213195432604954721/31250000000000000000000), (165164011495390910696337/12500000000000000000000);
    (78975867495993894531/39062500000000000000), (472701110538471666090099/125000000000000000000000), (1024551566309582019063/390625000000000000000), (91701798327314019721503/7812500000000000000000), (-161993387820908879390571/62500000000000000000000), (399397776604296369742639/62500000000000000000000), (114300667244892080716893/7812500000000000000000), (182899723258864994408823/15625000000000000000000), (162722158034092954699653/62500000000000000000000), (524961035169345188310117/62500000000000000000000), (345770866211648302188327/31250000000000000000000);
    (13615015226822464774959/6250000000000000000000), (-5036097114632579511519/781250000000000000000), (5203791606148749365193/312500000000000000000), (-2679184530343606983652611/125000000000000000000000), (4192236576139887413937/1562500000000000000000), (27182826029514012929019/7812500000000000000000), (-13749650455496090991651/15625000000000000000000), (162722158034092954699653/62500000000000000000000), (44771667792434800763049/15625000000000000000000), (99054653968600540641567/25000000000000000000000), (-78214253269991463443583/31250000000000000000000);
    0, (3585697585242529891383/1953125000000000000000), (-520768923841567993728089/62500000000000000000000), (-13154644552355487781857/12500000000000000000000), (-147469445025183683748711/31250000000000000000000), (524106460844275439355647/125000000000000000000000), (245956213195432604954721/31250000000000000000000), (524961035169345188310117/62500000000000000000000), (99054653968600540641567/25000000000000000000000), (4779825798533593098273/625000000000000000000), (292017980653289086193787/31250000000000000000000);
    0, (-2368569804124095553347/3125000000000000000000), (262381569447709960124313/31250000000000000000000), (469383090525092062640349/125000000000000000000000), (-77433238671989545611/12500000000000000000), (69592925374418957280309/62500000000000000000000), (165164011495390910696337/12500000000000000000000), (345770866211648302188327/31250000000000000000000), (-78214253269991463443583/31250000000000000000000), (292017980653289086193787/31250000000000000000000), (1387029645834548934573/97656250000000000000)]

private theorem f407_source_row_0 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 0) (f407basis 0) (f407basis b)=
      f407rawM4Form 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 0) (f407basis 0) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 0 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_0

private theorem f407_source_row_1 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 1) (f407basis 1) (f407basis b)=
      f407rawM4Form 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 1) (f407basis 1) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 1 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_1

private theorem f407_source_row_2 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 2) (f407basis 2) (f407basis b)=
      f407rawM4Form 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 2) (f407basis 2) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 2 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_2

private theorem f407_source_row_3 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 3) (f407basis 3) (f407basis b)=
      f407rawM4Form 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 3) (f407basis 3) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 3 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_3

private theorem f407_source_row_4 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 4) (f407basis 4) (f407basis b)=
      f407rawM4Form 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 4) (f407basis 4) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 4 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_4

private theorem f407_source_row_5 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 5) (f407basis 5) (f407basis b)=
      f407rawM4Form 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 5) (f407basis 5) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 5 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_5

private theorem f407_source_row_6 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 6) (f407basis 6) (f407basis b)=
      f407rawM4Form 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 6) (f407basis 6) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 6 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_6

private theorem f407_source_row_7 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 7) (f407basis 7) (f407basis b)=
      f407rawM4Form 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 7) (f407basis 7) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 7 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_7

private theorem f407_source_row_8 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 8) (f407basis 8) (f407basis b)=
      f407rawM4Form 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 8) (f407basis 8) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 8 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_8

private theorem f407_source_row_9 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 9) (f407basis 9) (f407basis b)=
      f407rawM4Form 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 9) (f407basis 9) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 9 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_9

private theorem f407_source_row_10 : ∀ b : Fin 11,
    natFourPrefixCollapsedForm (f407sourceRowCache 10) (f407basis 10) (f407basis b)=
      f407rawM4Form 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 11) =>
      natFourPrefixCollapsedForm (f407sourceRowCache 10) (f407basis 10) (f407basis b))
    (fun (_ : Fin 1) (b : Fin 11) => f407rawM4Form 10 b) (by decide +kernel)
  exact h 0

#print axioms f407_source_row_10

theorem f407_raw_M4_matrix_check : ∀ a b : Fin 11,
    natFourFactorizedCachedGramForm (f407sourceRowCache a) (f407basis a) (f407basis b)=f407rawM4Form a b := by
  intro a b
  have hshape (i : Fin 11) : (f407basis i).length=4 ∧ (f407basis i).sum=7 := by
    apply natFourBasis_shape 7
    rw [← f407_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hdegree := natFourSourceCache_degree 7 f407activePairs
    f407_active_pairs_source_check f407sourceGramCache f407_source_gram_cache_check
  have hrow : ∀ t : Fin 4, ∀ entry ∈ f407sourceRowCache a t.val,
      natFourCacheDegreeCompatible 7 t.val entry=true := by
    intro t entry he
    rw [f407_source_row_cache_check a t.val] at he
    exact natFourSourceRowCache_degree 7 f407sourceGramCache hdegree (f407basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq 7 (f407sourceRowCache a) hrow _ _
    (hshape a).1 (hshape b).1 (hshape a).2 (hshape b).2]
  fin_cases a
  · exact f407_source_row_0 b
  · exact f407_source_row_1 b
  · exact f407_source_row_2 b
  · exact f407_source_row_3 b
  · exact f407_source_row_4 b
  · exact f407_source_row_5 b
  · exact f407_source_row_6 b
  · exact f407_source_row_7 b
  · exact f407_source_row_8 b
  · exact f407_source_row_9 b
  · exact f407_source_row_10 b


theorem f407_actual_raw_M4_matrix (x y : Fin 11 → ℂ) :
    natOccupationInner (natFourWordBlock f407basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock f407basis y)) =
      star x ⬝ᵥ (complexify f407rawM4Form *ᵥ y) := by
  have hshape (a : Fin 11) :
      (f407basis a).length=4 ∧ (f407basis a).sum=7 := by
    apply natFourBasis_shape 7
    rw [← f407_basis_enumeration]
    exact List.mem_ofFn.mpr ⟨a,rfl⟩
  exact canonicalNatFourOriginalOperator_row_cached_matrix_form 7 f407basis
    (fun a => (hshape a).1) (fun a => (hshape a).2) f407activePairs
    f407_active_pairs_source_check f407sourceGramCache
    f407_source_gram_cache_check f407sourceRowCache
    f407_source_row_cache_check f407rawM4Form f407_raw_M4_matrix_check x y


#print axioms f407_raw_M4_matrix_check
#print axioms f407_actual_raw_M4_matrix
end TorusLean.BosonFiniteCertificate
