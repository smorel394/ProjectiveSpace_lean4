import ProjectiveSpace.ClosedHyperplanes
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual


open Classical
noncomputable section 

universe u 

/-! # The topology on projective space -/

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E]


/-- Equip projective space `ℙ 𝕜 E` with the "coinduced" topology from the natural map
`mk' : E ∖ {0} → ℙ 𝕜 E`. -/
instance : TopologicalSpace (ℙ 𝕜 E) :=
TopologicalSpace.coinduced (Projectivization.mk' 𝕜) instTopologicalSpaceSubtype 

section Chart1

def Goodset (φ : E →L[𝕜] 𝕜) : Set (ℙ 𝕜 E) := {x | φ x.rep ≠ 0}


lemma GoodsetPreimage (φ : E →L[𝕜] 𝕜) {u : E} (hu : u ≠ 0) :
(φ u ≠ 0) ↔ Projectivization.mk 𝕜 u hu ∈ Goodset φ := by 
  set x := Projectivization.mk 𝕜 u hu 
  have hux : Projectivization.mk 𝕜 u hu = Projectivization.mk 𝕜 x.rep (Projectivization.rep_nonzero x) := 
    by simp only [Projectivization.mk_rep]
  match (Projectivization.mk_eq_mk_iff 𝕜 u x.rep hu (Projectivization.rep_nonzero x)).mp hux with 
  | ⟨a, ha⟩ =>  
    change (a.1)•x.rep = u at ha 
    constructor 
    . intro h 
      change φ x.rep ≠ 0 
      by_contra habs
      rw [←ha, map_smul, smul_eq_mul, habs, mul_zero] at h 
      exact h (Eq.refl 0)
    . intro h 
      rw [←ha, map_smul, smul_eq_mul]
      by_contra habs 
      apply_fun (fun x => (a.1)⁻¹*x) at habs 
      simp only [Units.isUnit, IsUnit.inv_mul_cancel_left, mul_zero] at habs 
      exact h habs 

-- Is this useful ?
lemma GoodsetPreimage' (φ : E →L[𝕜] 𝕜) (u : {w : E | w ≠ 0}) : 
(u ∈ {w : {w : E | w ≠ 0} | φ w ≠ 0}) ↔ ((Projectivization.mk' 𝕜 u) ∈ (Goodset φ)) := by 
  change (φ u ≠ 0) ↔ (Projectivization.mk' 𝕜 u ∈ Goodset φ)
  rw [Projectivization.mk'_eq_mk]
  exact GoodsetPreimage φ u.2


lemma EstarIsOpen:  IsOpen {u : E | u ≠ 0} :=
isOpen_compl_iff.mpr (isClosed_singleton)


lemma NonzeroPhiIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen {u : {w : E | w ≠ 0} | φ u ≠ 0} := by
  have heq : {u : {w : E | w ≠ 0} | φ u ≠ 0} = ({w : E | w ≠ 0}.restrict φ.toLinearMap)⁻¹'
    {a : 𝕜 | a ≠ 0} := by
      simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, ContinuousLinearMap.coe_coe, Set.preimage_setOf_eq,
        Set.restrict_apply] 
  have hcont : Continuous ({w : E | w ≠ 0}.restrict φ.toLinearMap) := Continuous.comp φ.cont continuous_subtype_val 
  rw [heq]
  refine continuous_def.mp hcont _ ?_
  exact EstarIsOpen 


lemma GoodsetIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen (Goodset φ) := by 
  apply isOpen_coinduced.mpr 
  have heq : (Projectivization.mk' 𝕜)⁻¹' (Goodset φ) = {u | φ u.1 ≠ 0} := by
    ext u 
    simp only [ne_eq, Set.mem_preimage, Projectivization.mk'_eq_mk, Set.mem_setOf_eq]
    exact (Iff.symm (GoodsetPreimage φ u.2))
  rw [heq]
  exact NonzeroPhiIsOpen φ


lemma NonzeroOfNonzeroPhi {φ : E →ₗ[𝕜] 𝕜} {u : E} (hu :φ u ≠ 0) : u ≠ 0 := by 
  by_contra habs 
  rw [habs] at hu 
  simp only [map_zero, ne_eq, not_true] at hu   

lemma NonzeroPhiOfPhiEqOne {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : φ ≠ 0 := by 
  by_contra habs 
  rw [habs] at hv 
  simp only [ContinuousLinearMap.zero_apply, zero_ne_one] at hv  


/- First direction: from projective space to a hyperplane in E.-/

/- Version of chart1 with codomain E. -/
def Chart1_aux (φ : E →L[𝕜] 𝕜) (v : E) (x : ℙ 𝕜 E)  : E :=
(φ v / φ x.rep) • x.rep - v


/-- φ  applied to the result of chart1_aux is zero --/
lemma PhiOfChart1_aux (φ : E →L[𝕜] 𝕜) (v : E) {x : ℙ 𝕜 E} (h : x ∈ Goodset φ) :
φ (Chart1_aux φ v x) = 0 := by 
  unfold Chart1_aux 
  simp only [map_sub, map_smul, smul_eq_mul, ne_eq]
  rw [div_eq_mul_inv, mul_assoc, (mul_comm _ (φ x.rep)), DivisionRing.mul_inv_cancel, mul_one, sub_self]
  exact h 


/- Chart with image in the hyperplane. Here we assume that φ(v)=1, so we can use
the corresponding retraction on Ker(φ). If x is in Goodset φ, the retraction does
nothing as the image of x is already in Ker(φ); but this way we get a map defined on
all of ℙ(E). -/

def Chart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : (ℙ 𝕜 E)→ LinearMap.ker φ :=
(ContinuousRetractionOnHyperplane hv) ∘ (Chart1_aux φ v)


/- Continuity of chart1 and chart1_aux. First we lift chart1_aux to a map 
from E to E.-/

def Chart1_aux_lift (φ : E →L[𝕜] 𝕜) (v : E) (x : E) : E  :=
(φ v / φ x) • x - v


lemma Chart1_aux_lift_IsLift (φ : E →L[𝕜] 𝕜) {u : E} (v : E) (hu : φ u ≠ 0):
Chart1_aux_lift φ v u = Chart1_aux φ  v 
(Projectivization.mk 𝕜 u (NonzeroOfNonzeroPhi hu)) := by 
  unfold Chart1_aux Chart1_aux_lift
  simp only [sub_left_inj]
  match Projectivization.exists_smul_eq_mk_rep 𝕜 u (NonzeroOfNonzeroPhi hu) with 
  | ⟨a, ha⟩ => 
    change (a.1)•u = (Projectivization.mk 𝕜 u (NonzeroOfNonzeroPhi hu)).rep at ha 
    rw [←ha, map_smul, smul_eq_mul, smul_smul, mul_comm, mul_div, mul_div_mul_left]
    exact Units.ne_zero a 


/- We prove that this lift is smooth. For this we need 𝕜 to be complete (to prove smoothness 
of quotients of smooth functions). -/

variable [CompleteSpace 𝕜]

def Chart1_lift_aux (φ : E →L[𝕜] 𝕜) (v : E)  : E → 𝕜:=
fun (u : E) => (φ v) / (φ u)

lemma Chart1_lift_aux_IsSmoothAt (φ : E →L[𝕜] 𝕜) (v : E) {x : E} (hx : φ x≠0) : 
ContDiffAt 𝕜 ⊤ (Chart1_lift_aux φ v) x := by 
  apply ContDiffAt.div 
  . exact contDiffAt_const
  . apply contDiff_iff_contDiffAt.mp 
    apply ContinuousLinearMap.contDiff 
  . exact hx 

lemma Chart1_aux_lift_IsSmoothAt (φ : E→L[𝕜]𝕜)  (v : E) {x : E} (hx :φ  x ≠ 0) : 
ContDiffAt 𝕜 ⊤ (fun y => Chart1_aux_lift φ v y) x := by 
  unfold Chart1_aux_lift 
  apply ContDiffAt.sub 
  . apply ContDiffAt.smul 
    . apply Chart1_lift_aux_IsSmoothAt
      exact hx
    . apply contDiffAt_id
  . apply contDiffAt_const


/- We deduce that the lift is continuous. -/


lemma Chart1_aux_lift_IsContinuousAt (φ : E→L[𝕜]𝕜) {u : E} (v : E) (hu : φ u ≠ 0) :   
ContinuousAt (Chart1_aux_lift φ v) u := 
@ContDiffAt.continuousAt 𝕜 _ E _ _ E _ _ _ u ⊤ (Chart1_aux_lift_IsSmoothAt φ v hu)

-- Is this useful ?
lemma Chart1_aux_lift_IsContinuousAt' (φ : E →L[𝕜] 𝕜) {u : E} (v : E) (hu :φ u ≠ 0) :   
ContinuousAt (fun (u : {w : E| w ≠ 0}) => Chart1_aux_lift φ v u.1) ⟨u, NonzeroOfNonzeroPhi hu⟩ := by
  apply @ContinuousAt.comp {w : E | w ≠ 0} E E _ _ _ (Chart1_aux_lift φ v) (fun u => u.1) 
    ⟨u, NonzeroOfNonzeroPhi hu⟩ 
  . exact Chart1_aux_lift_IsContinuousAt φ v hu 
  . apply continuousAt_subtype_val 

lemma Chart1_aux_lift_IsContinuous (φ : E→L[𝕜] 𝕜)  (v : E) :   
ContinuousOn (Chart1_aux_lift φ v) {u : E | φ u ≠ 0} := by 
  apply ContinuousAt.continuousOn 
  exact fun _ hu => Chart1_aux_lift_IsContinuousAt φ v hu  


-- Is this useful >
lemma Chart1_aux_lift_IsContinuous' (φ : E→L[𝕜] 𝕜)  (v : E):   
ContinuousOn (fun (u : {w : E| w ≠ 0}) => Chart1_aux_lift φ v u) {u : {w : E | w ≠ 0} | φ u ≠ 0} := by 
  apply ContinuousAt.continuousOn 
  intro u hu 
  exact Chart1_aux_lift_IsContinuousAt' φ v hu 


/- Now we deduce that chart1_aux itself is continuous. -/

lemma Chart1_aux_IsContinuous (φ : E →L[𝕜] 𝕜) (v : E) : 
ContinuousOn (fun (x : ℙ 𝕜 E) => Chart1_aux φ v x) (Goodset φ) := by 
  apply (continuousOn_open_iff (GoodsetIsOpen φ)).mpr 
  intro U hU 
  apply isOpen_coinduced.mpr 
  have heq : ((Projectivization.mk' 𝕜) ⁻¹'
   (Goodset φ ∩ (fun (x : ℙ 𝕜 E) => Chart1_aux φ v x) ⁻¹' U)) = (fun u => u.1)⁻¹'
   ({u | (φ u ≠ 0)} ∩ ((fun u => Chart1_aux_lift φ v u)⁻¹' U)) := by 
     simp only [Set.preimage_inter, Set.preimage_setOf_eq]
     ext u 
     simp only [Set.mem_inter_iff, Set.mem_preimage, Projectivization.mk'_eq_mk, Set.mem_setOf_eq]
     rw [←GoodsetPreimage]
     simp only [and_congr_right_iff]
     intro hu
     rw [Chart1_aux_lift_IsLift]
     exact hu 
  rw [heq]
  simp only [Set.preimage_inter, Set.preimage_setOf_eq]
  exact ((continuousOn_open_iff (NonzeroPhiIsOpen φ)).mp (Chart1_aux_lift_IsContinuous' φ v)) U hU 



/- And we finally get the continuity of chart1 itself. -/

lemma Chart1_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : 
ContinuousOn (Chart1 hv) (Goodset φ) :=
Continuous.comp_continuousOn (ContinuousRetractionOnHyperplane hv).cont
(Chart1_aux_IsContinuous φ v)

end Chart1 


/- Now we construct the charts in the other direction. -/

section Chart2 

/- We start with a version defined on all of E. -/

def Chart2_aux (u v : E) (h : v + u ≠ 0) : ℙ 𝕜 E :=
Projectivization.mk 𝕜 (v + u) h


lemma Chart2_aux_hypothesis {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
φ (v + u) ≠ 0 := by 
  rw [map_add, u.2, hv, add_zero]
  exact one_ne_zero 

/- The actual chart2 is defined on Ker(φ) and uses a vector v such that φ(v)=1.  -/

def Chart2 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : ℙ 𝕜 E :=
Chart2_aux u.1 v (NonzeroOfNonzeroPhi (Chart2_aux_hypothesis hv u))

lemma Chart2_aux_CodomainGoodset {φ : E →L[𝕜] 𝕜} (u v : E) (h : φ (v + u) ≠ 0) :
(Chart2_aux u v (NonzeroOfNonzeroPhi h)) ∈ (Goodset φ) :=
(GoodsetPreimage φ (NonzeroOfNonzeroPhi h)).mp h


lemma Chart2_CodomainGoodset {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
(Chart2 hv u) ∈ (Goodset φ) := by 
  unfold Chart2 
  exact Chart2_aux_CodomainGoodset u.1 v (Chart2_aux_hypothesis hv u) 


/- Proof of the continuity of chart2. First we lift chart2 et chart2_aux to maps 
with codomain E. -/

def Chart2_aux_lift (v : E) (u : E) : E := v + u 

def Chart2_lift (φ : E →L[𝕜] 𝕜) (v : E) (u : LinearMap.ker φ) := v + u


/- We prove that these lifts are smooth. -/

lemma Chart2_aux_lift_IsSmooth (v : E) : 
ContDiff 𝕜 ⊤ (Chart2_aux_lift v) := by 
  apply ContDiff.add 
  . exact contDiff_const 
  . exact contDiff_id 

lemma Chart2_lift_IsSmooth (φ : E →L[𝕜] 𝕜) (v : E) : 
ContDiff 𝕜 ⊤ (Chart2_lift φ v) := by 
  apply ContDiff.add 
  . exact contDiff_const 
  . set f : LinearMap.ker φ →L[𝕜] E := 
    {toFun := fun u => u.1
     map_smul' := by tauto
     map_add' := by tauto
     cont := by continuity
    }
    exact ContinuousLinearMap.contDiff f 


/- We deduce that the lifts are continuous. -/

lemma Chart2_aux_lift_IsContinuous (v : E) : Continuous (Chart2_aux_lift v) :=
ContDiff.continuous (@Chart2_aux_lift_IsSmooth 𝕜 E _ _ _ v) 

lemma Chart2_lift_IsContinuous (φ : E →L[𝕜] 𝕜) (v : E) : 
Continuous (Chart2_lift φ v) :=
ContDiff.continuous (@Chart2_lift_IsSmooth 𝕜 E _ _ _ φ v)


/- Variant of chart2_lift with codomain {w:E|w≠0}. -/

-- Is this necessary ?
def Chart2_lift' {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :=
Set.codRestrict (Chart2_lift φ v) {w : E | w ≠ 0} 
(fun u => NonzeroOfNonzeroPhi (Chart2_aux_hypothesis hv u))


lemma Chart2_lift'_IsLift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
Chart2 hv = (Projectivization.mk' 𝕜) ∘ (Chart2_lift' hv) := by 
  ext u 
  unfold Chart2 Chart2_aux Chart2_lift' Chart2_lift
  simp only [ne_eq, Function.comp_apply, Projectivization.mk'_eq_mk, Set.val_codRestrict_apply]

lemma Chart2_lift'_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
Continuous (Chart2_lift' hv) :=
Continuous.codRestrict (Chart2_lift_IsContinuous φ v) _

/- We deduce that chart2 is continuous. -/

lemma Chart2_IsContinuous {φ : E →L[𝕜] 𝕜}  {v : E} (hv : φ v = 1) : 
Continuous (Chart2 hv) :=
Continuous.comp continuous_coinduced_rng (Chart2_lift'_IsContinuous hv)

end Chart2


/- We still need to prove that the charts are inverses of each other.-/

section Charts_are_inverses

/- We prove that Chart1_aux sends the goodset of φ to Ker(φ). -/

lemma Chart1CodomainEqDomainChart2 {φ : E →L[𝕜] 𝕜} (v : E) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) : 
φ (Chart1_aux φ v x) = 0 := by 
  unfold Chart1_aux 
  simp only [map_sub, map_smul, smul_eq_mul, ne_eq]
  rw [div_eq_mul_inv, mul_assoc, mul_comm _ (φ x.rep), DivisionRing.mul_inv_cancel, mul_one, sub_self]
  exact hx 

/- We prove that chart2 (chart1 x) is x if x is in the good set of φ. -/

lemma Chart2Chart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) :
Chart2 hv (Chart1 hv x) = x := by 
  unfold Chart1 Chart2 Chart2_aux
  simp only [Function.comp_apply, map_sub, map_smul, AddSubgroupClass.coe_sub, SetLike.val_smul] 
  have heq : ↑(ContinuousRetractionOnHyperplane hv (Chart1_aux φ v x)) = Chart1_aux φ v x := by
    rw [ContinuousRetractionIsRetraction hv ⟨Chart1_aux φ v x, Chart1CodomainEqDomainChart2 v hx⟩]
  simp_rw [heq]
  unfold Chart1_aux 
  simp only [add_sub_cancel'_right]
  have hnz : (φ v) / (φ x.rep) ≠ 0 := by 
    rw [hv, div_eq_mul_inv, one_mul]
    by_contra habs
    apply_fun (fun a => (φ x.rep) * a) at habs
    simp only [ne_eq, mul_zero, mul_eq_zero, inv_eq_zero, or_self] at habs 
    exact hx habs
  have hnz' : ((φ v) / (φ x.rep)) • x.rep ≠ 0 := smul_ne_zero hnz (Projectivization.rep_nonzero x) 
  suffices Projectivization.mk 𝕜 (((φ v) / (φ x.rep)) • x.rep) hnz' = Projectivization.mk 𝕜
    x.rep (Projectivization.rep_nonzero x) by exact Eq.trans this (Projectivization.mk_rep x)
  apply (Projectivization.mk_eq_mk_iff 𝕜 _ _ hnz' (Projectivization.rep_nonzero x)).mpr
  existsi Units.mk0 ((φ v) / (φ x.rep)) hnz 
  simp only [Units.smul_mk0]
  

/- We prove that Chart2 sends Ker(φ) to the Goodset of φ. -/

lemma Chart2CodomainEqDomainChart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : 
(Chart2 hv u) ∈ (Goodset φ) := by 
  unfold Chart2 Chart2_aux 
  apply (GoodsetPreimage φ _).mp 
  exact Chart2_aux_hypothesis hv u


/-Now we prove that Chart1 (Chart2 u) is u. -/

lemma Chart1Chart2 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
Chart1 hv (Chart2 hv u) = u := by 
  have hφ : φ (v + u.1) ≠ 0 := by 
    rw [map_add, hv, u.2, add_zero]
    simp only [ne_eq, one_ne_zero, not_false_eq_true]
  have hvu : v + u.1 ≠ 0 := NonzeroOfNonzeroPhi hφ
  unfold Chart1 Chart2 Chart2_aux 
  simp only [Function.comp_apply, map_sub, map_smul]
  set x := Projectivization.mk 𝕜 (v + u.1) hvu  
  have hx : x ∈ Goodset φ := by 
    rw [←GoodsetPreimage]
    exact hφ
  have heq : ↑(ContinuousRetractionOnHyperplane hv (Chart1_aux φ v x)) = Chart1_aux φ v x := by
    rw [ContinuousRetractionIsRetraction hv ⟨Chart1_aux φ v x, Chart1CodomainEqDomainChart2 v hx⟩]
  rw [←SetCoe.ext_iff, heq]
  unfold Chart1_aux  
  have hsimp : ((φ v) / (φ (Projectivization.rep x))) • (Projectivization.rep x) = v + u := by
    rw [hv]
    match (Projectivization.mk_eq_mk_iff 𝕜 _ _ _ _).mp (Projectivization.mk_rep x) with 
  | ⟨a, ha⟩ => 
    change a.1 • (v + u.1) = _ at ha 
    have hacopy := ha 
    apply_fun φ at hacopy 
    simp only [smul_add, map_add, map_smul, hv, smul_eq_mul, mul_one, LinearMap.map_coe_ker, mul_zero, add_zero] 
      at hacopy
    rw [hacopy] at ha 
    rw [←ha]
    simp only [smul_add, map_add, map_smul, hv, smul_eq_mul, mul_one, LinearMap.map_coe_ker, mul_zero, add_zero,
      one_div, ne_eq] 
    rw [smul_smul, smul_smul, mul_comm, DivisionRing.mul_inv_cancel, one_smul, one_smul]
    rw [GoodsetPreimage, Projectivization.mk_rep, ←GoodsetPreimage]
    exact hφ
  rw [hsimp]
  simp only [add_sub_cancel']

end Charts_are_inverses

/- Charted space structure on ℙ(E). -/

section ChartedSpace

variable [CompleteSpace 𝕜]

/- Definition of the local homeomorphisms between ℙ(E) and the hyperplanes. -/

def Chart1_LocalEquiv {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) : LocalEquiv (ℙ 𝕜 E) (LinearMap.ker φ) := 
{
  toFun := Chart1 hv
  invFun := Chart2 hv 
  source := Goodset φ
  target := ⊤
  map_source' := by tauto 
  map_target' := fun u _ => Chart2_aux_CodomainGoodset u.1 v (Chart2_aux_hypothesis hv u)
  left_inv' := fun _ hx => Chart2Chart1 hv hx 
  right_inv' := fun u _ => Chart1Chart2 hv u  
}


def Chart1_LocalHomeomorph {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) : 
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker φ) := {Chart1_LocalEquiv hv with  
  open_source := GoodsetIsOpen φ 
  open_target := isOpen_univ
  continuous_toFun := Chart1_IsContinuous hv 
  continuous_invFun := Continuous.continuousOn (Chart2_IsContinuous hv)
}

/- We want local homeomorphisms into a fixed model space. So we fix a continuous
linear form on E and use its kernel. -/

def Chart1_LocalHomeomorphFixedCodomain {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) 
{ψ : E →L[𝕜] 𝕜} (hψ : ψ ≠ 0) : LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker ψ) :=
LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hv) 
(ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hψ))

lemma Chart1_LocalHomeomorphFixedCodomain_source {φ : E →L[𝕜] 𝕜} {x : ℙ 𝕜 E} 
(hx: φ x.rep = 1) {ψ : E →L[𝕜] 𝕜} (hψ : ψ ≠ 0) : 
x ∈ (Chart1_LocalHomeomorphFixedCodomain hx hψ).toLocalEquiv.source := by 
  unfold Chart1_LocalHomeomorphFixedCodomain OneIsomorphismBetweenTwoClosedHyperplanes
  simp only [LocalHomeomorph.transHomeomorph_source]
  change φ x.rep ≠ 0
  rw [hx]
  exact one_ne_zero 

lemma Chart2_GoodsetPreimage (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} {w : E} (hw : ψ w = 1) 
(u : LinearMap.ker ψ) : (Chart2 hw u) ∈ (Goodset φ) ↔ (φ (w + u) ≠ 0) := by 
  unfold Chart2 Chart2_aux 
  apply Iff.symm 
  refine GoodsetPreimage φ ?_

/- To get a charted space, we need every point of projective space to be in a chart.
This is true if and only if continuous linear forms separate points on E. -/

-- This is the class SeparatingDual in mathlib, so let's comment it.
/-def ContinuousLinearFormsSeparatePoints (𝕜 E : Type u) [NontriviallyNormedField 𝕜]
[NormedAddCommGroup E] [NormedSpace 𝕜 E] := ∀ (v : E), (v ≠ 0) → (∃ (φ : E →L[𝕜] 𝕜), φ v = 1)-/

def Chart1At (x : ℙ 𝕜 E) {ψ : E →L[𝕜] 𝕜} (hψ : ψ ≠ 0) 
(hsep : SeparatingDual 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker ψ) := 
Chart1_LocalHomeomorphFixedCodomain (Classical.choose_spec 
(hsep.exists_eq_one (Projectivization.rep_nonzero x))) hψ 

def ChartedSpaceProjectiveSpace {ψ : E →L[𝕜] 𝕜} (hψ : ψ ≠ 0)
(hsep : SeparatingDual 𝕜 E) :
  ChartedSpace (LinearMap.ker ψ) (ℙ 𝕜 E) := 
{
  atlas := {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = Chart1_LocalHomeomorphFixedCodomain hv hψ}
  chartAt := fun x => Chart1At x hψ hsep 
  mem_chart_source := fun x => Chart1_LocalHomeomorphFixedCodomain_source 
    (Classical.choose_spec (hsep.exists_eq_one (Projectivization.rep_nonzero x))) hψ
  chart_mem_atlas := fun x => by unfold Chart1At; simp only [Set.mem_setOf_eq]
                                 exists Classical.choose 
                                   (hsep.exists_eq_one (Projectivization.rep_nonzero x))
                                 exists x.rep 
                                 exists Classical.choose_spec 
                                   (hsep.exists_eq_one (Projectivization.rep_nonzero x))
}
 
end ChartedSpace 


/-! Here is how change of charts works: We consider two charts, defined by φ₁, v₁ 
and φ₂, v₂ respectively. The change of chart map goes from Ker φ₁ to Ker φ₂, it is 
defined on the open set {u : Ker φ₁ | φ₂(v₁+u)≠0}, and it sends u to 
(φ₂(v₂)/φ₂(v₁+u))•(v₁+u)-v₂. This seems to be always smooth, even if E is 
infinite-dimensional. We should probably make this a general result. 
-/

 /-! We need 𝕜 to be complete to prove smoothness of quotients of smooth functions. -/

section ChangeOfChart

variable [CompleteSpace 𝕜]


def ChangeOfChart_aux (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} (v : E) {w : E} (hw : ψ w = 1) := 
(Chart1_aux φ v) ∘ (Chart2 hw)

lemma Projectivization_vs_LinearForm {φ : E →ₗ[𝕜] 𝕜} {u v : E} (hu : φ u ≠ 0) (hv : φ v ≠ 0)
(hproj : Projectivization.mk 𝕜 u (NonzeroOfNonzeroPhi hu) = Projectivization.mk 𝕜 v (NonzeroOfNonzeroPhi hv)) :
(1 / (φ u)) • u = (1 / (φ v)) • v := by
  rw [Projectivization.mk_eq_mk_iff] at hproj
  match hproj with 
  | ⟨a, ha⟩ =>
    change (a.1) • v = u at ha
    rw [←ha]
    simp only [map_smul, smul_eq_mul, one_div, mul_inv_rev]
    rw [smul_smul, mul_assoc]
    simp only [ne_eq, Units.ne_zero, not_false_eq_true, inv_mul_cancel, mul_one]

lemma ChangeOfChart_aux_apply (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1)
(hw : ψ w = 1) (u : LinearMap.ker ψ) : 
ChangeOfChart_aux φ v hw u= (1 / (φ (w + u))) • (w + u) - v := by 
  unfold ChangeOfChart_aux Chart1_aux Chart2 Chart2_aux 
  simp only [Function.comp_apply, sub_left_inj, hv]
  have hnz : w + u.1 ≠ 0 := NonzeroOfNonzeroPhi (Chart2_aux_hypothesis hw u)
  match (Projectivization.mk_eq_mk_iff 𝕜 _ _ _ _).mp 
    (Projectivization.mk_rep (Projectivization.mk 𝕜 (w + u.1) hnz)) with 
  | ⟨a, ha⟩ => 
    change (a.1) • (w + u.1) = _ at ha
    by_cases h : φ (w + u.1) = 0 
    . have h' : φ  (Projectivization.rep (Projectivization.mk 𝕜 (w + u.1) hnz)) = 0 := by
        rw [←ha, map_smul, h, smul_zero]
      rw [h, h']
      simp only [div_zero, zero_smul, smul_add, add_zero] 
    . have h' : φ (Projectivization.rep (Projectivization.mk 𝕜 (w + ↑u) hnz)) ≠ 0 := by 
        rw [←ha, map_smul]
        by_contra habs
        apply_fun (fun x => (a.1)⁻¹ • x) at habs
        rw [smul_zero, smul_smul, mul_comm] at habs
        simp only [ne_eq, Units.ne_zero, not_false_eq_true, mul_inv_cancel, smul_eq_mul, one_mul] at habs    
        exact h habs 
      apply Projectivization_vs_LinearForm h' h
      rw [Projectivization.mk_rep]
 

def ChangeOfChart_smul (φ : E →L[𝕜] 𝕜) (v w : E)  : E → 𝕜 :=
fun (u : E) => (φ v) / (φ (w + u))


lemma ChangeOfChart_smul_IsSmoothOn (φ : E →L[𝕜] 𝕜) (v w : E) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart_smul φ v w ) {u : E | φ (w + u) ≠ 0} := by 
  apply ContDiffOn.div 
  . apply ContDiff.contDiffOn 
    apply contDiff_const
  . apply (ContDiffOn.continuousLinearMap_comp φ) 
    apply ContDiff.contDiffOn
    apply ContDiff.add
    . apply contDiff_const
    . apply contDiff_id 
  . exact fun _ hu => hu


def ChangeOfChart_aux' (φ : E →L[𝕜] 𝕜) (v w : E)  : E → E:=
fun (u : E) => (ChangeOfChart_smul φ v w u) • (w + u) - v  

lemma ChangeOfChart_aux'_IsSmoothOn (φ : E →L[𝕜] 𝕜) (v w : E) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart_aux' φ v w ) {u : E | φ (w + u) ≠ 0} := by 
  unfold ChangeOfChart_aux'
  apply ContDiffOn.sub
  . apply ContDiffOn.smul
    . exact ChangeOfChart_smul_IsSmoothOn φ v w
    . apply ContDiffOn.add
      . apply contDiffOn_const
      . apply contDiffOn_id
  . apply contDiffOn_const

def InclusionHyperplaneAsContinuousLinearMap (φ : E →L[𝕜] 𝕜) :
LinearMap.ker φ →L[𝕜] E := Submodule.subtypeL (LinearMap.ker φ)

lemma ChangeOfChart_aux'_vs_aux {φ ψ: E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) : 
ChangeOfChart_aux φ v hw =
(ChangeOfChart_aux' φ v w) ∘ (InclusionHyperplaneAsContinuousLinearMap ψ) := by 
  ext  u
  unfold ChangeOfChart_aux' InclusionHyperplaneAsContinuousLinearMap 
    ChangeOfChart_smul
  rw [ChangeOfChart_aux_apply]
  simp only [map_add, one_div, smul_add, hv, Submodule.coe_subtypeL', Submodule.coeSubtype, Function.comp_apply]
  exact hv

lemma ChangeOfChart_aux_IsSmoothOn {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart_aux φ v hw) {u : LinearMap.ker ψ | φ (w + u) ≠ 0} := by 
  rw [ChangeOfChart_aux'_vs_aux hv]
  have heq : {u : LinearMap.ker ψ | φ (w + u) ≠ 0} = (InclusionHyperplaneAsContinuousLinearMap ψ)⁻¹'
    {u : E | φ (w + u) ≠ 0} := by 
    ext u 
    unfold InclusionHyperplaneAsContinuousLinearMap
    simp only [map_add, ne_eq, Set.mem_setOf_eq, Submodule.coe_subtypeL', Submodule.coeSubtype, Set.preimage_setOf_eq] 
  rw [heq]
  refine ContDiffOn.comp_continuousLinearMap ?_ (InclusionHyperplaneAsContinuousLinearMap ψ)
  apply ChangeOfChart_aux'_IsSmoothOn

def ChangeOfChart {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) := 
(Chart1 hv) ∘ (Chart2 hw)

lemma ChangeOfChart_IsSmoothOn {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart hv hw) {u : LinearMap.ker ψ | φ (w + u) ≠ 0} := 
ContDiffOn.continuousLinearMap_comp (ContinuousRetractionOnHyperplane hv)
(ChangeOfChart_aux_IsSmoothOn hv hw)

lemma ChangeOfChartFixedCodomain_source {φ ψ χ : E →L[𝕜] 𝕜} {v w : E} 
(hv : φ v = 1) (hw : ψ w = 1) (hχ : χ ≠ 0) :
((Chart1_LocalHomeomorphFixedCodomain hw hχ).symm.trans
(Chart1_LocalHomeomorphFixedCodomain hv hχ)).toLocalEquiv.source
= (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).symm⁻¹'
{u : LinearMap.ker ψ | φ (w + u) ≠ 0} := by 
  ext u 
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.coe_coe_symm, Set.mem_inter_iff, Set.mem_preimage, 
    Set.preimage_setOf_eq, Set.mem_setOf_eq]
  unfold Chart1_LocalHomeomorphFixedCodomain Chart1_LocalHomeomorph Chart1_LocalEquiv
  simp only [Set.top_eq_univ, LocalHomeomorph.transHomeomorph_target, ContinuousLinearEquiv.symm_toHomeomorph,
    ContinuousLinearEquiv.coe_toHomeomorph, Set.preimage_univ, Set.mem_univ, LocalHomeomorph.transHomeomorph_symm_apply,
    LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, Function.comp_apply, LocalHomeomorph.transHomeomorph_source,
    true_and]
  rw [Chart2_GoodsetPreimage]


lemma ChangeOfChartFixedCodomain_IsSmoothOn {φ ψ χ : E →L[𝕜] 𝕜} {v w : E} 
(hv : φ v = 1) (hw : ψ w = 1) (hχ : χ ≠ 0) :
ContDiffOn 𝕜 ⊤ ((Chart1_LocalHomeomorphFixedCodomain hv hχ).symm.trans
(Chart1_LocalHomeomorphFixedCodomain hw hχ))
((Chart1_LocalHomeomorphFixedCodomain hv hχ).symm.trans
(Chart1_LocalHomeomorphFixedCodomain hw hχ)).toLocalEquiv.source := by 
  rw [ChangeOfChartFixedCodomain_source]
  unfold Chart1_LocalHomeomorphFixedCodomain
  apply ContDiffOn.continuousLinearMap_comp
    (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).toContinuousLinearMap
  simp only [Equiv.toLocalEquiv_source, LocalEquiv.restr_univ, LocalEquiv.symm_symm, LocalHomeomorph.symm_symm,
    LocalHomeomorph.transHomeomorph_source, LocalHomeomorph.symm_toLocalEquiv, LocalHomeomorph.restrOpen_toLocalEquiv,
    LocalEquiv.restr_coe_symm, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
    ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply,
    LocalHomeomorph.toFun_eq_coe, Set.preimage_setOf_eq]
  set f := (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ).symm.toContinuousLinearMap 
  have heq : {a | ψ (v + (f a).1) ≠ 0} = f⁻¹' {b | ψ (v + b.1) ≠ 0} := by
    ext u 
    simp only [ContinuousLinearEquiv.coe_coe, map_add, ne_eq, Set.mem_setOf_eq, Set.preimage_setOf_eq]
  erw [heq]
  change ContDiffOn 𝕜 ⊤ (fun x => (Chart1_LocalHomeomorph hw) ((Chart1_LocalHomeomorph hv).symm
    (f x))) _ 
  change ContDiffOn 𝕜 ⊤ ((Chart1_LocalHomeomorph hw) ∘ (Chart1_LocalHomeomorph hv).symm ∘ f) _
  rw [←Function.comp.assoc] 
  refine ContDiffOn.comp_continuousLinearMap ?_ f
  apply ChangeOfChart_IsSmoothOn 
  exact hv 


def ModelHyperplane (φ : E →L[𝕜] 𝕜) := modelWithCornersSelf 𝕜 (LinearMap.ker φ) 


def ProjectiveSpace_SmoothManifold {χ : E →L[𝕜] 𝕜} (hχ : χ ≠ 0) 
(hsep : SeparatingDual 𝕜 E) :
@SmoothManifoldWithCorners _ _ _ _ _ _ _ (ModelHyperplane χ) (ℙ 𝕜 E) _
(ChartedSpaceProjectiveSpace hχ hsep) :=
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ (ModelHyperplane χ) (ℙ 𝕜 E) 
_ (ChartedSpaceProjectiveSpace hχ hsep) 
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, v, hv, hev⟩, ⟨ψ, w, hw, he'w⟩ => 
       rw [hev, he'w]
       unfold ModelHyperplane
       simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp.right_id,
         Function.comp.left_id, Set.preimage_id_eq, id_eq, Set.range_id, Set.inter_univ]
       exact ChangeOfChartFixedCodomain_IsSmoothOn hv hw hχ
)

end ChangeOfChart

