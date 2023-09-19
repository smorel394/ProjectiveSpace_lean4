import ProjectiveSpace.ClosedHyperplanes
import Mathlib.Geometry.Manifold.Instances.Sphere



open Classical
noncomputable section 

universe u 

/- Manifold structure on E-{0}.-/

variable {k E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜]

lemma EstarIsOpen:  IsOpen {u : E | u ≠ 0} :=
isOpen_compl_iff.mpr (isClosed_singleton)

def EstarToE : OpenEmbedding (fun (u : {u : E | u ≠ 0}) => (u : E)) :=
{
  induced := by tauto
  inj := by intro u v; rw [SetCoe.ext_iff]; simp only [imp_self]
  open_range := by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]
                   exact EstarIsOpen
}

variable [Nonempty {u : E | u ≠ 0}]


lemma OpenEmbeddingEstar.inverse {u : E} (hu : u ≠ 0) :
u = (OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE)).symm u := by 
  have heq : u = (fun u=> u.1) (⟨u, hu⟩ : {u : E | u ≠ 0}) := by simp only 
  nth_rewrite 2 [heq]
  nth_rewrite 2 [←(OpenEmbedding.toLocalHomeomorph_apply _ EstarToE)]
  rw [LocalHomeomorph.left_inv]
  tauto 

@[default_instance 200]
instance instChartedSpaceEstar : ChartedSpace E {u : E | u ≠ 0} := EstarToE.singletonChartedSpace 

lemma Estar.chartAt (u : {u : E | u ≠ 0}) : 
instChartedSpaceEstar.chartAt u = OpenEmbedding.toLocalHomeomorph (fun u => u.1) EstarToE := by tauto

lemma Estar.chartAt.target (u : {u : E | u ≠ 0}) : 
(instChartedSpaceEstar.chartAt u).target = {u : E | u ≠ 0} := by 
  rw [Estar.chartAt, OpenEmbedding.toLocalHomeomorph_target]
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Subtype.range_coe_subtype]
    

lemma Estar.chartAt.inverse (u : {u : E | u ≠ 0}) {v : E} (hv : v ≠ 0) :
v = (instChartedSpaceEstar.chartAt u).symm v := by sorry

instance : SmoothManifoldWithCorners (modelWithCornersSelf 𝕜 E) {u : E | u ≠ 0} :=
  EstarToE.singleton_smoothManifoldWithCorners (modelWithCornersSelf 𝕜 E) 



section Preliminaries

/- Some lemmas about linear forms.-/

lemma NonzeroOfNonzeroPhi {φ : E →ₗ[𝕜] 𝕜} {u : E} (hu :φ u ≠ 0) : u ≠ 0 := by 
  by_contra habs 
  rw [habs] at hu 
  simp only [map_zero, ne_eq, not_true] at hu   

lemma NonzeroPhiOfPhiEqOne {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : φ ≠ 0 := by 
  by_contra habs 
  rw [habs] at hv 
  simp only [ContinuousLinearMap.zero_apply, zero_ne_one] at hv  


lemma Projectivization_vs_LinearMap {F : Type u} [AddCommMonoid F] [Module 𝕜 F] (φ : E →ₗ[𝕜] 𝕜) {u v : E} 
(hu : u ≠ 0) (hv : v ≠ 0) (f : E →ₗ[𝕜] F)
(hproj : Projectivization.mk 𝕜 u hu = Projectivization.mk 𝕜 v hv) :
(1 / (φ u)) • (f u) = (1 / (φ v)) • (f v) := by
  rw [Projectivization.mk_eq_mk_iff] at hproj
  match hproj with 
  | ⟨a, ha⟩ =>
    change (a.1) • v = u at ha
    rw [←ha]
    simp only [map_smul, smul_eq_mul, one_div, mul_inv_rev]
    rw [smul_smul, mul_assoc]
    simp only [ne_eq, Units.ne_zero, not_false_eq_true, inv_mul_cancel, mul_one]

lemma Projectivization_vs_LinearMap_cor (φ : E →ₗ[𝕜] 𝕜) {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
(hproj : Projectivization.mk 𝕜 u hu = Projectivization.mk 𝕜 v hv) :
(1 / (φ u)) • u = (1 / (φ v)) • v := 
Projectivization_vs_LinearMap φ hu hv (LinearMap.id) hproj 

/-- Equip projective space `ℙ 𝕜 E` with the "coinduced" topology from the natural map
`mk' : E ∖ {0} → ℙ 𝕜 E`. -/
instance : TopologicalSpace (ℙ 𝕜 E) :=
TopologicalSpace.coinduced (Projectivization.mk' 𝕜) instTopologicalSpaceSubtype 

/- We introduce the open sets where the charts will be defined.-/

def Goodset (φ : E →L[𝕜] 𝕜) : Set (ℙ 𝕜 E) := {x | φ x.rep ≠ 0}

lemma GoodsetZero {φ : E →L[𝕜] 𝕜} (hφ : φ = 0) : Goodset φ = ∅ := by 
  unfold Goodset 
  rw [hφ]
  simp only [ContinuousLinearMap.zero_apply, ne_eq, not_true, Set.setOf_false]

/- Preimage of the good set in E-{0}.-/

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


lemma NonzeroPhiIsOpen' (φ : E →L[𝕜] 𝕜) : IsOpen {u : {w : E | w ≠ 0} | φ u ≠ 0} := by
  have heq : {u : {w : E | w ≠ 0} | φ u ≠ 0} = ({w : E | w ≠ 0}.restrict φ.toLinearMap)⁻¹'
    {a : 𝕜 | a ≠ 0} := by
      simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, ContinuousLinearMap.coe_coe, Set.preimage_setOf_eq,
        Set.restrict_apply] 
  have hcont : Continuous ({w : E | w ≠ 0}.restrict φ.toLinearMap) := Continuous.comp φ.cont continuous_subtype_val 
  rw [heq]
  refine continuous_def.mp hcont _ ?_
  exact EstarIsOpen 

lemma NonzeroPhiIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen {u : E | φ u ≠ 0} := by
  rw [←(@Set.preimage_setOf_eq _ _ (fun u => u ≠ 0) φ)]
  apply continuous_def.mp φ.cont 
  exact EstarIsOpen 
  

lemma GoodsetIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen (Goodset φ) := by 
  apply isOpen_coinduced.mpr 
  have heq : (Projectivization.mk' 𝕜)⁻¹' (Goodset φ) = {u | φ u.1 ≠ 0} := by
    ext u 
    simp only [ne_eq, Set.mem_preimage, Projectivization.mk'_eq_mk, Set.mem_setOf_eq]
    exact (Iff.symm (GoodsetPreimage φ u.2))
  rw [heq]
  exact NonzeroPhiIsOpen' φ



end Preliminaries 

namespace ProjectiveSpace 

section Chart


/- First direction: from projective space to a hyperplane in E.-/


/- If φ is a continuous linear form on E and v is a vector of E such that φ(v)=1, we define
a chart on Goodset φ with image in the hyperplane Ker(φ). We assume that φ(v)=1 (and not just
φ(v) ≠ 0), because it suffices and simplifies the formulas. For technical reasons, the chart is
defined on all of ℙ(E). If x is in Goodset φ, the last step (the retraction) does
nothing as the image of x by the first map is already in Ker(φ). -/


def Chart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (x : ℙ 𝕜 E) : LinearMap.ker φ :=
(ContinuousRetractionOnHyperplane hv) ((φ v / φ x.rep) • x.rep - v)



/- To prove continuity, we lift the chart to a map defined on E.-/


def ChartLift_aux (φ : E →L[𝕜] 𝕜) (v : E) (u : E) : E  :=
(φ v / φ u) • u - v

def ChartLift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : E → (LinearMap.ker φ) :=
(ContinuousRetractionOnHyperplane hv) ∘ (ChartLift_aux φ v)


lemma ChartLift_is_lift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu : u ≠ 0) : 
ChartLift hv u = Chart hv (Projectivization.mk 𝕜 u hu) := by 
  unfold ChartLift Chart ChartLift_aux 
  simp only [hv, Function.comp_apply, map_sub, map_smul, sub_left_inj]
  apply Projectivization_vs_LinearMap 
  exact Eq.symm (Projectivization.mk_rep (Projectivization.mk 𝕜 u hu))
  

/- We prove that this lift is smooth. For this we need 𝕜 to be complete (to prove smoothness 
of quotients of smooth functions). -/


lemma ChartLift_aux_IsSmoothAt (φ : E→L[𝕜]𝕜)  (v : E) {u : E} (hu :φ u ≠ 0) : 
ContDiffAt 𝕜 ⊤ (ChartLift_aux φ v) u := by 
  unfold ChartLift_aux 
  apply ContDiffAt.sub
  . apply ContDiffAt.smul
    . apply ContDiffAt.div 
      . apply contDiffAt_const 
      . apply contDiff_iff_contDiffAt.mp 
        apply ContinuousLinearMap.contDiff 
      . exact hu 
    . apply contDiffAt_id
  . apply contDiffAt_const

lemma ChartLift_IsSmoothAt {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu :φ u ≠ 0) : 
ContDiffAt 𝕜 ⊤ (ChartLift hv) u := by 
  unfold ChartLift
  apply ContDiffAt.continuousLinearMap_comp 
  exact ChartLift_aux_IsSmoothAt φ v hu 

/- We deduce that the lift is continuous. -/

lemma ChartLift_IsContinuousAt {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu :φ u ≠ 0) : 
ContinuousAt (ChartLift hv) u := 
@ContDiffAt.continuousAt 𝕜 _ E _ _ (LinearMap.ker φ) _ _ _ u ⊤ (ChartLift_IsSmoothAt hv hu)

lemma ChartLift_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1)  : 
ContinuousOn (ChartLift hv) {u : E | φ u ≠ 0} := 
ContinuousAt.continuousOn (fun _ hu => ChartLift_IsContinuousAt hv hu)


/- Now we deduce that the chart itself is continuous. -/

lemma Chart_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : 
ContinuousOn (Chart hv) (Goodset φ) := by 
  apply (continuousOn_open_iff (GoodsetIsOpen φ)).mpr 
  intro U hU 
  apply isOpen_coinduced.mpr 
  have heq : ((Projectivization.mk' 𝕜) ⁻¹'
   (Goodset φ ∩ (fun (x : ℙ 𝕜 E) => Chart hv x) ⁻¹' U)) = (fun u => u.1)⁻¹' 
   ({u : E| (φ u ≠ 0)} ∩ (ChartLift hv)⁻¹' U) := by 
    ext u 
    simp only [ne_eq, Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Projectivization.mk'_eq_mk,
      Set.preimage_setOf_eq, Set.mem_setOf_eq]
    rw [←GoodsetPreimage, ChartLift_is_lift]
  rw [heq]
  apply IsOpen.preimage 
  . simp_all only [ne_eq, Set.preimage_inter, Set.preimage_setOf_eq]
    apply continuous_induced_dom
  . exact (@continuousOn_open_iff _ _ _ _ (ChartLift hv) _ (NonzeroPhiIsOpen φ)).mp (ChartLift_IsContinuous hv) U hU  
     
end Chart 


/- Now we construct the charts in the other direction. -/

section InverseChart

lemma InverseChart_nonzero {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
φ (v + u) ≠ 0 := by 
  rw [map_add, u.2, hv, add_zero]
  exact one_ne_zero 

def InverseChart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : ℙ 𝕜 E :=
Projectivization.mk 𝕜 (v + u.1) (NonzeroOfNonzeroPhi (InverseChart_nonzero hv u)) 

lemma InverseChart_CodomainGoodset {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
(InverseChart hv u) ∈ (Goodset φ) := by 
  unfold InverseChart 
  rw [←GoodsetPreimage]
  exact InverseChart_nonzero hv u 

-- Is this useful ?
lemma InverseChart_GoodsetPreimage (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} {w : E} (hw : ψ w = 1) 
(u : LinearMap.ker ψ) : (InverseChart hw u) ∈ (Goodset φ) ↔ (φ (w + u) ≠ 0) := by 
  unfold InverseChart 
  apply Iff.symm 
  refine GoodsetPreimage φ ?_



/- Proof of the continuity of the inverse chart. First we lift it to a map with codomain E. -/

def InverseChart_lift (φ : E →L[𝕜] 𝕜) (v : E) (u : LinearMap.ker φ) := v + u


/- We prove that this lift is smooth. -/

lemma InverseChart_lift_IsSmooth (φ : E →L[𝕜] 𝕜) (v : E) : 
ContDiff 𝕜 ⊤ (InverseChart_lift φ v) := by 
  apply ContDiff.add 
  . exact contDiff_const 
  . set f : LinearMap.ker φ →L[𝕜] E := 
    {toFun := fun u => u.1
     map_smul' := by tauto
     map_add' := by tauto
     cont := by continuity
    }
    exact ContinuousLinearMap.contDiff f 



/- We deduce that the lift is continuous. -/

lemma InverseChart_lift_IsContinuous (φ : E →L[𝕜] 𝕜) (v : E) : 
Continuous (InverseChart_lift φ v) :=
ContDiff.continuous (InverseChart_lift_IsSmooth φ v)

/- To relate this to the inverse chart, it is convenient to define a variant of the lift with codomain {u : E | u ≠ 0}.-/

def InverseChart_lift' {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :=
Set.codRestrict (InverseChart_lift φ v) {u : E | u ≠ 0}
(fun u => NonzeroOfNonzeroPhi (InverseChart_nonzero hv u))

lemma InverseChart_lift'_IsLift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
InverseChart hv = (Projectivization.mk' 𝕜) ∘ (InverseChart_lift' hv) := by 
  ext u 
  unfold InverseChart InverseChart_lift' InverseChart_lift
  simp only [ne_eq, Function.comp_apply, Projectivization.mk'_eq_mk, Set.val_codRestrict_apply]

lemma InverseChart_lift'_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
Continuous (InverseChart_lift' hv) :=
Continuous.codRestrict (InverseChart_lift_IsContinuous φ v) _

/- We deduce that the inverse chart is continuous. -/

lemma InverseChart_IsContinuous {φ : E →L[𝕜] 𝕜}  {v : E} (hv : φ v = 1) : 
Continuous (InverseChart hv) :=
Continuous.comp continuous_coinduced_rng (InverseChart_lift'_IsContinuous hv)

end InverseChart
 

/- We need to prove that the chart and the inverse chart are indeed inverses of each other.-/

section Charts_are_inverses

/- We prove that the chart without the retraction sends the goodset of φ to Ker(φ). -/

lemma ChartCodomainEqDomainInverseChart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) : 
φ (((1 / φ x.rep) • x.rep - v)) = 0 := by 
  simp only [one_div, map_sub, map_smul, smul_eq_mul, ne_eq]
  rw [mul_comm _ (φ x.rep), DivisionRing.mul_inv_cancel, hv, sub_self]
  exact hx 


/- We prove that InverseChart (Chart x) is x if x is in the Goodset of φ. -/

lemma InverseChartChart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) :
InverseChart hv (Chart hv x) = x := by 
  unfold Chart InverseChart 
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul] 
  rw [hv]
  have heq : ↑(ContinuousRetractionOnHyperplane hv ((1 / φ x.rep) • x.rep - v)) = ((1 / φ x.rep) • x.rep - v) := by
    rw [ContinuousRetractionIsRetraction hv ⟨_, ChartCodomainEqDomainInverseChart hv hx⟩]
  simp_rw [heq]
  simp only [add_sub_cancel'_right]
  have hnz : 1 / (φ x.rep) ≠ 0 := by 
    rw [div_eq_mul_inv, one_mul]
    by_contra habs
    apply_fun (fun a => (φ x.rep) * a) at habs
    simp only [ne_eq, mul_zero, mul_eq_zero, inv_eq_zero, or_self] at habs 
    exact hx habs
  have hnz' : (1 / (φ x.rep)) • x.rep ≠ 0 := smul_ne_zero hnz (Projectivization.rep_nonzero x) 
  suffices Projectivization.mk 𝕜 ((1 / (φ x.rep)) • x.rep) hnz' = Projectivization.mk 𝕜
    x.rep (Projectivization.rep_nonzero x) by exact Eq.trans this (Projectivization.mk_rep x)
  apply (Projectivization.mk_eq_mk_iff 𝕜 _ _ hnz' (Projectivization.rep_nonzero x)).mpr
  existsi Units.mk0 (1 / (φ x.rep)) hnz 
  simp only [Units.smul_mk0]
  

/- We prove that the inverse chart sends Ker(φ) to the Goodset of φ. -/

lemma InverseChartCodomainEqDomainChart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : 
(InverseChart hv u) ∈ (Goodset φ) := by 
  unfold InverseChart  
  apply (GoodsetPreimage φ _).mp 
  exact InverseChart_nonzero hv u


/-Now we prove that Chart (InverseChart u) is u. -/

lemma ChartInverseChart {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
Chart hv (InverseChart hv u) = u := by 
  have hφ1 : φ (v + u.1) = 1 := by 
    rw [map_add, hv, u.2, add_zero]
  have hφ : φ (v + u.1) ≠ 0 := by 
    rw [hφ1]
    simp only [ne_eq, one_ne_zero, not_false_eq_true]
  have hvu : v + u.1 ≠ 0 := NonzeroOfNonzeroPhi hφ
  unfold Chart InverseChart 
  simp only [Function.comp_apply]
  set x := Projectivization.mk 𝕜 (v + u.1) hvu  
  have hx : x ∈ Goodset φ := by 
    rw [←GoodsetPreimage]
    exact hφ
  have heq : ↑(ContinuousRetractionOnHyperplane hv ((1 / φ x.rep) • x.rep - v)) = ((1 / φ x.rep) • x.rep - v) := by
    rw [ContinuousRetractionIsRetraction hv ⟨_, ChartCodomainEqDomainInverseChart hv hx⟩]
  rw [hv, ←SetCoe.ext_iff, heq]
  have hsimp : (1 / (φ (Projectivization.rep x))) • (Projectivization.rep x) = v + u := by
    have ha := @Projectivization_vs_LinearMap_cor 𝕜 E _ _ _ φ _ _ (Projectivization.rep_nonzero x) hvu 
    erw [hφ1] at ha
    simp only [Projectivization.mk_rep, ContinuousLinearMap.coe_coe,  ne_eq, one_ne_zero, not_false_eq_true,
      div_self, smul_add, one_smul, forall_true_left] at ha  
    exact ha
  rw [hsimp]
  simp only [add_sub_cancel']

end Charts_are_inverses


/- Charted space structure on ℙ(E). -/

section ChartAsLocalHomeomorph


/- Definition of the local homeomorphisms between ℙ(E) and the hyperplanes. -/

def Chart_LocalEquiv {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) : LocalEquiv (ℙ 𝕜 E) (LinearMap.ker φ) := 
{
  toFun := Chart hv
  invFun := InverseChart hv 
  source := Goodset φ
  target := ⊤
  map_source' := by tauto 
  map_target' := fun u _ => InverseChart_CodomainGoodset hv u
  left_inv' := fun _ hx => InverseChartChart hv hx 
  right_inv' := fun u _ => ChartInverseChart hv u  
}


def Chart_LocalHomeomorph {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) : 
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker φ) := {Chart_LocalEquiv hv with  
  open_source := GoodsetIsOpen φ 
  open_target := isOpen_univ
  continuous_toFun := Chart_IsContinuous hv 
  continuous_invFun := Continuous.continuousOn (InverseChart_IsContinuous hv)
}

end ChartAsLocalHomeomorph

/- Here is how change of charts works if we use charts with varying codomaons: 
We consider two charts, defined by φ₁, v₁ and φ₂, v₂ respectively. The change of 
chart map goes from Ker φ₁ to Ker φ₂, it is defined on the open set 
{u : Ker φ₁ | φ₂(v₁+u)≠0}, and it sends u to (φ₂(v₂)/φ₂(v₁+u))•(v₁+u)-v₂. This is 
always smooth, even if E is infinite-dimensional. 
For charts with fixed codomain, it's the same but we throw in some continuous linear
equivalences at the beginning and at the end, and these are smooth.
Note that we need 𝕜 to be complete to prove smoothness of quotients of smooth functions. -/

section ChangeOfChart


/- The version with varying codomains.-/

def ChangeOfChart' {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
LinearMap.ker ψ → LinearMap.ker φ := (Chart hv) ∘ (InverseChart hw)

lemma ChangeOfChart'_formula {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1)
(u : LinearMap.ker ψ) :
ChangeOfChart' hv hw u = ContinuousRetractionOnHyperplane hv ((1 / (φ (w + u))) • (w + u) - v) := by 
  unfold ChangeOfChart' Chart InverseChart
  simp only [Function.comp_apply, map_sub, sub_left_inj]
  apply congrArg
  rw [hv] 
  have hwu : w + u.1 ≠ 0 := by 
    have h : ψ (w + u.1) ≠ 0 := by 
      rw [map_add, hw, u.2, add_zero]
      exact one_ne_zero
    exact NonzeroOfNonzeroPhi h   
  exact Projectivization_vs_LinearMap_cor (φ : E →ₗ[𝕜] 𝕜) (Projectivization.rep_nonzero _) hwu  
    (Projectivization.mk_rep _ ) 


lemma ChangeOfChart'_IsSmoothOn {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart' hv hw) {u : LinearMap.ker ψ | φ (w + u) ≠ 0} := by 
  refine ContDiffOn.congr ?_ (fun u _ => ChangeOfChart'_formula hv hw u)
  apply ContDiffOn.continuousLinearMap_comp
  apply ContDiffOn.sub
  . apply ContDiffOn.smul
    . simp_rw [one_div]
      apply ContDiffOn.inv
      . apply ContDiffOn.continuousLinearMap_comp
        apply ContDiffOn.add
        . apply contDiffOn_const
        . apply ContDiff.contDiffOn
          apply ContinuousLinearMap.contDiff (Submodule.subtypeL (LinearMap.ker ψ))   
      . simp only [map_add, ne_eq, Set.mem_setOf_eq, imp_self, Subtype.forall, LinearMap.mem_ker, implies_true,
        forall_const] 
    . apply ContDiffOn.add
      . apply contDiffOn_const
      . apply ContDiff.contDiffOn
        apply ContinuousLinearMap.contDiff (Submodule.subtypeL (LinearMap.ker ψ))   
  . apply contDiffOn_const


/- The version with fixed codomain.-/

variable {χ : E →L[𝕜] 𝕜} (hχ : χ ≠ 0)

def ChangeOfChart {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
LinearMap.ker χ → LinearMap.ker χ := 
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ) ∘ (Chart hv) ∘ (InverseChart hw) ∘
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).symm 


lemma ChangeOfChart_IsSmoothOn {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart hχ hv hw) 
((OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ)''
{u : LinearMap.ker ψ | φ (w + u) ≠ 0}) := by 
  unfold ChangeOfChart
  refine @ContDiffOn.continuousLinearMap_comp 𝕜 _ (LinearMap.ker χ) _ _ (LinearMap.ker φ) _ _ (LinearMap.ker χ) _ _
    _ _ ⊤ (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ) ?_ 
  rw [←Function.comp.assoc]
  change ContDiffOn 𝕜 ⊤ (_ ∘ (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).invFun) _ 
  have heq : ∀ (s : Set (LinearMap.ker ψ)),
    ((OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ))'' s = 
    (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).invFun ⁻¹' s := by 
    intro s
    rw [Set.image_eq_preimage_of_inverse]
    . exact (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).left_inv
    . exact (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).right_inv
  rw [heq _]
  refine @ContDiffOn.comp_continuousLinearMap 𝕜 _ (LinearMap.ker ψ) _ _ (LinearMap.ker φ) _ _ (LinearMap.ker χ) _ _  _ _ ⊤ ?_ 
    ((OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ).symm : _ →L[𝕜] _)
  exact ChangeOfChart'_IsSmoothOn hv hw  


lemma ChangeOfChartIsChangeOfChart {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
(↑(LocalHomeomorph.trans (LocalHomeomorph.symm (LocalHomeomorph.transHomeomorph (Chart_LocalHomeomorph hv)
(ContinuousLinearEquiv.toHomeomorph (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))))
(LocalHomeomorph.transHomeomorph (Chart_LocalHomeomorph hw) (ContinuousLinearEquiv.toHomeomorph 
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ))))) =
ChangeOfChart hχ hw hv := by 
  unfold Chart_LocalHomeomorph Chart_LocalEquiv ChangeOfChart
  ext u 
  simp only [Set.top_eq_univ, LocalHomeomorph.coe_trans, LocalHomeomorph.transHomeomorph_apply,
           ContinuousLinearEquiv.coe_toHomeomorph, LocalHomeomorph.mk_coe, LocalHomeomorph.transHomeomorph_symm_apply,
           LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, ContinuousLinearEquiv.symm_toHomeomorph,
           Function.comp_apply]     


lemma ChangeOfChart_domain {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
(LocalHomeomorph.trans (LocalHomeomorph.symm (LocalHomeomorph.transHomeomorph (Chart_LocalHomeomorph hv)
(ContinuousLinearEquiv.toHomeomorph (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))))
(LocalHomeomorph.transHomeomorph (Chart_LocalHomeomorph hw) (ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ)))).toLocalEquiv.source =
((OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ)''
{u : LinearMap.ker φ | ψ (v + u) ≠ 0}) := by
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.transHomeomorph_target, ContinuousLinearEquiv.symm_toHomeomorph,
    ContinuousLinearEquiv.coe_toHomeomorph, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
    LocalHomeomorph.transHomeomorph_source, map_add]
  unfold Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [Set.top_eq_univ, Set.preimage_univ, LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, Set.univ_inter]
  ext u 
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_setOf_eq, Subtype.exists, LinearMap.mem_ker,
    exists_and_left]
  unfold InverseChart
  rw [←GoodsetPreimage]
  simp only [map_add, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, LinearMap.mem_ker, exists_and_left]
  constructor
  . intro h 
    existsi (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ).symm u 
    simp only [ne_eq, h, not_false_eq_true, Subtype.coe_eta, ContinuousLinearEquiv.apply_symm_apply,
      LinearMap.map_coe_ker, exists_prop, and_self]
  . intro h 
    match h with 
    | ⟨a, ha⟩ => 
      match ha.2 with 
      | ⟨x, hx⟩ => 
        rw [←hx]
        simp only [ContinuousLinearEquiv.symm_apply_apply, ne_eq, ha.1, not_false_eq_true]

  end ChangeOfChart

end ProjectiveSpace