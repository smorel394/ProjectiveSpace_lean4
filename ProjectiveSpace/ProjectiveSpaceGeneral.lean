import ProjectiveSpace.ClosedHyperplanes
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Geometry.Manifold.Instances.Sphere



open Classical
noncomputable section 

universe u 

/- Manifold structure on E-{0}.-/

section Estar
variable (E : Type u) [NormedAddCommGroup E] 

def Estar : Set E := {u : E | u ≠ 0}

lemma EstarIsOpen:  IsOpen {u : E | u ≠ 0} :=
isOpen_compl_iff.mpr (isClosed_singleton)

def EstarToE : OpenEmbedding (fun (u : Estar E) => (u : E)) :=
{
  induced := by tauto
  inj := by intro u v; rw [SetCoe.ext_iff]; simp only [imp_self]
  open_range := by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]
                   exact EstarIsOpen E
}

variable [Nonempty (Estar E)]

lemma OpenEmbeddingEstar.inverse {u : E} (hu : u ≠ 0) :
u = (OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE E)).symm u := by 
  have heq : u = (fun u=> u.1) (⟨u, hu⟩ : Estar E) := by simp only 
  nth_rewrite 2 [heq]
  nth_rewrite 2 [←(OpenEmbedding.toLocalHomeomorph_apply _ (EstarToE E))]
  rw [LocalHomeomorph.left_inv]
  tauto 

instance : ChartedSpace E (Estar E) := (EstarToE E).singletonChartedSpace 

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

instance : SmoothManifoldWithCorners (modelWithCornersSelf 𝕜 E) (Estar E) :=
  (EstarToE E).singleton_smoothManifoldWithCorners (modelWithCornersSelf 𝕜 E) 

end Estar


variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E]


section Preliminaries
/-- Equip projective space `ℙ 𝕜 E` with the "coinduced" topology from the natural map
`mk' : E ∖ {0} → ℙ 𝕜 E`. -/
instance : TopologicalSpace (ℙ 𝕜 E) :=
TopologicalSpace.coinduced (Projectivization.mk' 𝕜) instTopologicalSpaceSubtype 


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


lemma NonzeroPhiIsOpen' (φ : E →L[𝕜] 𝕜) : IsOpen {u : {w : E | w ≠ 0} | φ u ≠ 0} := by
  have heq : {u : {w : E | w ≠ 0} | φ u ≠ 0} = ({w : E | w ≠ 0}.restrict φ.toLinearMap)⁻¹'
    {a : 𝕜 | a ≠ 0} := by
      simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, ContinuousLinearMap.coe_coe, Set.preimage_setOf_eq,
        Set.restrict_apply] 
  have hcont : Continuous ({w : E | w ≠ 0}.restrict φ.toLinearMap) := Continuous.comp φ.cont continuous_subtype_val 
  rw [heq]
  refine continuous_def.mp hcont _ ?_
  exact EstarIsOpen 𝕜

lemma NonzeroPhiIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen {u : E | φ u ≠ 0} := by
  rw [←(@Set.preimage_setOf_eq _ _ (fun u => u ≠ 0) φ)]
  apply continuous_def.mp φ.cont 
  exact EstarIsOpen 𝕜
  

lemma GoodsetIsOpen (φ : E →L[𝕜] 𝕜) : IsOpen (Goodset φ) := by 
  apply isOpen_coinduced.mpr 
  have heq : (Projectivization.mk' 𝕜)⁻¹' (Goodset φ) = {u | φ u.1 ≠ 0} := by
    ext u 
    simp only [ne_eq, Set.mem_preimage, Projectivization.mk'_eq_mk, Set.mem_setOf_eq]
    exact (Iff.symm (GoodsetPreimage φ u.2))
  rw [heq]
  exact NonzeroPhiIsOpen' φ


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

end Preliminaries 

section Chart1

/- First direction: from projective space to a hyperplane in E.-/


/- Chart with image in the hyperplane Ker(φ). Here we assume that φ(v)=1, so we can use
the corresponding retraction on Ker(φ). If x is in Goodset φ, the retraction does
nothing as the image of x is already in Ker(φ); but this way we get a map defined on
all of ℙ(E). -/


def Chart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (x : ℙ 𝕜 E) : LinearMap.ker φ :=
(ContinuousRetractionOnHyperplane hv) ((φ v / φ x.rep) • x.rep - v)


/- To prove continuity, we lift the chart to a map defined on E.-/


/- Continuity of Chart1. First we lift Chart1 to a map from E to ker φ.-/

def Chart1Lift_aux (φ : E →L[𝕜] 𝕜) (v : E) (u : E) : E  :=
(φ v / φ u) • u - v

def Chart1Lift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : E → (LinearMap.ker φ) :=
(ContinuousRetractionOnHyperplane hv) ∘ (Chart1Lift_aux φ v)


lemma Chart1Lift_is_lift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu : u ≠ 0) : 
Chart1Lift hv u = Chart1 hv (Projectivization.mk 𝕜 u hu) := by 
  unfold Chart1Lift Chart1 Chart1Lift_aux 
  simp only [hv, Function.comp_apply, map_sub, map_smul, sub_left_inj]
  refine @Projectivization_vs_LinearMap 𝕜 E _ _ _ (LinearMap.ker φ) _ _ φ _ _ hu 
    (Projectivization.rep_nonzero (Projectivization.mk 𝕜 u hu)) (ContinuousRetractionOnHyperplane hv) ?_
  rw [Projectivization.mk_rep]



/- We prove that this lift is smooth. For this we need 𝕜 to be complete (to prove smoothness 
of quotients of smooth functions). -/

variable [CompleteSpace 𝕜]

lemma Chart1Lift_aux_IsSmoothAt (φ : E→L[𝕜]𝕜)  (v : E) {u : E} (hu :φ u ≠ 0) : 
ContDiffAt 𝕜 ⊤ (Chart1Lift_aux φ v) u := by 
  unfold Chart1Lift_aux 
  apply ContDiffAt.sub
  . apply ContDiffAt.smul
    . apply ContDiffAt.div 
      . apply contDiffAt_const 
      . apply contDiff_iff_contDiffAt.mp 
        apply ContinuousLinearMap.contDiff 
      . exact hu 
    . apply contDiffAt_id
  . apply contDiffAt_const

lemma Chart1Lift_IsSmoothAt {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu :φ u ≠ 0) : 
ContDiffAt 𝕜 ⊤ (Chart1Lift hv) u := by 
  unfold Chart1Lift
  apply ContDiffAt.continuousLinearMap_comp 
  exact Chart1Lift_aux_IsSmoothAt φ v hu 

/- We deduce that the lift is continuous. -/

lemma Chart1Lift_IsContinuousAt {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {u : E} (hu :φ u ≠ 0) : 
ContinuousAt (Chart1Lift hv) u := 
@ContDiffAt.continuousAt 𝕜 _ E _ _ (LinearMap.ker φ) _ _ _ u ⊤ (Chart1Lift_IsSmoothAt hv hu)

lemma Chart1Lift_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1)  : 
ContinuousOn (Chart1Lift hv) {u : E | φ u ≠ 0} := 
ContinuousAt.continuousOn (fun _ hu => Chart1Lift_IsContinuousAt hv hu)

-- Is this useful ?
/-
lemma Chart1Lift_aux_IsContinuousAt (φ : E→L[𝕜]𝕜) {u : E} (v : E) (hu : φ u ≠ 0) :   
ContinuousAt (Chart1Lift_aux φ v) u := 
@ContDiffAt.continuousAt 𝕜 _ E _ _ E _ _ _ u ⊤ (Chart1Lift_aux_IsSmoothAt φ v hu)
-/


/- Now we deduce that Chart1 itself is continuous. -/

lemma Chart1_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : 
ContinuousOn (Chart1 hv) (Goodset φ) := by 
  apply (continuousOn_open_iff (GoodsetIsOpen φ)).mpr 
  intro U hU 
  apply isOpen_coinduced.mpr 
  have heq : ((Projectivization.mk' 𝕜) ⁻¹'
   (Goodset φ ∩ (fun (x : ℙ 𝕜 E) => Chart1 hv x) ⁻¹' U)) = (fun u => u.1)⁻¹' 
   ({u : E| (φ u ≠ 0)} ∩ (Chart1Lift hv)⁻¹' U) := by 
    ext u 
    simp only [ne_eq, Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Projectivization.mk'_eq_mk,
      Set.preimage_setOf_eq, Set.mem_setOf_eq]
    rw [←GoodsetPreimage, Chart1Lift_is_lift]
  rw [heq]
  apply IsOpen.preimage 
  . simp_all only [ne_eq, Set.preimage_inter, Set.preimage_setOf_eq]
    apply continuous_induced_dom
  . exact (@continuousOn_open_iff _ _ _ _ (Chart1Lift hv) _ (NonzeroPhiIsOpen φ)).mp (Chart1Lift_IsContinuous hv) U hU  
     
end Chart1 


/- Now we construct the charts in the other direction. -/

section Chart2 

lemma Chart2_nonzero {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
φ (v + u) ≠ 0 := by 
  rw [map_add, u.2, hv, add_zero]
  exact one_ne_zero 

def Chart2 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : ℙ 𝕜 E :=
Projectivization.mk 𝕜 (v + u.1) (NonzeroOfNonzeroPhi (Chart2_nonzero hv u)) 

lemma Chart2_CodomainGoodset {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
(Chart2 hv u) ∈ (Goodset φ) := by 
  unfold Chart2 
  rw [←GoodsetPreimage]
  exact Chart2_nonzero hv u 

lemma Chart2_GoodsetPreimage (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} {w : E} (hw : ψ w = 1) 
(u : LinearMap.ker ψ) : (Chart2 hw u) ∈ (Goodset φ) ↔ (φ (w + u) ≠ 0) := by 
  unfold Chart2 
  apply Iff.symm 
  refine GoodsetPreimage φ ?_


/- Proof of the continuity of Chart2. First we lift Chart2 to maps with codomain E. -/


def Chart2_lift (φ : E →L[𝕜] 𝕜) (v : E) (u : LinearMap.ker φ) := v + u


/- We prove that this lift is smooth. -/

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



/- We deduce that the lift is continuous. -/

lemma Chart2_lift_IsContinuous (φ : E →L[𝕜] 𝕜) (v : E) : 
Continuous (Chart2_lift φ v) :=
ContDiff.continuous (@Chart2_lift_IsSmooth 𝕜 E _ _ _ φ v)

/- To relate this to Chart2, it is convenient to define a variant of the lift with codomain {u : E | u ≠ 0}.-/

def Chart2_lift' {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :=
Set.codRestrict (Chart2_lift φ v) (Estar E)
(fun u => NonzeroOfNonzeroPhi (Chart2_nonzero hv u))

lemma Chart2_lift'_IsLift {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
Chart2 hv = (Projectivization.mk' 𝕜) ∘ (Chart2_lift' hv) := by 
  ext u 
  unfold Chart2 Chart2_lift' Chart2_lift
  simp only [ne_eq, Function.comp_apply, Projectivization.mk'_eq_mk, Set.val_codRestrict_apply]

lemma Chart2_lift'_IsContinuous {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
Continuous (Chart2_lift' hv) :=
Continuous.codRestrict (Chart2_lift_IsContinuous φ v) _

/- We deduce that chart2 is continuous. -/

lemma Chart2_IsContinuous {φ : E →L[𝕜] 𝕜}  {v : E} (hv : φ v = 1) : 
Continuous (Chart2 hv) :=
Continuous.comp continuous_coinduced_rng (Chart2_lift'_IsContinuous hv)

end Chart2
 

/- We need to prove that the charts are inverses of each other.-/

section Charts_are_inverses

/- We prove that Chart1 without the retraction sends the goodset of φ to Ker(φ). -/

lemma Chart1CodomainEqDomainChart2 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) : 
φ (((1 / φ x.rep) • x.rep - v)) = 0 := by 
  simp only [one_div, map_sub, map_smul, smul_eq_mul, ne_eq]
  rw [mul_comm _ (φ x.rep), DivisionRing.mul_inv_cancel, hv, sub_self]
  exact hx 


/- We prove that Chart2 (Chart1 x) is x if x is in the Goodset of φ. -/

lemma Chart2Chart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) {x : ℙ 𝕜 E} (hx : x ∈ Goodset φ) :
Chart2 hv (Chart1 hv x) = x := by 
  unfold Chart1 Chart2 
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul] 
  rw [hv]
  have heq : ↑(ContinuousRetractionOnHyperplane hv ((1 / φ x.rep) • x.rep - v)) = ((1 / φ x.rep) • x.rep - v) := by
    rw [ContinuousRetractionIsRetraction hv ⟨_, Chart1CodomainEqDomainChart2 hv hx⟩]
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
  

/- We prove that Chart2 sends Ker(φ) to the Goodset of φ. -/

lemma Chart2CodomainEqDomainChart1 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) : 
(Chart2 hv u) ∈ (Goodset φ) := by 
  unfold Chart2  
  apply (GoodsetPreimage φ _).mp 
  exact Chart2_nonzero hv u


/-Now we prove that Chart1 (Chart2 u) is u. -/

lemma Chart1Chart2 {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : LinearMap.ker φ) :
Chart1 hv (Chart2 hv u) = u := by 
  have hφ1 : φ (v + u.1) = 1 := by 
    rw [map_add, hv, u.2, add_zero]
  have hφ : φ (v + u.1) ≠ 0 := by 
    rw [hφ1]
    simp only [ne_eq, one_ne_zero, not_false_eq_true]
  have hvu : v + u.1 ≠ 0 := NonzeroOfNonzeroPhi hφ
  unfold Chart1 Chart2 
  simp only [Function.comp_apply]
  set x := Projectivization.mk 𝕜 (v + u.1) hvu  
  have hx : x ∈ Goodset φ := by 
    rw [←GoodsetPreimage]
    exact hφ
  have heq : ↑(ContinuousRetractionOnHyperplane hv ((1 / φ x.rep) • x.rep - v)) = ((1 / φ x.rep) • x.rep - v) := by
    rw [ContinuousRetractionIsRetraction hv ⟨_, Chart1CodomainEqDomainChart2 hv hx⟩]
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
  map_target' := fun u _ => Chart2_CodomainGoodset hv u
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


/- To define the charted space structure, we want local homeomorphisms into a fixed model space. 
So we fix a continuous linear form on E and use its kernel. It is isomorphic to every other closed
hyperplane by OneIsomorphismBetweenClosedHyperplanes.-/

variable {χ : E →L[𝕜] 𝕜} (hχ : χ ≠ 0)

/- To get a charted space, we need every point of projective space to be in a chart.
This is true if and only if continuous linear forms separate points on E, so we supposed that
have a SeparatingDual structure on E. -/

variable (hsep : SeparatingDual 𝕜 E)

/- Chart at x ∈ ℙ(E). First with varying codomain, then with fixed codomain.-/

def ProjectiveSpace.ChartAt_aux (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker (Classical.choose 
(hsep.exists_eq_one (Projectivization.rep_nonzero x)))) := 
Chart1_LocalHomeomorph (Classical.choose_spec 
(hsep.exists_eq_one (Projectivization.rep_nonzero x)))


def ProjectiveSpace.ChartAt (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker χ) := 
LocalHomeomorph.transHomeomorph (ChartAt_aux hsep x)
(ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne (Classical.choose_spec 
(hsep.exists_eq_one (Projectivization.rep_nonzero x)))) hχ))

lemma ProjectiveSpace.ChartAt_source (x : ℙ 𝕜 E) :
(ProjectiveSpace.ChartAt hχ hsep x).source = 
Goodset (Classical.choose (hsep.exists_eq_one (Projectivization.rep_nonzero x))) := by
  unfold ProjectiveSpace.ChartAt ProjectiveSpace.ChartAt_aux Chart1_LocalHomeomorph Chart1_LocalEquiv
  simp only [Set.top_eq_univ, LocalHomeomorph.transHomeomorph_source]


lemma Chart1_LocalHomeomorphFixedCodomain_source {φ : E →L[𝕜] 𝕜} {x : ℙ 𝕜 E} 
(hx: φ x.rep = 1) : 
x ∈ (LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hx) 
(ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hx) hχ))).toLocalEquiv.source := by 
  simp only [LocalHomeomorph.transHomeomorph_source]
  change φ x.rep ≠ 0
  rw [hx]
  exact one_ne_zero 


def ChartedSpaceProjectiveSpace : ChartedSpace (LinearMap.ker χ) (ℙ 𝕜 E) := 
{
  atlas := {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = LocalHomeomorph.transHomeomorph 
    (Chart1_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
    (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))}
  chartAt := fun x => ProjectiveSpace.ChartAt hχ hsep x  
  mem_chart_source := fun x => Chart1_LocalHomeomorphFixedCodomain_source hχ
    (Classical.choose_spec (hsep.exists_eq_one (Projectivization.rep_nonzero x))) 
  chart_mem_atlas := fun x => by unfold ProjectiveSpace.ChartAt; simp only [Set.mem_setOf_eq]
                                 exists Classical.choose 
                                   (hsep.exists_eq_one (Projectivization.rep_nonzero x))
                                 exists x.rep 
                                 exists Classical.choose_spec 
                                   (hsep.exists_eq_one (Projectivization.rep_nonzero x))
}
 
end ChartedSpace 


/-! Here is how change of charts works if we use charts with varying codomaons: 
We consider two charts, defined by φ₁, v₁ and φ₂, v₂ respectively. The change of 
chart map goes from Ker φ₁ to Ker φ₂, it is defined on the open set 
{u : Ker φ₁ | φ₂(v₁+u)≠0}, and it sends u to (φ₂(v₂)/φ₂(v₁+u))•(v₁+u)-v₂. This is 
always smooth, even if E is infinite-dimensional. 
For charts with fixed codomain, it's the same but we throw in some continuous linear
equivalences at the beginning and at the end, and these are smooth.
-/

 /- Note that we need 𝕜 to be complete to prove smoothness of quotients of smooth functions. -/

section ChangeOfChart

variable [CompleteSpace 𝕜]

/- The version with varying codomains.-/

def ChangeOfChart' {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
LinearMap.ker ψ → LinearMap.ker φ := (Chart1 hv) ∘ (Chart2 hw)

lemma ChangeOfChart'_formula {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1)
(u : LinearMap.ker ψ) :
ChangeOfChart' hv hw u = ContinuousRetractionOnHyperplane hv ((1 / (φ (w + u))) • (w + u) - v) := by 
  --have hker : (1 / (φ (w + u))) • (w + u) - v ∈ LinearMap.ker φ := sorry 
  unfold ChangeOfChart' Chart1 Chart2
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
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ) ∘ (Chart1 hv) ∘ (Chart2 hw) ∘
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
(↑(LocalHomeomorph.trans (LocalHomeomorph.symm (LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hv)
(ContinuousLinearEquiv.toHomeomorph (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))))
(LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hw) (ContinuousLinearEquiv.toHomeomorph 
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ))))) =
ChangeOfChart hχ hw hv := by 
  unfold Chart1_LocalHomeomorph Chart1_LocalEquiv ChangeOfChart
  ext u 
  simp only [Set.top_eq_univ, LocalHomeomorph.coe_trans, LocalHomeomorph.transHomeomorph_apply,
           ContinuousLinearEquiv.coe_toHomeomorph, LocalHomeomorph.mk_coe, LocalHomeomorph.transHomeomorph_symm_apply,
           LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, ContinuousLinearEquiv.symm_toHomeomorph,
           Function.comp_apply]     

lemma ChangeOfChart_domain {φ ψ : E →L[𝕜] 𝕜} {v w : E} (hv : φ v = 1) (hw : ψ w = 1) :
(LocalHomeomorph.trans (LocalHomeomorph.symm (LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hv)
(ContinuousLinearEquiv.toHomeomorph (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))))
(LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hw) (ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hw) hχ)))).toLocalEquiv.source =
((OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ)''
{u : LinearMap.ker φ | ψ (v + u) ≠ 0}) := by
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.transHomeomorph_target, ContinuousLinearEquiv.symm_toHomeomorph,
    ContinuousLinearEquiv.coe_toHomeomorph, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
    LocalHomeomorph.transHomeomorph_source, map_add]
  unfold Chart1_LocalHomeomorph Chart1_LocalEquiv
  simp only [Set.top_eq_univ, Set.preimage_univ, LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, Set.univ_inter]
  ext u 
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_setOf_eq, Subtype.exists, LinearMap.mem_ker,
    exists_and_left]
  unfold Chart2
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

/- We can finally define the manifold structure on ℙ(E). We need continuous linear forms to separate points.-/

variable (hsep : SeparatingDual 𝕜 E)

def ModelHyperplane := modelWithCornersSelf 𝕜 (LinearMap.ker χ) 

def ProjectiveSpace_SmoothManifold :
@SmoothManifoldWithCorners _ _ _ _ _ _ _ (ModelHyperplane) (ℙ 𝕜 E) _
(ChartedSpaceProjectiveSpace hχ hsep) :=
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ (ModelHyperplane) (ℙ 𝕜 E) 
_ (ChartedSpaceProjectiveSpace hχ hsep) 
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, v, hv, hev⟩, ⟨ψ, w, hw, he'w⟩ => 
       rw [hev, he'w]
       unfold ModelHyperplane
       simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp.right_id,
         Function.comp.left_id, Set.preimage_id_eq, id_eq, Set.range_id, Set.inter_univ] 
       rw [ChangeOfChartIsChangeOfChart]
       rw [ChangeOfChart_domain]
       exact ChangeOfChart_IsSmoothOn hχ hw hv 
)

end ChangeOfChart
