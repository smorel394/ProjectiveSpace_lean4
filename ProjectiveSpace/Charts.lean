import Mathlib.Tactic
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import ProjectiveSpace.Grassmannian 
import Mathlib.Topology.Algebra.Module.FiniteDimension


open Classical
noncomputable section 


section NoTopology 

variable {r : ℕ} {𝕜 E U : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U]

namespace Grassmannian

/- We define what will be charts on Grassmannian 𝕜 E r. The charts are indexed by linear equivalences
φ : E ≃ₗ[𝕜] U × (Fin r → 𝕜), the model of each chart is ((Fin r → 𝕜) →ₗ[𝕜] U). The source of the chart is
the set of r-dimensional subspaces W such that φ.2 induces an isomorphism W ≃ (Fin r → 𝕜), or equivalently
such that W intersects Ker φ.1 trivially; we call this the Goodset of φ.1; its image is all of the codomain.
To have a chart defined at each point, we will need to assume that there exists a linear equivalence between E and 
(Fin r → 𝕜) × U, but we do that later.-/

/- Definition of the sources and lemmas about it.-/

def Goodset (φ : E →ₗ[𝕜] (Fin r → 𝕜)) : Set (Grassmannian 𝕜 E r) :=
{W : Grassmannian 𝕜 E r | W.1 ⊓ (LinearMap.ker φ) = ⊥}

lemma Goodset_iff_equiv (φ : E →ₗ[𝕜] (Fin r → 𝕜)) (W : Grassmannian 𝕜 E r) :
W ∈ Goodset φ ↔ Function.Bijective (LinearMap.domRestrict φ W.1) := by
  unfold Goodset
  simp only [ge_iff_le, Set.mem_setOf_eq]
  constructor 
  . intro hW 
    have hker : LinearMap.ker (LinearMap.domRestrict φ W.1) = ⊥ := by
      ext u 
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
      constructor 
      . intro h 
        change u.1 ∈ LinearMap.ker φ at h 
        have h' := Submodule.mem_inf.mpr ⟨u.2, h⟩
        rw [hW] at h'
        simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at h' 
        exact h'
      . exact fun h => by simp only [h, ZeroMemClass.coe_zero, map_zero]
    rw [LinearMap.ker_eq_bot] at hker
    change _ ∧ _ 
    rw [and_iff_right hker]
    letI := W.2.1
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hker 
    rw [W.2.2]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  . intro hW 
    ext u
    simp only [ge_iff_le, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot]
    constructor 
    . intro ⟨huW, huφ⟩
      have huφ' : LinearMap.domRestrict φ W ⟨u, huW⟩ = 0 := by
        rw [LinearMap.domRestrict_apply]
        exact huφ
      rw [←(LinearMap.map_zero (LinearMap.domRestrict φ W ))] at huφ'
      have h := hW.1 huφ'
      simp only [Submodule.mk_eq_zero] at h   
      exact h
    . exact fun h => by simp only [h, Submodule.zero_mem, map_zero, and_self]

/- Definition of the charts.-/

def Chart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : Grassmannian 𝕜 E r → ((Fin r → 𝕜) →ₗ[𝕜] U) := by 
  intro W 
  set φ₁ := (LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap
  by_cases hW : W ∈ Goodset φ₁
  . rw [Goodset_iff_equiv] at hW  
    exact ((LinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap).comp ((Submodule.subtype W.1).comp 
      (LinearEquiv.ofBijective (φ₁.domRestrict W.1) hW).symm.toLinearMap) 
  . exact 0 

/- Definition of the inverse chart.-/


def InverseChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : ((Fin r → 𝕜) →ₗ[𝕜] U) → Grassmannian 𝕜 E r := by 
  intro f 
  refine ⟨Submodule.map φ.symm (LinearMap.graph f), ?_⟩
  unfold Grassmannian
  simp only [Set.mem_setOf_eq]
  constructor
  . letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst f).symm 
    apply Module.Finite.map 
  . erw [LinearEquiv.finrank_map_eq φ.symm]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst f)]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma InverseChart_codomainGoodset (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
InverseChart φ f ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap) := by
  rw [Goodset_iff_equiv]
  unfold InverseChart
  simp only
  erw [LinearMap.coe_comp]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype]
  rw [Set.bijective_iff_bijOn_univ]
  apply Set.BijOn.comp (t := Submodule.map (LinearEquiv.symm φ) (LinearMap.graph f))
  . apply Set.BijOn.comp (t := LinearMap.graph f)
    . apply Set.BijOn.mk
      . apply Set.mapsTo_univ
      . rw [Set.injOn_iff_injective]
        exact LinearMap.graph_fst_injective f         
      . rw [Set.surjOn_iff_surjective]
        exact LinearMap.graph_fst_surjective f                 
    . simp only [Submodule.map_coe]
      apply Equiv.bijOn' φ.toEquiv 
      . simp only [LinearEquiv.coe_toEquiv, Set.maps_image_to]
        intro u
        simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Function.comp_apply, LinearEquiv.apply_symm_apply,
          imp_self]
      . simp only [LinearEquiv.coe_toEquiv_symm]
        intro u
        simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_image, Prod.exists, exists_eq_left]
        intro hu
        existsi u.1 
        rw [←hu]
        simp only [Prod.mk.eta]
        rfl
  . constructor 
    . simp only [Submodule.map_coe, Set.maps_univ_to, Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff,
      Prod.exists, exists_eq_left, Subtype.forall, Submodule.mem_map, forall_exists_index, forall_apply_eq_imp_iff',
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, forall_const]
    . rw [and_iff_right Set.injOn_subtype_val]
      have heq : Submodule.map (LinearEquiv.symm φ) (LinearMap.graph f) = (fun (x : Submodule.map 
        (LinearEquiv.symm φ) (LinearMap.graph f)) => x.1) '' Set.univ := by
        simp only [Submodule.map_coe, Set.image_univ, Subtype.range_coe_subtype, Submodule.mem_map,
          LinearMap.mem_graph_iff, Prod.exists, exists_eq_left]
        ext u
        simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_graph_iff, Prod.exists, exists_eq_left,
          Set.mem_setOf_eq]
      rw [heq]
      apply Set.surjOn_image 

/- We prove that the charts are inverses.-/

lemma InverseChartChart_aux1 (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) {u : E} (hu : u ∈ x.1) :
(Chart φ x) (φ u).1 = (φ u).2 := by
  unfold Chart
  simp only [hx, dite_true, LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype, Function.comp_apply,
    LinearMap.snd_apply]
  have heq : (φ u).1 = ((LinearMap.fst 𝕜 _ _).comp φ.toLinearMap).domRestrict x.1 ⟨u, hu⟩ := by
    simp only [LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.fst_apply]
  rw [heq]
  rw [←LinearEquiv.invFun_eq_symm]
  erw [LinearEquiv.left_inv]
 

lemma InverseChartChart_aux2 (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r}
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) :
Submodule.map φ x.1 = LinearMap.graph (Chart φ x) := by
  letI := LinearEquiv.finiteDimensional (LinearMap.graph_equiv_fst (Chart φ x)).symm
  apply FiniteDimensional.eq_of_le_of_finrank_eq
  . intro u 
    simp only [Submodule.mem_map, LinearMap.mem_graph_iff, forall_exists_index, and_imp] 
    intro v hvx hvu 
    rw [←hvu]
    apply Eq.symm
    exact InverseChartChart_aux1 φ hx hvx
  . erw [LinearEquiv.finrank_map_eq φ]
    rw [LinearEquiv.finrank_eq (LinearMap.graph_equiv_fst (Chart φ x)), x.2.2]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]


lemma InverseChartChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) {x : Grassmannian 𝕜 E r} 
(hx : x ∈ Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)) :
InverseChart φ (Chart φ x) = x := by
  unfold InverseChart 
  simp_rw [←(InverseChartChart_aux2 φ hx)]
  ext u
  simp only [Submodule.mem_map, exists_exists_and_eq_and, LinearEquiv.symm_apply_apply, exists_eq_right]
   

lemma ChartInverseChart_aux (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) {u : E}
(hu : u ∈ φ.symm '' (LinearMap.graph f)) :
(φ u).2 = f (φ u).1 := by
  rw [LinearEquiv.image_symm_eq_preimage] at hu
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_graph_iff] at hu 
  exact hu

lemma ChartInverseChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) (f : (Fin r → 𝕜) →ₗ[𝕜] U) :
Chart φ (InverseChart φ f) = f := by
  unfold Chart
  simp only [InverseChart_codomainGoodset, dite_true]
  apply LinearMap.ext 
  intro v 
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coeSubtype, Function.comp_apply, LinearMap.snd_apply]
  rw [ChartInverseChart_aux φ f]
  . apply congrArg
    change LinearMap.fst 𝕜 _ _ _ = v 
    erw [←(LinearMap.comp_apply (f := LinearMap.fst 𝕜 _ _) (g := φ.toLinearMap))]
    have hf := InverseChart_codomainGoodset φ f
    rw [Goodset_iff_equiv] at hf  
    erw [←(LinearMap.comp_apply (f := LinearMap.comp (LinearMap.fst 𝕜 _ _) φ.toLinearMap) (x := v)
      (g := LinearMap.comp (Submodule.subtype _) (LinearEquiv.symm (LinearEquiv.ofBijective _ hf)).toLinearMap))]
    conv => rhs 
            rw [←(LinearMap.id_apply (R := 𝕜) (M := Fin r → 𝕜) v)]
    apply congrFun
    rw [←LinearMap.comp_assoc]
    change 
      ↑(LinearMap.comp (LinearMap.domRestrict (LinearMap.comp (LinearMap.fst 𝕜 _ _) φ.toLinearMap) (InverseChart φ f).1) 
      (LinearEquiv.symm (LinearEquiv.ofBijective _ hf)).toLinearMap) = fun v => LinearMap.id v 
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.id_coe, id_eq] 
    rw [←LinearEquiv.invFun_eq_symm]
    have heq : (LinearMap.domRestrict (LinearMap.comp (LinearMap.fst 𝕜 (Fin r → 𝕜) U) φ.toLinearMap) (InverseChart φ f).1) =
      (LinearEquiv.ofBijective _ hf).toLinearMap := by
      ext u
      simp only [LinearMap.domRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.fst_apply, LinearEquiv.ofBijective_apply]
    nth_rewrite 1 [heq]
    erw [←LinearEquiv.toFun_eq_coe]
    ext v 
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm,
      Function.comp_apply, LinearEquiv.apply_symm_apply]   
  . change _ ∈ Submodule.map φ.symm (LinearMap.graph f)
    unfold InverseChart
    simp only [SetLike.coe_mem]

/- Definition of the chart as LocalEquiv.-/

def Chart_LocalEquiv (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : LocalEquiv (Grassmannian 𝕜 E r) ((Fin r → 𝕜) →ₗ[𝕜] U) :=
{
  toFun := Chart φ
  invFun := InverseChart φ 
  source := Goodset ((LinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toLinearMap)
  target := ⊤
  map_source' := by tauto 
  map_target' := fun f _ => InverseChart_codomainGoodset φ f
  left_inv' := fun _ hW  => InverseChartChart φ hW  
  right_inv' := fun f _ => ChartInverseChart φ f   
}

end Grassmannian
end NoTopology

section Topology

namespace Grassmannian

variable {𝕜 E U : Type*} [NormedDivisionRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 E] [CompleteSpace 𝕜]

def ContChart (φ : E ≃ₗ[𝕜] (Fin r → 𝕜) × U) : Grassmannian 𝕜 E r → ((Fin r → 𝕜) →L[𝕜] U) := by
  intro W
  exact LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := Fin r → 𝕜) (Chart φ W) 


end Grassmannian
end Topology



#exit 


class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 

