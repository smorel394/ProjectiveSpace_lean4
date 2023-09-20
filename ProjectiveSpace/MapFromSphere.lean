import ProjectiveSpace.SmoothMaps 
import Mathlib.Geometry.Manifold.Instances.Sphere

open Classical
noncomputable section 

universe u 

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : Nat}
  [Fact (FiniteDimensional.finrank ℝ E = n + 1)]

lemma SphereToEstar_aux (x : Metric.sphere (0 : E) 1) : x.1 ≠ 0 := by
  by_contra habs 
  have h := x.2 
  simp only [mem_sphere_iff_norm, sub_zero] at h 
  rw [habs] at h
  simp only [norm_zero, zero_ne_one] at h      

def SphereToEstar : Metric.sphere (0 : E) 1 → {u : E // u ≠ 0} := by
  intro x
  exact ⟨x.1, SphereToEstar_aux E x⟩
  

instance : Nonempty {u : E // u ≠ 0} := sorry 

lemma SphereToEstar_IsSmooth : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
(modelWithCornersSelf ℝ E) ⊤ (SphereToEstar E) := by 
  have : Nonempty {u : E | u ≠ 0} := by 
      have hne' : Nonempty {u : E // u ≠ 0} := inferInstance
      exact hne'
  set e : LocalHomeomorph {u : E // u ≠ 0} E := OpenEmbedding.toLocalHomeomorph (fun u => u.1) EstarToE
  have he : e ∈ SmoothManifoldWithCorners.maximalAtlas (modelWithCornersSelf ℝ E) {u : E // u ≠ 0} := by
    apply SmoothManifoldWithCorners.subset_maximalAtlas 
    change _ ∈ {(OpenEmbedding.toLocalHomeomorph (fun u => u.1) EstarToE)} 
    simp only [Set.mem_singleton_iff]
  have heq : SphereToEstar E = e.symm ∘ Subtype.val := by
    unfold SphereToEstar
    ext x
    simp only [Function.comp_apply]
    have h : x.1 = (⟨x.1, SphereToEstar_aux E x⟩ : {u : E | u ≠ 0}).1 := by simp only
    rw [h, SetCoe.ext_iff, LocalHomeomorph.eq_symm_apply]
    rw [OpenEmbedding.toLocalHomeomorph_apply]
    .  rw [OpenEmbedding.toLocalHomeomorph_source]
       simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Set.mem_univ]
    . rw [OpenEmbedding.toLocalHomeomorph_target]
      simp only [ne_eq, Set.coe_setOf, Subtype.range_coe_subtype, Set.mem_setOf_eq, SphereToEstar_aux E x,
        not_false_eq_true]
  rw [heq, ←contMDiffOn_univ]
  apply ContMDiffOn.comp (I' := modelWithCornersSelf ℝ E) (t := {u : E | u ≠ 0})
  . have h : e.target = {u : E | u ≠ 0} := by 
      ext u
      simp only [ne_eq, OpenEmbedding.toLocalHomeomorph_target, Subtype.range_coe_subtype, Set.mem_setOf_eq]
    rw [←h]
    exact contMDiffOn_symm_of_mem_maximalAtlas he
  . rw [contMDiffOn_univ]
    exact contMDiff_coe_sphere 
  . intro x _ 
    simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq]
    exact SphereToEstar_aux E x 

namespace ProjectiveSpace

lemma MapFromSphere_IsSmooth : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
(ModelHyperplane ℝ E) ⊤ (Projectivization.mk' ℝ ∘ SphereToEstar E ) := by
  apply ContMDiff.comp (I' := modelWithCornersSelf ℝ E)
  . exact Smooth.quotientMap ℝ E 
  . exact SphereToEstar_IsSmooth E 

end ProjectiveSpace
