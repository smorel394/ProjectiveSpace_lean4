import ProjectiveSpace.ProjectiveSpaceGeneral



open Classical
noncomputable section 

universe u 

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace 𝕜]  {hsep : SeparatingDual 𝕜 E}
variable {χ : E →L[𝕜] 𝕜} (hχ : χ ≠ 0)
variable [Nonempty (Estar E)]

/- We prove that the Projectivization.mk' map from Estar to ℙ(E) is smooth. This is useful to construct
smooth maps to ℙ(E).-/

lemma Smooth.quotientMap : 
@ContMDiff 𝕜 _ E _ _ _ _ (modelWithCornersSelf 𝕜 E) (Estar E) _ _ (LinearMap.ker χ) _ _ _ _
(ModelHyperplane) (ℙ 𝕜 E) _ (ChartedSpaceProjectiveSpace hχ hsep) ⊤ 
(Projectivization.mk' 𝕜) := by 
  set CS := ChartedSpaceProjectiveSpace hχ hsep
  set SM := ProjectiveSpace_SmoothManifold hχ hsep 
  rw [@contMDiff_iff 𝕜 _ E _ _ _ _ (modelWithCornersSelf 𝕜 E) (Estar E) _ _ _ (LinearMap.ker χ) _ _ _ _
    (ModelHyperplane) (ℙ 𝕜 E) _ CS SM _ ⊤]
  constructor 
  . rw [continuous_def]
    intro U 
    rw [isOpen_coinduced]
    simp only [ne_eq, imp_self]
  . intro u x 
    unfold ModelHyperplane
    simp only [extChartAt, LocalHomeomorph.extend, modelWithCornersSelf_localEquiv, LocalEquiv.trans_refl,
      OpenEmbedding.toLocalHomeomorph_source, LocalHomeomorph.singletonChartedSpace_chartAt_eq,
      LocalHomeomorph.coe_coe_symm, OpenEmbedding.toLocalHomeomorph_target, Subtype.range_coe_subtype, Set.setOf_mem_eq]
    unfold chartAt ChartedSpace.chartAt ChartedSpaceProjectiveSpace
    simp only
    rw [ProjectiveSpace.ChartAt_source] 
    set φ := (Classical.choose (hsep.exists_eq_one (Projectivization.rep_nonzero x))) with hφdef
    set hφ := (Classical.choose_spec (hsep.exists_eq_one (Projectivization.rep_nonzero x)))
    have heq : (Estar E) ∩ ((OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE E)).symm ⁻¹'
      ((Projectivization.mk' 𝕜) ⁻¹' (Goodset φ))) = {u : E | φ u ≠ 0} := by 
      ext u 
      unfold Estar EstarToE
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Projectivization.mk'_eq_mk]
      rw [←GoodsetPreimage]
      constructor 
      . intro ⟨hu1, hu2⟩  
        erw [←(OpenEmbeddingEstar.inverse E hu1)] at hu2  
        exact hu2  
      . intro hu 
        have hunz := NonzeroOfNonzeroPhi hu 
        erw [←(OpenEmbeddingEstar.inverse E hunz)] 
        exact ⟨hunz, hu⟩ 
    rw [heq]  
    unfold ProjectiveSpace.ChartAt 
    change ContDiffOn 𝕜 ⊤ ((_ ∘ (ProjectiveSpace.ChartAt_aux hsep x)) ∘ _ ∘ _) _ 
    rw [Function.comp.assoc]
    refine @ContDiffOn.continuousLinearMap_comp 𝕜 _ E _ _ (LinearMap.ker φ) _ _ (LinearMap.ker χ) _ _
      _ _ ⊤ (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hφ) hχ) ?_
    set f := (ProjectiveSpace.ChartAt_aux hsep x) ∘ (Projectivization.mk' 𝕜) ∘ 
      (OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE E)).symm 
    set g := fun (u : E) => ContinuousRetractionOnHyperplane hφ (((φ x.rep) / (φ u)) • u - x.rep) 
    have hcongr : ∀ (u : E), u ∈ {u : E | φ u ≠ 0} → f u = g u := by 
      intro u hu 
      have hunz := NonzeroOfNonzeroPhi hu
      simp only [ne_eq, Function.comp_apply, Projectivization.mk'_eq_mk, map_sub, map_smul]
      conv => lhs 
              congr 
              rfl
              congr 
              erw [←(OpenEmbeddingEstar.inverse E hunz)] 
      unfold ProjectiveSpace.ChartAt_aux Chart1_LocalHomeomorph Chart1_LocalEquiv Chart1
      simp only [map_sub, map_smul, Set.top_eq_univ, LocalHomeomorph.mk_coe, sub_left_inj]
      simp_rw [←hφdef]
      rw [hφ]
      erw [@Projectivization_vs_LinearMap 𝕜 E _ _ _ (LinearMap.ker φ) _ _ φ _ _ (Projectivization.rep_nonzero 
        (Projectivization.mk 𝕜 u hunz)) hunz (ContinuousRetractionOnHyperplane hφ) (Projectivization.mk_rep _)] 
      simp only [ContinuousLinearMap.coe_coe, one_div]
    refine ContDiffOn.congr ?_ hcongr 
    apply ContDiffOn.continuousLinearMap_comp 
    apply ContDiffOn.sub 
    . simp_rw [hφ, one_div]
      apply ContDiffOn.smul
      . apply ContDiffOn.inv 
        . apply ContDiff.contDiffOn
          apply ContinuousLinearMap.contDiff 
        . exact fun _ hu => hu  
      . exact contDiffOn_id 
    . apply contDiffOn_const  
  
    
/- If f is map from ℙ(E) to a manifold such that f ∘ Projectivization.mk'is smooth, we prove that f is
smooth. This is useful to construct smooth maps from ℙ(E).-/



lemma Smooth.mapFromProjectiveSpace {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type u}
[TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners I M] {f : ℙ 𝕜 E → M} 
(hf : ContMDiff (modelWithCornersSelf 𝕜 E) I ⊤ (f ∘ (Projectivization.mk' 𝕜) : (Estar E) → M)) :
@ContMDiff 𝕜 _ (LinearMap.ker χ) _ _ (LinearMap.ker χ) _ ModelHyperplane (ℙ 𝕜 E) _ 
(ChartedSpaceProjectiveSpace hχ hsep) F _ _ H _ I M _ _ ⊤ f := by 
  set CS := ChartedSpaceProjectiveSpace hχ hsep
  set SM := ProjectiveSpace_SmoothManifold hχ hsep 
  rw [contMDiff_iff] at hf ⊢
  constructor
  . rw [continuous_def] at hf ⊢
    intro U hU 
    rw [isOpen_coinduced, ←Set.preimage_comp]
    exact hf.1 U hU   
  . intro x y 
    have h := hf.2 ⟨x.rep, Projectivization.rep_nonzero x⟩ y  
    

