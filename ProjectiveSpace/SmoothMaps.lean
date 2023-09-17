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
  

/- The Projectivization.mk' map admits local smooth sections: if we have a nonzero continuous linear form φ
and a point x in ℙ(E) such that φ(x.rep)=1, then the map y => (1 / φ(y.rep)) • y.rep sends
Goodset φ to {φ = 1}, hence to E-{0}, and it is a section of Projectivization.mk'. We introduce it
and prove that it is smooth.-/

def ProjectiveSpace.LocalSection (φ : E →L[𝕜] 𝕜) :
ℙ 𝕜 E → Estar E := by 
  intro y 
  by_cases hgood : φ y.rep = 0 
  . exact Classical.choice inferInstance  
  . refine ⟨(1 / (φ y.rep)) • y.rep, ?_⟩
    unfold Estar
    simp only [one_div, ne_eq, Set.mem_setOf_eq, smul_eq_zero, inv_eq_zero]
    rw [not_or, and_iff_right hgood]
    exact NonzeroOfNonzeroPhi hgood

lemma ProjectiveSpace.LocalSectionIsSection (φ : E →L[𝕜] 𝕜) {y : ℙ 𝕜 E} (hy : y ∈ Goodset φ) : 
Projectivization.mk' 𝕜 (ProjectiveSpace.LocalSection φ y) = y := by
  unfold ProjectiveSpace.LocalSection
  change φ (y.rep) ≠ 0 at hy
  simp only [hy, one_div, dite_false, Projectivization.mk'_eq_mk]
  conv => rhs
          rw [←(Projectivization.mk_rep y)]
  apply Eq.symm
  rw [Projectivization.mk_eq_mk_iff]  
  existsi Units.mk0 (φ y.rep) hy 
  simp only [Units.smul_mk0, ne_eq]
  rw [smul_smul]
  simp only [ne_eq, hy, not_false_eq_true, mul_inv_cancel, one_smul]

lemma ProjectiveSpace.LocalSection_IsContinuousOn (φ : E →L[𝕜] 𝕜) :
ContinuousOn (ProjectiveSpace.LocalSection φ) (Goodset φ) := by sorry

lemma ProjectiveSpace.LocalSection_IsSmoothOn (φ : E →L[𝕜] 𝕜) :
@ContMDiffOn 𝕜 _ (LinearMap.ker χ) _ _ (LinearMap.ker χ) _ ModelHyperplane (ℙ 𝕜 E) _ 
(ChartedSpaceProjectiveSpace hχ hsep) E _ _ E _ (modelWithCornersSelf 𝕜 E) (Estar E) _ _ ⊤
(ProjectiveSpace.LocalSection φ) (Goodset φ) := by 
  set CS := ChartedSpaceProjectiveSpace hχ hsep
  set SM := ProjectiveSpace_SmoothManifold hχ hsep 
  by_cases hφ : φ = 0 
  . rw [GoodsetZero hφ]
    apply contMDiffOn_of_locally_contMDiffOn
    simp only [Set.mem_empty_iff_false, Set.empty_inter, IsEmpty.forall_iff, implies_true]
  . have hφ' : ∃ (v : E), φ v = 1 := by 
      match ContinuousLinearMap.exists_ne_zero hφ with 
      | ⟨w, hw⟩ =>
        existsi (1 / (φ w)) • w 
        simp only [one_div, map_smul, smul_eq_mul, ne_eq]
        simp only [ne_eq, hw, not_false_eq_true, inv_mul_cancel]
    match hφ' with 
    | ⟨v, hv⟩ =>
      have hv' : φ v ≠ 0 := by rw [hv]; exact one_ne_zero
      set x := Projectivization.mk 𝕜 v (NonzeroOfNonzeroPhi hv')
      set y := x.rep
      rw [@contMDiffOn_iff_of_mem_maximalAtlas 𝕜 _ (LinearMap.ker χ) _ _ _ _ ModelHyperplane (ℙ 𝕜 E) _
        CS SM E _ _ _ _ (modelWithCornersSelf 𝕜 E) (Estar E) _ _ _ (LocalHomeomorph.transHomeomorph 
        (Chart1_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
        (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))) 
        (OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE E)) (ProjectiveSpace.LocalSection φ)
        (Goodset φ) ⊤ 
        (by apply SmoothManifoldWithCorners.subset_maximalAtlas 
            change _ ∈ @atlas (LinearMap.ker χ) _ (ℙ 𝕜 E) _ (ChartedSpaceProjectiveSpace hχ hsep) 
            change _ ∈  {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = LocalHomeomorph.transHomeomorph 
              (Chart1_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
              (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))}
            simp only [Set.mem_setOf_eq]
            existsi φ; existsi v; existsi hv
            rfl)
        (by apply SmoothManifoldWithCorners.subset_maximalAtlas 
            change _ ∈ {(OpenEmbedding.toLocalHomeomorph (fun u => u.1) (EstarToE E))}
            simp only [Set.mem_singleton_iff])
        (by rw [ProjectiveSpace.Chart_source])
        (by simp only [OpenEmbedding.toLocalHomeomorph_source]
            apply Set.mapsTo_univ)]
      constructor
      . exact ProjectiveSpace.LocalSection_IsContinuousOn φ 
      . sorry 

 

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
  apply contMDiff_of_locally_contMDiffOn
  intro x 
  set φ := (Classical.choose (hsep.exists_eq_one (Projectivization.rep_nonzero x)))
  set hφ := (Classical.choose_spec (hsep.exists_eq_one (Projectivization.rep_nonzero x)))
  exists Goodset φ
  rw [and_iff_right (GoodsetIsOpen φ)]
  constructor 
  . change φ x.rep ≠ 0
    rw [hφ]
    exact one_ne_zero
  . set g : ℙ 𝕜 E → M := f ∘ (Projectivization.mk' 𝕜) ∘ (ProjectiveSpace.LocalSection φ) with hgdef
    have heq : ∀ (y : ℙ 𝕜 E), y ∈ Goodset φ → f y = g y := by 
      intro y hy 
      rw [hgdef]
      simp only [ne_eq, Function.comp_apply]
      rw [ProjectiveSpace.LocalSectionIsSection]
      exact hy
    refine ContMDiffOn.congr ?_ heq  
    rw [hgdef, ←Function.comp.assoc]
    refine @ContMDiffOn.comp 𝕜 _ (LinearMap.ker χ) _ _ (LinearMap.ker χ) _ ModelHyperplane (ℙ 𝕜 E) _
      (ChartedSpaceProjectiveSpace hχ hsep) E _ _ E _ (modelWithCornersSelf 𝕜 E) (Estar E) _ _ 
      F _ _ H _ I M _ _ (ProjectiveSpace.LocalSection φ) (Goodset φ) ⊤ ⊤ 
      (f ∘ (Projectivization.mk' 𝕜)) (ContMDiff.contMDiffOn (s := ⊤) hf) ?_ ?_
    . apply ProjectiveSpace.LocalSection_IsSmoothOn 
    . simp only [Set.top_eq_univ, Set.preimage_univ, Set.subset_univ]


