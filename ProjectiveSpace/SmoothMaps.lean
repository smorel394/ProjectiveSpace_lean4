import ProjectiveSpace.ProjectiveSpaceManifold


open Classical
noncomputable section 

universe u 

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [Nonempty {u : E | u ≠ 0}] [SeparatingDual 𝕜 E]


namespace ProjectiveSpace 

/- We prove that the Projectivization.mk' map from Estar to ℙ(E) is smooth. This is useful to construct
smooth maps to ℙ(E).-/

-- Why can't Lean infer the ChartedSpace instance on {u : E | u ≠ 0} unless I explicitly tell it to do it ?


lemma Smooth.quotientMap : 
@ContMDiff 𝕜 _ E _ _ _ _ (modelWithCornersSelf 𝕜 E) {u : E | u ≠ 0} _ inferInstance
(LinearMap.ker (Chi 𝕜 E)) _ _ _ _ (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) _ _
⊤ (Projectivization.mk' 𝕜 : {u : E | u ≠ 0} → ℙ 𝕜 E) := by 
  rw [contMDiff_iff]
  constructor 
  . rw [continuous_def]
    intro U 
    rw [isOpen_coinduced]
    simp only [ne_eq, imp_self]
  . intro u x 
    set φ := PhiForChart x 
    set hφ := PhiForChart_prop x 
    have hφ' : φ  ≠ 0 := NonzeroPhiOfPhiEqOne hφ
    unfold ModelHyperplane
    simp only [extChartAt, LocalHomeomorph.extend, modelWithCornersSelf_localEquiv, LocalEquiv.trans_refl, ne_eq,
      Set.coe_setOf, Set.mem_setOf_eq, LocalHomeomorph.coe_coe_symm]
    unfold chartAt ChartedSpace.chartAt ProjectiveSpace.instChartedSpaceProjectiveSpace 
    simp only
    rw [ProjectiveSpace.ChartAt_source]
    apply ContDiffOn.mono (s := {u : E | φ u ≠ 0})
    swap
    . intro v 
      simp only [Set.mem_inter_iff, Set.mem_preimage, Projectivization.mk'_eq_mk, Set.mem_setOf_eq, and_imp]
      intro hv1 hv2
      erw [Estar.chartAt.target u] at hv1 
      change v ≠ 0 at hv1 
      conv at hv2 => congr
                     congr 
                     erw [←(Estar.chartAt.inverse u hv1)]
      rw [←GoodsetPreimage] at hv2 
      exact hv2      
    . unfold ProjectiveSpace.ChartAt 
      change ContDiffOn 𝕜 ⊤ ((_ ∘ (ProjectiveSpace.ChartAt_aux x)) ∘ _ ∘ _) _ 
      refine @ContDiffOn.continuousLinearMap_comp 𝕜 _ E _ _ (LinearMap.ker φ) _ _ 
         (LinearMap.ker (Chi 𝕜 E)) _ _ _ _ ⊤
         (OneIsomorphismBetweenTwoClosedHyperplanes hφ' (hChi 𝕜 E)) ?_ 
      set g := fun (u : E) => ContinuousRetractionOnHyperplane (PhiForChart_prop x) (((φ x.rep) / (φ u)) • u - x.rep) 
      refine ContDiffOn.congr (f := g) ?_ ?_
      swap
      . intro v hv
        have hvnz : v ≠ 0 := NonzeroOfNonzeroPhi hv
        simp only [Function.comp_apply, Projectivization.mk'_eq_mk, ne_eq, map_sub, map_smul]
        conv => lhs
                congr
                rfl
                congr
                erw [←(Estar.chartAt.inverse u hvnz)] 
        unfold ProjectiveSpace.ChartAt_aux Chart_LocalHomeomorph Chart_LocalEquiv Chart
        simp only [map_sub, map_smul, Set.top_eq_univ, LocalHomeomorph.mk_coe, sub_left_inj]
        rw [hφ]
        apply Projectivization_vs_LinearMap (φ : E →ₗ[𝕜] 𝕜) (Projectivization.rep_nonzero _) hvnz 
        rw [Projectivization.mk_rep]
      . apply ContDiffOn.continuousLinearMap_comp 
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
ℙ 𝕜 E → {u : E | u ≠ 0} := by 
  intro y 
  by_cases hgood : φ y.rep = 0 
  . exact Classical.choice inferInstance  
  . refine ⟨(1 / (φ y.rep)) • y.rep, ?_⟩
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


def RetractionOnHyperplane {φ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) : {u : E | u ≠ 0} → {u : E | φ u = 1} := by 
  intro u 
  by_cases h : φ u = 0 
  . exact ⟨Classical.choose (NonzeroExistsEqOne hφ), Classical.choose_spec (NonzeroExistsEqOne hφ)⟩
  . refine ⟨(1 / (φ u)) • u.1, ?_⟩
    simp only [one_div, Set.mem_setOf_eq, map_smul, smul_eq_mul, ne_eq, h, not_false_eq_true, inv_mul_cancel]

lemma RetractionOnHyperplaneIsContinuousOn {φ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) :
ContinuousOn (RetractionOnHyperplane hφ) {u : {u : E | u ≠ 0} | φ u.1 ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict, continuous_induced_rng]
  set f : {u : {u : E | u ≠ 0} | φ u.1 ≠ 0} → E :=  fun u => (1 / φ u.1) • u.1.1
  have heq : ∀ u, f u = (Subtype.val ∘ Set.restrict {u : {u : E | u ≠ 0} | φ u.1 ≠ 0} (RetractionOnHyperplane hφ)) u := by
    intro u
    simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Function.comp_apply, Set.restrict_apply] 
    unfold RetractionOnHyperplane
    have hu : φ u ≠ 0 := u.2
    simp only [one_div, hu, Set.mem_setOf_eq, dite_false]
  refine Continuous.congr ?_ heq 
  apply Continuous.smul
  . simp_rw [one_div]
    apply Continuous.inv₀ 
    . rename_i inst_4
      aesop_unfold [Function.comp]
      simp_all only [ne_eq, nonempty_subtype, Set.coe_setOf, Set.mem_setOf_eq, one_div, Set.restrict_apply,
        Subtype.forall]
      unhygienic with_reducible aesop_destruct_products
      apply Continuous.clm_apply
      · apply continuous_const
      · apply Continuous.comp'
        · apply continuous_induced_dom
        · apply continuous_induced_dom
    . exact fun u => u.2 
  . rename_i inst_4
    aesop_unfold [Function.comp]
    simp_all only [ne_eq, nonempty_subtype, Set.coe_setOf, Set.mem_setOf_eq, one_div, Set.restrict_apply,
      Subtype.forall]
    unhygienic with_reducible aesop_destruct_products
    apply Continuous.comp'
    · apply continuous_induced_dom
    · apply continuous_induced_dom

def InclusionHyperplane (φ : E →L[𝕜] 𝕜) : {u : E | φ u = 1} → {u : E | u ≠ 0} := by
  intro ⟨u, hu⟩
  refine ⟨u, ?_⟩
  change u ≠ 0
  by_contra habs 
  rw [habs] at hu
  simp only [Set.mem_setOf_eq, map_zero, zero_ne_one] at hu  

lemma InclusionHyperplaneIsContinuous (φ : E →L[𝕜] 𝕜) :
Continuous (InclusionHyperplane φ) := by
  unfold InclusionHyperplane 
  simp only [Set.coe_setOf, Set.mem_setOf_eq]
  continuity

lemma ProjectiveSpace.LocalSection_IsContinuousOn {φ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) :
ContinuousOn (ProjectiveSpace.LocalSection φ) (Goodset φ) := by 
  rw [continuousOn_open_iff (GoodsetIsOpen φ)]
  intro U hU 
  rw [isOpen_coinduced]
  have heq : (Projectivization.mk' 𝕜) ⁻¹' (Goodset φ ∩ (LocalSection φ) ⁻¹' U) = {u | φ u.1 ≠ 0} ∩
    (RetractionOnHyperplane hφ) ⁻¹' ((InclusionHyperplane φ) ⁻¹' U) := by 
    ext u 
    simp only [Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Projectivization.mk'_eq_mk,
      Set.coe_setOf]
    rw [←GoodsetPreimage]
    change _ ↔ φ u ≠ 0 ∧ _ 
    simp only [and_congr_right_iff]
    intro hu 
    have hunz := NonzeroOfNonzeroPhi hu 
    unfold RetractionOnHyperplane 
    simp only [hu, Set.mem_setOf_eq, dite_false]
    unfold LocalSection
    rw [GoodsetPreimage φ hunz] at hu 
    change φ _ ≠ 0 at hu 
    simp only [hu, dite_false, Set.mem_setOf_eq]
    have heq' : (1 / φ (Projectivization.mk 𝕜 u.1 hunz).rep) • (Projectivization.mk 𝕜 u.1 hunz).rep = 
       (1/ φ u) • u.1 := by 
      apply Projectivization_vs_LinearMap_cor 
      rw [Projectivization.mk_rep]   
    simp_rw [heq']
    unfold InclusionHyperplane
    simp only 
  rw [heq] 
  refine ContinuousOn.preimage_open_of_open (RetractionOnHyperplaneIsContinuousOn hφ) ?_ 
    (IsOpen.preimage (InclusionHyperplaneIsContinuous φ) hU)
  apply NonzeroPhiIsOpen'


lemma ProjectiveSpace.LocalSection_IsSmoothOn (φ : E →L[𝕜] 𝕜) :
ContMDiffOn (ModelHyperplane 𝕜 E) (modelWithCornersSelf 𝕜 E) ⊤ (ProjectiveSpace.LocalSection φ) (Goodset φ) := by 
  by_cases hφ : φ = 0 
  . rw [GoodsetZero hφ]
    apply contMDiffOn_of_locally_contMDiffOn
    simp only [Set.mem_empty_iff_false, Set.empty_inter, IsEmpty.forall_iff, implies_true]
  . match NonzeroExistsEqOne hφ with
    | ⟨v, hv⟩ => 
      have hv' : φ v ≠ 0 := by rw [hv]; exact one_ne_zero
      set x := Projectivization.mk 𝕜 v (NonzeroOfNonzeroPhi hv')
      set y := x.rep
      rw [contMDiffOn_iff_of_mem_maximalAtlas
      (e := (LocalHomeomorph.transHomeomorph 
        (Chart_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
        (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) (hChi 𝕜 E)))))
      (e' := (OpenEmbedding.toLocalHomeomorph (fun u => u.1) EstarToE))
      (by apply SmoothManifoldWithCorners.subset_maximalAtlas 
          change _ ∈ @atlas (LinearMap.ker (Chi 𝕜 E)) _ (ℙ 𝕜 E) _ _ 
          change _ ∈  {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = LocalHomeomorph.transHomeomorph 
              (Chart_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
              (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) (hChi 𝕜 E)))}
          simp only [Set.mem_setOf_eq]
          existsi φ; existsi v; existsi hv
          rfl)
       (by apply SmoothManifoldWithCorners.subset_maximalAtlas 
           change _ ∈ {(OpenEmbedding.toLocalHomeomorph (fun u => u.1) EstarToE)}
           simp only [Set.mem_singleton_iff])
        (by rw [ProjectiveSpace.Chart_source])
        (by simp only [OpenEmbedding.toLocalHomeomorph_source]
            apply Set.mapsTo_univ)]
      constructor
      . exact ProjectiveSpace.LocalSection_IsContinuousOn hφ
      . apply ContDiffOn.mono (s := ⊤)
        swap
        . simp only [LocalHomeomorph.extend, ne_eq, LocalEquiv.coe_trans, ModelWithCorners.toLocalEquiv_coe,
          LocalHomeomorph.toFun_eq_coe, LocalHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
          Function.comp_apply, Set.top_eq_univ, Set.subset_univ]
        . set f : LinearMap.ker (Chi 𝕜 E) → E := (fun u => v + u.1) ∘ 
            (OneIsomorphismBetweenTwoClosedHyperplanes hφ (hChi 𝕜 E)).symm 
          apply ContDiffOn.congr (f := f)
          swap
          . intro u _ 
            simp only [ne_eq, Set.coe_setOf, LocalHomeomorph.extend, Set.mem_setOf_eq, modelWithCornersSelf_localEquiv,
              LocalEquiv.trans_refl, LocalHomeomorph.toFun_eq_coe, LocalEquiv.coe_trans_symm,
              LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
              ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph,
              ModelWithCorners.toLocalEquiv_coe_symm, Function.comp_apply]  
            unfold ModelHyperplane
            simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, modelWithCornersSelf_coe_symm, id_eq]    
            generalize (OneIsomorphismBetweenTwoClosedHyperplanes hφ (hChi 𝕜 E)).symm u = u  
            have hu1 : φ (v + u.1) = 1 := by
              rw [map_add, hv, u.2, add_zero]  
            have hu2 : φ (v + u.1) ≠ 0 := by 
              rw [hu1]
              exact one_ne_zero 
            have hu3 : v + u.1 ≠ 0 := NonzeroOfNonzeroPhi hu2  
            unfold Chart_LocalHomeomorph Chart_LocalEquiv
            simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, Set.top_eq_univ, LocalHomeomorph.mk_coe_symm,
              LocalEquiv.coe_symm_mk]            
            unfold InverseChart LocalSection
            have hgood : φ (Projectivization.mk 𝕜 (v + u.1) hu3).rep ≠ 0 := by
              change Projectivization.mk 𝕜 (v + u.1) hu3 ∈ Goodset φ
              rw [←GoodsetPreimage]
              exact hu2             
            simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq, hgood, one_div, dite_false]    
            erw [OpenEmbedding.toLocalHomeomorph_apply (fun u : {u : E | u ≠ 0} => u.1) EstarToE]
            simp only
            rw [←one_div]
            have h : v + u.1 = (1 / φ (v + u.1)) • (v + u.1) := by 
              rw [hu1, div_self, one_smul]
              exact one_ne_zero 
            conv => rhs 
                    rw [h]
            apply Projectivization_vs_LinearMap_cor 
            rw [Projectivization.mk_rep]
          . rw [Set.top_eq_univ, contDiffOn_univ]
            change ContDiff 𝕜 ⊤ (_ ∘ _)
            refine @ContDiff.comp_continuousLinearMap 𝕜 _ (LinearMap.ker φ) _ _ E _ _
              (LinearMap.ker (Chi 𝕜 E)) _ _ ⊤ (fun u => v + u.1) 
              (OneIsomorphismBetweenTwoClosedHyperplanes hφ (hChi 𝕜 E)).symm ?_
            apply ContDiff.add
            . apply contDiff_const
            . exact ContinuousLinearMap.contDiff (Submodule.subtypeL (LinearMap.ker φ)) 
 
/- If f is map from ℙ(E) to a manifold such that f ∘ Projectivization.mk'is smooth, we prove that f is
smooth. This is useful to construct smooth maps from ℙ(E).-/

lemma Smooth.mapFromProjectiveSpace {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type u}
[TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners I M] {f : ℙ 𝕜 E → M} 
(hf : ContMDiff (modelWithCornersSelf 𝕜 E) I ⊤ (f ∘ (Projectivization.mk' 𝕜) : {u : E | u ≠ 0} → M)) :
@ContMDiff 𝕜 _ (LinearMap.ker (Chi 𝕜 E)) _ _ (LinearMap.ker (Chi 𝕜 E)) _ (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) _ 
_ F _ _ H _ I M _ _ ⊤ f := by 
  apply contMDiff_of_locally_contMDiffOn
  intro x 
  set φ := PhiForChart x 
  set hφ := PhiForChart_prop x 
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
    refine @ContMDiffOn.comp 𝕜 _ (LinearMap.ker (Chi 𝕜 E)) _ _ (LinearMap.ker (Chi 𝕜 E)) _ 
      (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) _ _ E _ _ E _ (modelWithCornersSelf 𝕜 E) 
      {u : E | u ≠ 0} _ _ 
      F _ _ H _ I M _ _ (ProjectiveSpace.LocalSection φ) (Goodset φ) ⊤ ⊤ 
      (f ∘ (Projectivization.mk' 𝕜)) (ContMDiff.contMDiffOn (s := ⊤) hf) ?_ ?_
    . exact ProjectiveSpace.LocalSection_IsSmoothOn φ  
    . simp only [Set.top_eq_univ, Set.preimage_univ, Set.subset_univ]


lemma Smooth.mapFromProductProjectiveSpace {F G : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] 
[NormedAddCommGroup G] [NormedSpace 𝕜 G] {H H' : Type u} [TopologicalSpace H] [TopologicalSpace H']
{I : ModelWithCorners 𝕜 F H} {I' : ModelWithCorners 𝕜 G H'} {M N : Type u} [TopologicalSpace M] 
[ChartedSpace H M] [SmoothManifoldWithCorners I M] [TopologicalSpace N] [ChartedSpace H' N]
[SmoothManifoldWithCorners I' N] 
{f : N × ℙ 𝕜 E → M} 
(hf : ContMDiff (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 E)) I ⊤ 
(f ∘ (Prod.map (fun x => x) (Projectivization.mk' 𝕜)) : N × {u : E | u ≠ 0} → M)) :
@ContMDiff 𝕜 _ (G × (LinearMap.ker (Chi 𝕜 E))) _ _ (H' × (LinearMap.ker (Chi 𝕜 E))) _ 
(ModelWithCorners.prod I' (ModelHyperplane 𝕜 E)) (N × (ℙ 𝕜 E)) _ 
(@prodChartedSpace H' _ N _ _ (LinearMap.ker (Chi 𝕜 E)) _ (ℙ 𝕜 E) _ _) 
F _ _ H _ I M _ _ ⊤ f := by 
  apply @contMDiff_of_locally_contMDiffOn 𝕜 _ (G × (LinearMap.ker (Chi 𝕜 E))) _ _ (H' × (LinearMap.ker (Chi 𝕜 E))) _
    (ModelWithCorners.prod I' (ModelHyperplane 𝕜 E)) (N × (ℙ 𝕜 E)) _ 
    (prodChartedSpace H' N (LinearMap.ker (Chi 𝕜 E)) (ℙ 𝕜 E)) 
  intro x 
  set φ := PhiForChart x.2
  set hφ := PhiForChart_prop x.2 
  existsi ⊤ ×ˢ (Goodset φ) 
  constructor 
  . apply IsOpen.prod 
    . simp only [Set.top_eq_univ, isOpen_univ]
    . exact GoodsetIsOpen φ 
  . constructor 
    . erw [Set.mem_prod]
      simp only [Set.top_eq_univ, Set.mem_univ, true_and]  
      change φ x.2.rep ≠ 0 
      rw [hφ]
      exact one_ne_zero 
    . set g : N × ℙ 𝕜 E → M := f ∘ (Prod.map (fun x => x) 
        (Projectivization.mk' 𝕜)) ∘ (Prod.map (fun x => x) (ProjectiveSpace.LocalSection φ)) with hgdef
      have heq : ∀ (y : N × ℙ 𝕜 E), y ∈ ⊤ ×ˢ (Goodset φ) → f y = g y := by sorry
      refine @ContMDiffOn.congr 𝕜 _ (G × (LinearMap.ker (Chi 𝕜 E))) _ _ (H' × (LinearMap.ker (Chi 𝕜 E))) _
        (ModelWithCorners.prod I' (ModelHyperplane 𝕜 E)) (N × (ℙ 𝕜 E)) _ 
        (prodChartedSpace H' N (LinearMap.ker (Chi 𝕜 E)) (ℙ 𝕜 E)) F _ _ H _ I M
        _ _ g f (⊤ ×ˢ (Goodset φ)) ⊤ ?_ heq  
      rw [hgdef, ←Function.comp.assoc]
      have hf' := @ContMDiff.contMDiffOn 𝕜 _ (G × E) _ _ (H' × E) _ (ModelWithCorners.prod I'
        (modelWithCornersSelf 𝕜 E)) (N × {u : E | u ≠ 0}) _ 
        (@prodChartedSpace H' _ N _ _ E _ {u : E | u ≠ 0} _ _)
        F _ _ H _ I M _ _ _ ⊤ ⊤ hf 
      refine @ContMDiffOn.comp 𝕜 _ (G × (LinearMap.ker (Chi 𝕜 E))) _ _ (H' × (LinearMap.ker (Chi 𝕜 E))) _
        (ModelWithCorners.prod I' (ModelHyperplane 𝕜 E)) (N × (ℙ 𝕜 E)) _ 
        (prodChartedSpace H' N (LinearMap.ker (Chi 𝕜 E)) (ℙ 𝕜 E)) (G × E) _ _ (H' × E) _
        (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 E)) (N × {u : E | u ≠ 0}) _ 
        (@prodChartedSpace H' _ N _ _ E _ {u : E | u ≠ 0} _ _) F _ _ H _ I M _ _ 
        (Prod.map (fun x => x) (ProjectiveSpace.LocalSection φ)) (⊤ ×ˢ (Goodset φ)) ⊤ ⊤ _ 
        hf' ?_ ?_
      . refine @ContMDiffOn.prod_map 𝕜 _ G _ _ H' _ I' N _ _ G _ _ H' _ I' N _ _ 
          (LinearMap.ker (Chi 𝕜 E)) _ _ (LinearMap.ker (Chi 𝕜 E)) _ (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) _ _ 
          E _ _ E _ (modelWithCornersSelf 𝕜 E) {u : E | u ≠ 0} _ _ (fun x => x) ⊤ ⊤ 
          (ProjectiveSpace.LocalSection φ) (Goodset φ) ?_ ?_   
        . exact contMDiffOn_id 
        . exact ProjectiveSpace.LocalSection_IsSmoothOn φ  
      . simp only [Set.top_eq_univ, Set.preimage_univ, Set.subset_univ]


