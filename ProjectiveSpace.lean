import ProjectiveSpace.ProjectiveSpaceGeneral


open Classical
noncomputable section 

universe u 



variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

variable (n : ℕ)  [Fact (FiniteDimensional.finrank 𝕜 E = n + 1)]
  [CompleteSpace 𝕜]



instance : Nonempty (Estar E) := sorry 

/- The case of projective space of a 𝕜-vector space of dimension n+1.-/
section PnCharts

/- Charts on ℙ 𝕜 E with fixed codomain 𝕜^n.-/


def Chart1_LocalHomeomorphFixedCodomain_kn {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) 
 : LocalHomeomorph (ℙ 𝕜 E) (Fin n → 𝕜) :=
LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hv) 
(ContinuousLinearEquiv.toHomeomorph
(ClosedHyperplaneToFixedSpace (hdim n) 
  (NonzeroPhiOfPhiEqOne hv)))


lemma Chart1_LocalHomeomorphFixedCodomain_kn_source {φ : E →L[𝕜] 𝕜} {x : ℙ 𝕜 E} 
(hx: φ x.rep = 1) : 
x ∈ (Chart1_LocalHomeomorphFixedCodomain_kn n hx).toLocalEquiv.source := by 
  unfold Chart1_LocalHomeomorphFixedCodomain_kn ClosedHyperplaneToFixedSpace 
  simp only [LocalHomeomorph.transHomeomorph_source]
  change φ x.rep ≠ 0
  rw [hx]
  exact one_ne_zero 

def Chart1PnAt (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (Fin n → 𝕜) :=
Chart1_LocalHomeomorphFixedCodomain_kn n (Classical.choose_spec 
((FiniteDimensional.SeparatingDual 𝕜 E).exists_eq_one (Projectivization.rep_nonzero x))) 

instance ChartedSpacePn :
  ChartedSpace (Fin n → 𝕜) (ℙ 𝕜 E) := 
{
  atlas := {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = Chart1_LocalHomeomorphFixedCodomain_kn n hv}
  chartAt := fun x => Chart1PnAt n x   
  mem_chart_source := fun x => Chart1_LocalHomeomorphFixedCodomain_kn_source n  
    (Classical.choose_spec ((FiniteDimensional.SeparatingDual 𝕜 E).exists_eq_one (Projectivization.rep_nonzero x))) 
  chart_mem_atlas := fun x => by unfold Chart1PnAt; simp only [Set.mem_setOf_eq]
                                 exists Classical.choose ((FiniteDimensional.SeparatingDual 𝕜 E).exists_eq_one 
                                   (Projectivization.rep_nonzero x))
                                 exists x.rep 
                                 exists Classical.choose_spec ((FiniteDimensional.SeparatingDual 𝕜 E).exists_eq_one 
                                   (Projectivization.rep_nonzero x))
}
 
end PnCharts



section ChangeOfCharts

lemma ChangeOfChartFixedCodomain_kn_source {φ ψ : E →L[𝕜] 𝕜} {v w : E} 
(hv : φ v = 1) (hw : ψ w = 1) :
((Chart1_LocalHomeomorphFixedCodomain_kn n hw).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn n hv)).toLocalEquiv.source
= (ClosedHyperplaneToFixedSpace (hdim n) (NonzeroPhiOfPhiEqOne hw)).symm⁻¹'
{u : LinearMap.ker ψ | φ (w + u) ≠ 0} := by 
  ext u 
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.coe_coe_symm, Set.mem_inter_iff, Set.mem_preimage, map_add, ne_eq,
    Set.preimage_setOf_eq, Set.mem_setOf_eq]
  unfold Chart1_LocalHomeomorphFixedCodomain_kn Chart1_LocalHomeomorph Chart1_LocalEquiv
    ClosedHyperplaneToFixedSpace
  simp only [Set.top_eq_univ, LocalHomeomorph.transHomeomorph_target, ContinuousLinearEquiv.symm_toHomeomorph,
    ContinuousLinearEquiv.coe_toHomeomorph, Set.preimage_univ, Set.mem_univ, LocalHomeomorph.transHomeomorph_symm_apply,
    LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, Function.comp_apply, LocalHomeomorph.transHomeomorph_source,
    true_and]
  rw [Chart2_GoodsetPreimage]
  simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, map_add, ne_eq]

lemma ChangeOfChartFixedCodomain_kn_IsSmoothOn {φ ψ : E →L[𝕜] 𝕜} {v w : E} 
(hv : φ v = 1) (hw : ψ w = 1) :
ContDiffOn 𝕜 ⊤ ((Chart1_LocalHomeomorphFixedCodomain_kn n hv).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn n hw))
((Chart1_LocalHomeomorphFixedCodomain_kn n hv).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn n hw)).toLocalEquiv.source := by 
  rw [ChangeOfChartFixedCodomain_kn_source]
  unfold Chart1_LocalHomeomorphFixedCodomain_kn
  apply ContDiffOn.continuousLinearMap_comp
    (ClosedHyperplaneToFixedSpace (hdim n) (NonzeroPhiOfPhiEqOne hw)).toContinuousLinearMap
  simp only [Equiv.toLocalEquiv_source, LocalEquiv.restr_univ, LocalEquiv.symm_symm, LocalHomeomorph.symm_symm,
    LocalHomeomorph.transHomeomorph_source, LocalHomeomorph.symm_toLocalEquiv, LocalHomeomorph.restrOpen_toLocalEquiv,
    LocalEquiv.restr_coe_symm, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
    ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply,
    LocalHomeomorph.toFun_eq_coe, Set.preimage_setOf_eq]
  set f := (ClosedHyperplaneToFixedSpace (hdim n) (NonzeroPhiOfPhiEqOne hv)).symm.toContinuousLinearMap 
  have heq : {a | ψ (v + (f a).1) ≠ 0} = f⁻¹' {b | ψ (v + b.1) ≠ 0} := by
    ext u 
    simp only [ContinuousLinearEquiv.coe_coe, map_add, ne_eq, Set.mem_setOf_eq, Set.preimage_setOf_eq]
  erw [heq]
  change ContDiffOn 𝕜 ⊤ (fun x => (Chart1_LocalHomeomorph hw) ((Chart1_LocalHomeomorph hv).symm
    (f x))) _ 
  change ContDiffOn 𝕜 ⊤ ((Chart1_LocalHomeomorph hw) ∘ (Chart1_LocalHomeomorph hv).symm ∘ f) _
  rw [←Function.comp.assoc] 
  refine ContDiffOn.comp_continuousLinearMap ?_ f
  apply ChangeOfChart'_IsSmoothOn 
  exact hv 

variable (𝕜)
def ModelPn := modelWithCornersSelf 𝕜 (Fin n → 𝕜)
variable {𝕜}

instance Pn_SmoothManifold :
SmoothManifoldWithCorners (ModelPn 𝕜 n) (ℙ 𝕜 E) := 
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ (ModelPn 𝕜 n) (ℙ 𝕜 E) 
_ _
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, v, hv, hev⟩, ⟨ψ, w, hw, he'w⟩ => 
       rw [hev, he'w]
       unfold ModelPn
       simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp.right_id,
         Function.comp.left_id, Set.preimage_id_eq, id_eq, Set.range_id, Set.inter_univ]
       exact ChangeOfChartFixedCodomain_kn_IsSmoothOn n hv hw 
)


section SmoothMaps

/- We prove that the Projectivization.mk' map from Estar to ℙ(E) is smooth. This is useful to construct
smooth maps to ℙ(E).-/


lemma Smooth.quotientMap : 
ContMDiff (modelWithCornersSelf 𝕜 E) (ModelPn 𝕜 n) ⊤ (Projectivization.mk' 𝕜: Estar E → ℙ 𝕜 E) := by sorry
#exit 
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
  


end SmoothMaps 




