import ProjectiveSpace.ProjectiveSpaceGeneral


open Classical
noncomputable section 

universe u 

section SeparatingDual

variable (𝕜 E : Type u) [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

def FiniteDimensional.SeparatingDual : SeparatingDual 𝕜 E := 
{exists_ne_zero' := 
  by intro v hv
     set f : 𝕜 →ₗ[𝕜] Submodule.span 𝕜 {v} := 
       {
        toFun := fun a => ⟨a • v, by rw [Submodule.mem_span_singleton]; existsi a; rfl⟩
        map_add' := by simp only [add_smul, AddSubmonoid.mk_add_mk, forall_const]
        map_smul' := by simp only [smul_eq_mul, RingHom.id_apply, SetLike.mk_smul_mk, smul_smul, forall_const]
       }
     have hsurj : Function.Surjective f := by 
       intro w
       have h := w.2 
       rw [Submodule.mem_span_singleton] at h
       match h with 
       | ⟨a, ha⟩ => 
         existsi a
         rw [←SetCoe.ext_iff, ←ha]
         simp only [LinearMap.coe_mk, AddHom.coe_mk]
     have hinj : Function.Injective f := by 
       intro a b heq
       simp only [LinearMap.coe_mk, AddHom.coe_mk, Subtype.mk.injEq] at heq 
       exact smul_left_injective 𝕜 hv heq 
     set g := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
     match @LinearMap.exists_extend 𝕜 E 𝕜 _ _ _ _ _ (Submodule.span 𝕜 {v}) g.symm with
     | ⟨φ, hφ⟩ => 
       have hval : φ v = 1 := by 
         have h1 : 1 = g.symm ⟨v, Submodule.mem_span_singleton_self v⟩ := by 
           have h : g 1 = ⟨v, Submodule.mem_span_singleton_self v⟩ := by
             simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_mk, AddHom.coe_mk, one_smul]
           rw [←h, ←LinearEquiv.invFun_eq_symm]
           exact Eq.symm (g.left_inv 1)
         have h2 : v = Submodule.subtype (Submodule.span 𝕜 {v}) ⟨v, Submodule.mem_span_singleton_self v⟩ := by
           simp only [Submodule.coeSubtype] 
         rw [h2, ←(@Function.comp_apply _ _ _ φ _ _), h1, ←LinearMap.coe_comp, hφ]
         rfl 
       existsi (LinearMap.toContinuousLinearMap φ)
       simp only [LinearMap.coe_toContinuousLinearMap', hval, ne_eq, one_ne_zero, not_false_eq_true]
} 
end SeparatingDual


variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

variable {n : ℕ}  (hdim : FiniteDimensional.finrank 𝕜 E = n + 1)
  [CompleteSpace 𝕜]

/- The case of projective space of a 𝕜-vector space of dimension n+1.-/
section PnCharts

/- Charts on ℙ 𝕜 E with fixed codomain 𝕜^n.-/


def Chart1_LocalHomeomorphFixedCodomain_kn {φ : E →L[𝕜] 𝕜} {v : E} (hv: φ v = 1) 
 : LocalHomeomorph (ℙ 𝕜 E) (Fin n → 𝕜) :=
LocalHomeomorph.transHomeomorph (Chart1_LocalHomeomorph hv) 
(ContinuousLinearEquiv.toHomeomorph
(ClosedHyperplaneToFixedSpace hdim (NonzeroPhiOfPhiEqOne hv)))


lemma Chart1_LocalHomeomorphFixedCodomain_kn_source {φ : E →L[𝕜] 𝕜} {x : ℙ 𝕜 E} 
(hx: φ x.rep = 1) : 
x ∈ (Chart1_LocalHomeomorphFixedCodomain_kn hdim hx).toLocalEquiv.source := by 
  unfold Chart1_LocalHomeomorphFixedCodomain_kn ClosedHyperplaneToFixedSpace 
  simp only [LocalHomeomorph.transHomeomorph_source]
  change φ x.rep ≠ 0
  rw [hx]
  exact one_ne_zero 

def Chart1PnAt (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (Fin n → 𝕜) :=
Chart1_LocalHomeomorphFixedCodomain_kn hdim (Classical.choose_spec 
((FiniteDimensional.SeparatingDual 𝕜 E).exists_eq_one (Projectivization.rep_nonzero x))) 

def ChartedSpacePn :
  ChartedSpace (Fin n → 𝕜) (ℙ 𝕜 E) := 
{
  atlas := {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = Chart1_LocalHomeomorphFixedCodomain_kn hdim hv}
  chartAt := fun x => Chart1PnAt hdim x   
  mem_chart_source := fun x => Chart1_LocalHomeomorphFixedCodomain_kn_source hdim 
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
((Chart1_LocalHomeomorphFixedCodomain_kn hdim hw).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn hdim hv)).toLocalEquiv.source
= (ClosedHyperplaneToFixedSpace hdim (NonzeroPhiOfPhiEqOne hw)).symm⁻¹'
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
ContDiffOn 𝕜 ⊤ ((Chart1_LocalHomeomorphFixedCodomain_kn hdim hv).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn hdim hw))
((Chart1_LocalHomeomorphFixedCodomain_kn hdim hv).symm.trans
(Chart1_LocalHomeomorphFixedCodomain_kn hdim hw)).toLocalEquiv.source := by 
  rw [ChangeOfChartFixedCodomain_kn_source]
  unfold Chart1_LocalHomeomorphFixedCodomain_kn
  apply ContDiffOn.continuousLinearMap_comp
    (ClosedHyperplaneToFixedSpace hdim (NonzeroPhiOfPhiEqOne hw)).toContinuousLinearMap
  simp only [Equiv.toLocalEquiv_source, LocalEquiv.restr_univ, LocalEquiv.symm_symm, LocalHomeomorph.symm_symm,
    LocalHomeomorph.transHomeomorph_source, LocalHomeomorph.symm_toLocalEquiv, LocalHomeomorph.restrOpen_toLocalEquiv,
    LocalEquiv.restr_coe_symm, LocalHomeomorph.coe_coe_symm, LocalHomeomorph.transHomeomorph_symm_apply,
    ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply,
    LocalHomeomorph.toFun_eq_coe, Set.preimage_setOf_eq]
  set f := (ClosedHyperplaneToFixedSpace hdim (NonzeroPhiOfPhiEqOne hv)).symm.toContinuousLinearMap 
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

def ModelPn := modelWithCornersSelf 𝕜 (Fin n → 𝕜)


def Pn_SmoothManifold :
@SmoothManifoldWithCorners _ _ _ _ _ _ _ ModelPn (ℙ 𝕜 E) _ (ChartedSpacePn hdim) :=
@smoothManifoldWithCorners_of_contDiffOn _ _ _ _ _ _ _ ModelPn (ℙ 𝕜 E) 
_ (ChartedSpacePn hdim) 
(
  by intro e e' he he'
     match he, he' with 
     | ⟨φ, v, hv, hev⟩, ⟨ψ, w, hw, he'w⟩ => 
       rw [hev, he'w]
       unfold ModelPn
       simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp.right_id,
         Function.comp.left_id, Set.preimage_id_eq, id_eq, Set.range_id, Set.inter_univ]
       exact ChangeOfChartFixedCodomain_kn_IsSmoothOn hdim hv hw 
)



end ChangeOfCharts





