import ProjectiveSpace.ProjectiveSpaceGeneral

open Classical
noncomputable section 

universe u 


variable (𝕜 E : Type u) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜]


/- To define the charted space structure, we want local homeomorphisms into a fixed model space. 
So we need to fix a nonzero continuous linear form on E and to use its kernel. It is isomorphic 
to every other closed hyperplane by OneIsomorphismBetweenClosedHyperplanes. But we don't want to
have that linear form as a parameter in our instance, so we will use a choice function to pick it,
after we put a Nonempty instance on E-{0} and a SeperatingDual instance on E. We need the
SeparatingDual instance anyway to prove that every point of ℙ(E) is in the domain of a chart.-/

variable [Nonempty {u : E // u ≠ 0}] [SeparatingDual 𝕜 E]


lemma ExistsNonzeroContinuousLinearForm : ∃ (χ : E →L[𝕜] 𝕜), χ ≠ 0 := by 
  set v : {u : E // u ≠ 0} := Classical.choice inferInstance 
  existsi Classical.choose (SeparatingDual.exists_ne_zero v.2)
  by_contra habs 
  apply_fun (fun φ => φ v.1) at habs 
  simp only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf, ContinuousLinearMap.zero_apply] at habs  
  exact Classical.choose_spec (SeparatingDual.exists_ne_zero v.2) habs 

abbrev Chi : (E →L[𝕜] 𝕜) := Classical.choose (ExistsNonzeroContinuousLinearForm 𝕜 E)


abbrev hChi := Classical.choose_spec (ExistsNonzeroContinuousLinearForm 𝕜 E)


namespace ProjectiveSpace

variable {𝕜 E}


section ChartedSpace 

/- Chart at x ∈ ℙ(E). First with varying codomain, then with fixed codomain.-/

abbrev PhiForChart (x : ℙ 𝕜 E) : (E →L[𝕜] 𝕜) := Classical.choose (SeparatingDual.exists_eq_one
(Projectivization.rep_nonzero x))

abbrev PhiForChart_prop (x : ℙ 𝕜 E) : PhiForChart x x.rep = 1 := Classical.choose_spec (SeparatingDual.exists_eq_one
(Projectivization.rep_nonzero x))


def ProjectiveSpace.ChartAt_aux (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker (PhiForChart x)) := 
Chart_LocalHomeomorph (PhiForChart_prop x)


def ProjectiveSpace.ChartAt (x : ℙ 𝕜 E) :
LocalHomeomorph (ℙ 𝕜 E) (LinearMap.ker (Chi 𝕜 E)) := 
LocalHomeomorph.transHomeomorph (ChartAt_aux x)
(ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne (PhiForChart_prop x)) (hChi 𝕜 E)))


lemma ProjectiveSpace.ChartAt_source (x : ℙ 𝕜 E) :
(ProjectiveSpace.ChartAt x).source = Goodset (PhiForChart x) := by
  unfold ProjectiveSpace.ChartAt ProjectiveSpace.ChartAt_aux Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [Set.top_eq_univ, LocalHomeomorph.transHomeomorph_source]


lemma ProjectiveSpace.Chart_source {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) :
(LocalHomeomorph.transHomeomorph 
    (Chart_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
    (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) hχ))).source = 
  Goodset φ := by 
  unfold Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [Set.top_eq_univ, LocalHomeomorph.transHomeomorph_source]


lemma Chart_LocalHomeomorphFixedCodomain_source {φ : E →L[𝕜] 𝕜} {x : ℙ 𝕜 E} 
(hx: φ x.rep = 1) : 
x ∈ (LocalHomeomorph.transHomeomorph (Chart_LocalHomeomorph hx) 
(ContinuousLinearEquiv.toHomeomorph
(OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hx) hχ))).toLocalEquiv.source := by 
  simp only [LocalHomeomorph.transHomeomorph_source]
  change φ x.rep ≠ 0
  rw [hx]
  exact one_ne_zero 


instance instChartedSpaceProjectiveSpace : ChartedSpace (LinearMap.ker (Chi 𝕜 E)) (ℙ 𝕜 E) := 
{
  atlas := {f | ∃ (φ : E →L[𝕜] 𝕜) (v : E) (hv : φ v = 1), f = LocalHomeomorph.transHomeomorph 
    (Chart_LocalHomeomorph hv) (ContinuousLinearEquiv.toHomeomorph
    (OneIsomorphismBetweenTwoClosedHyperplanes (NonzeroPhiOfPhiEqOne hv) (hChi 𝕜 E)))}
  chartAt := fun x => ProjectiveSpace.ChartAt x  
  mem_chart_source := fun x => Chart_LocalHomeomorphFixedCodomain_source (PhiForChart_prop x)
  chart_mem_atlas := fun x => by unfold ProjectiveSpace.ChartAt; simp only [Set.mem_setOf_eq]
                                 exists PhiForChart x 
                                 exists x.rep 
                                 exists PhiForChart_prop x
}

end ChartedSpace 


/- We can finally define the manifold structure on ℙ(E).-/

section Manifold

/- The model is the kernel of the fixed continuous linear form.-/
variable (𝕜 E)
def ModelHyperplane := modelWithCornersSelf 𝕜 (LinearMap.ker (Chi 𝕜 E)) 

variable {𝕜 E}

instance SmoothManifold : SmoothManifoldWithCorners (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) :=
smoothManifoldWithCorners_of_contDiffOn (ModelHyperplane 𝕜 E) (ℙ 𝕜 E) 
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
       exact ChangeOfChart_IsSmoothOn (hChi 𝕜 E) hw hv 
)

end Manifold

end ProjectiveSpace
