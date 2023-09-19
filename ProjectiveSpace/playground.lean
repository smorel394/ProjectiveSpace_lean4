import Mathlib.Tactic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners


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

#synth ChartedSpace E (Estar E) 