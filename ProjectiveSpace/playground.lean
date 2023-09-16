import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Basic

universe u 

variable {E : Type u} [NormedAddCommGroup E] [Nonempty {u : E | u ≠ 0}]

def inj : {u : E | u ≠ 0} → E := fun u => u.1 

example (u : E) (hu : u ≠ 0) (OE : OpenEmbedding inj):
u = (OpenEmbedding.toLocalHomeomorph inj OE).symm u := by 
  have heq : u = inj ⟨u, hu⟩ := by unfold inj; simp only 
  nth_rewrite 2 [heq]
  nth_rewrite 2 [←(OpenEmbedding.toLocalHomeomorph_apply inj OE)]
  rw [LocalHomeomorph.left_inv]
  unfold inj 
  tauto 