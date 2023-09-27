import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.NormedSpace.OperatorNorm



open Classical
noncomputable section 

universe u 

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

example (v : E) (hv : v ≠ 0) : ∃ (φ : E →ₗ[𝕜] 𝕜), φ v ≠ 0 := by
  library_search 