import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.NormedSpace.OperatorNorm



open Classical
noncomputable section 

universe u 


variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

#synth CompleteSpace (E →L[𝕜] E) 

#synth ChartedSpace (E →L[𝕜] E) (E →L[𝕜] E)ˣ 