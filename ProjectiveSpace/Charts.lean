import Mathlib.Tactic
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic

open Classical
noncomputable section 

universe u 

variable {𝕜 E : Type u} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] 