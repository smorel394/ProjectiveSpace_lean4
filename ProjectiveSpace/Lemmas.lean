import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis


lemma Basis.constr_ker {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M' : Type u_7} [Semiring R] 
[AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] (b : Basis ι R M) (S : Type u_10) 
[Semiring S] [Module S M'] [SMulCommClass R S M'] {v : ι → M'} (hv : LinearIndependent R v) :
LinearMap.ker (Basis.constr b S v) = ⊥ := by
  ext u
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor 
  . intro h
    rw [Basis.constr_apply] at h 
    change LinearMap.ker _ = ⊥  at hv 
    rw [←Finsupp.total_apply, ←LinearMap.mem_ker, hv] at h
    simp only [Submodule.mem_bot, AddEquivClass.map_eq_zero_iff] at h  
    exact h 
  . exact fun h => by simp only [h, map_zero]

