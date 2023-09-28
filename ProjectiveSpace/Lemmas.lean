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

lemma LinearMap.graph_fst_injective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
Function.Injective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) := by
  intro ⟨v, hv⟩ ⟨v', hv'⟩ hvv' 
  simp only [Subtype.mk.injEq]
  simp only [domRestrict_apply, fst_apply] at hvv' 
  rw [Prod.ext_iff, and_iff_right hvv']
  rw [LinearMap.mem_graph_iff] at hv hv'
  rw [hv, hv', hvv']

lemma LinearMap.graph_fst_surjective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
Function.Surjective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) := by
  intro v 
  simp only [domRestrict_apply, fst_apply, Subtype.exists, mem_graph_iff, exists_prop, Prod.exists, exists_eq_left,
         exists_eq]

noncomputable def LinearMap.graph_equiv_fst {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M] 
[AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) : LinearMap.graph f ≃ₗ[R] M := 
 LinearEquiv.ofBijective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) 
 ⟨LinearMap.graph_fst_injective f, LinearMap.graph_fst_surjective f⟩