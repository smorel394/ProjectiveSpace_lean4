import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.NormedSpace.BallAction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.ProjectiveSpace.Independence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Data.ENat.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.LinearAlgebra.Finrank




open Classical
noncomputable section 

universe u 

/-! # If E is k-vector space, then all the closed hyperplanes of E are isomorphic. 
Here we define a closed hyperplane as the kernel of a nonzero continuous linear form.  -/


variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance : Module 𝕜 𝕜 := Semiring.toModule 

/- We first construct the retractions on a closed hyperplane, given as the kernel of
a continuous linear form. -/

 def ContinuousRetractionOnHyperplane_aux (φ : E→L[𝕜] 𝕜) (v : E) : E→L[𝕜]E := 
 (ContinuousLinearMap.id 𝕜 E) - (ContinuousLinearMap.smulRight φ v)


lemma ContinuousRetractionOnHyperplane_image {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : E) :
ContinuousRetractionOnHyperplane_aux φ v u ∈ LinearMap.ker φ := by 
  unfold ContinuousRetractionOnHyperplane_aux
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
  rw [hv, mul_one, sub_self]


def ContinuousRetractionOnHyperplane {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) : 
E→L[𝕜] LinearMap.ker φ := 
ContinuousLinearMap.codRestrict  
(ContinuousRetractionOnHyperplane_aux φ v) (LinearMap.ker φ) 
(ContinuousRetractionOnHyperplane_image hv)

lemma ContinuousRetractionOnHyperplane_apply {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) (u : E) :
ContinuousRetractionOnHyperplane hv u = u - (φ u)•v := by 
  unfold ContinuousRetractionOnHyperplane ContinuousRetractionOnHyperplane_aux 
  simp only [ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.smulRight_apply]
  

lemma ContinuousRetractionIsRetraction {φ : E →L[𝕜] 𝕜} {v : E} (hv : φ v = 1) 
(u : LinearMap.ker φ) : ContinuousRetractionOnHyperplane hv u.1 = u := by 
  unfold ContinuousRetractionOnHyperplane ContinuousRetractionOnHyperplane_aux
  rw [←SetCoe.ext_iff]
  simp only [ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.smulRight_apply, LinearMap.map_coe_ker, zero_smul, sub_zero]
  

lemma GoodChoiceForRetractionOnClosedHyperplane {φ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) : ∃ (v : E), φ v = 1 := by 
  have hnt := Not.imp hφ (@ContinuousLinearMap.ext 𝕜 𝕜  _ _ (RingHom.id 𝕜) E _ _ 𝕜 _ _ _ _ φ 0) 
  push_neg at hnt 
  match hnt with 
  | ⟨w, hw⟩ => 
    set v:=(1/φ w)•w 
    have hv : φ v = 1 := by 
      simp only [one_div, map_smul, smul_eq_mul, ne_eq]
      rw [mul_comm, (DivisionRing.mul_inv_cancel _ hw)]
    existsi v; exact hv 


lemma ClosedHyperplanesIncomparable1 {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) 
(hψ : ψ  ≠ 0) (h: LinearMap.ker φ ≤ LinearMap.ker ψ)  : ∃ (a : 𝕜ˣ), ψ = a•φ := by 
  match (GoodChoiceForRetractionOnClosedHyperplane hφ) with 
  | ⟨v, hv⟩ => 
      have goal : ψ = (ψ v)•φ := by 
        ext w 
        have h1 : φ (w-(φ w)• v) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul]
          rw [hv, mul_one, sub_self]
        have h2 : w - (φ w)•v ∈ LinearMap.ker ψ := by  
          exact h h1 
        have h3 : ψ (w-(φ w)•v) = 0 := h2 
        rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul] at h3  
        rw [eq_of_sub_eq_zero h3]
        simp only [smul_eq_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
        rw [mul_comm]
      have hunit : IsUnit (ψ v) := by 
        refine isUnit_of_mul_eq_one (ψ v) (ψ v)⁻¹ (DivisionRing.mul_inv_cancel _ ?_)
        by_contra habs 
        rw [habs, zero_smul] at goal
        exact hψ goal  
      match hunit with   
      | ⟨a, ha⟩ => 
        existsi a 
        rw [←ha] at goal
        exact goal 


lemma ContinuousLinearMaps_vs_ClosedHyperplanes {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) : 
(LinearMap.ker φ = LinearMap.ker ψ) ↔ (∃ (a : 𝕜ˣ), φ = a•ψ) := by 
  constructor 
  . exact fun h => ClosedHyperplanesIncomparable1 hψ hφ (le_of_eq (Eq.symm h))  
  . intro h 
    match h with 
    | ⟨a, ha⟩ => 
      ext v 
      rw [ha]
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_smul', Pi.smul_apply]
      constructor 
      . intro hzero 
        apply_fun (fun v => a⁻¹ • v) at hzero
        simp only [inv_smul_smul, smul_zero] at hzero  
        exact hzero 
      . exact fun hzero => by rw [hzero, smul_zero]



lemma ClosedHyperplanesIncomparable2 {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) 
(h : LinearMap.ker φ ≠ LinearMap.ker ψ) : 
¬(LinearMap.ker φ ≤ LinearMap.ker ψ) := by
  by_contra habs 
  rw [(ContinuousLinearMaps_vs_ClosedHyperplanes hψ hφ).mpr (ClosedHyperplanesIncomparable1 hφ hψ habs)] at h 
  simp only [ne_eq, not_true] at h  

lemma GoodChoiceForRetractionOnTwoClosedHyperplanes_aux {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ :ψ ≠ 0) 
(h : LinearMap.ker φ ≠ LinearMap.ker ψ) : ∃ (v : E), (φ v = 0) ∧ (ψ v = 1) := by 
  match Set.not_subset.mp (ClosedHyperplanesIncomparable2 hφ hψ h) with
  | ⟨v, hvφ, hvψ⟩ => 
    set w := (ψ v)⁻¹ • v 
    have hwφ : φ w = 0 := by 
      simp only [map_smul, smul_eq_mul, mul_eq_zero, inv_eq_zero]
      exact Or.inr hvφ 
    have hwψ : ψ w = 1 := by 
      simp only [map_smul, smul_eq_mul, ne_eq]
      rw [mul_comm]
      apply DivisionRing.mul_inv_cancel
      exact hvψ
    existsi w 
    exact ⟨hwφ, hwψ⟩ 


lemma GoodChoiceForRetractionOnTwoClosedHyperplanes {φ ψ : E →L[𝕜] 𝕜} 
(hφ : φ ≠ 0) (hψ :ψ ≠ 0) (h : LinearMap.ker φ ≠ LinearMap.ker ψ) : 
∃ v :E, (φ v=1)∧ (ψ  v=1) := by 
  match GoodChoiceForRetractionOnTwoClosedHyperplanes_aux hφ hψ h with
  | ⟨v, hvφ, hvψ⟩ => 
    match GoodChoiceForRetractionOnTwoClosedHyperplanes_aux hψ hφ (Ne.symm h) with
    | ⟨w, hwφ, hwψ⟩ => 
      existsi v + w 
      simp only [map_add, hvφ, hwψ, zero_add, hvψ, hwφ, add_zero, and_self]

def MorphismBetweenTwoClosedHyperplanes (φ : E →L[𝕜] 𝕜) {ψ : E →L[𝕜] 𝕜} {v : E}  (hvψ : ψ v = 1) : 
LinearMap.ker φ →L[𝕜] LinearMap.ker ψ := 
  {
    toFun := Function.comp (ContinuousRetractionOnHyperplane hvψ) (LinearMap.ker φ).subtype 
    map_add' := by simp only [Submodule.coeSubtype, Function.comp_apply, AddSubmonoid.coe_add,
      Submodule.coe_toAddSubmonoid, map_add, Subtype.forall, LinearMap.mem_ker, implies_true, forall_const]
    map_smul' := by simp only [Submodule.coeSubtype, Function.comp_apply, SetLike.val_smul, map_smul, RingHom.id_apply,
      Subtype.forall, LinearMap.mem_ker, implies_true, forall_const]
    cont := by simp only [Submodule.coeSubtype]
               apply Continuous.comp 
               . exact (ContinuousRetractionOnHyperplane hvψ).cont 
               . exact continuous_subtype_val 
  }


lemma MorphismBetweenTwoClosedHyperplanes_apply {φ ψ : E →L[𝕜] 𝕜} {v : E} 
(hvψ : ψ v = 1) (u : LinearMap.ker φ) :
 MorphismBetweenTwoClosedHyperplanes φ hvψ u = ↑u - (ψ u)•v := by 
   unfold MorphismBetweenTwoClosedHyperplanes 
   simp only [Submodule.coeSubtype, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply] 
   rw [ContinuousRetractionOnHyperplane_apply]


lemma MorphismBetweenTwoClosedHyperplanesLeftInverse {φ ψ : E →L[𝕜] 𝕜} {v : E} (hvφ : φ v = 1) (hvψ : ψ v = 1) :
Function.LeftInverse (MorphismBetweenTwoClosedHyperplanes φ hvψ)
(MorphismBetweenTwoClosedHyperplanes ψ hvφ) := by 
  intro u 
  rw [←SetCoe.ext_iff, MorphismBetweenTwoClosedHyperplanes_apply, MorphismBetweenTwoClosedHyperplanes_apply]
  simp only [map_sub, LinearMap.map_coe_ker, map_smul, hvψ, smul_eq_mul, mul_one, zero_sub, neg_smul, sub_neg_eq_add,
    sub_add_cancel]

lemma MorphismBetweenTwoClosedHyperplanes_injective {φ ψ : E →L[𝕜] 𝕜} {v : E} (hvφ : φ v = 1) (hvψ : ψ v = 1) : 
Function.Injective (MorphismBetweenTwoClosedHyperplanes φ hvψ) := 
Function.LeftInverse.injective (MorphismBetweenTwoClosedHyperplanesLeftInverse hvψ hvφ)

lemma MorphismBetweenTwoClosedHyperplanesRightInverse {φ ψ :E →L[𝕜] 𝕜} {v : E} (hvφ : φ v = 1) (hvψ : ψ v = 1) :
Function.RightInverse (MorphismBetweenTwoClosedHyperplanes φ hvψ)
(MorphismBetweenTwoClosedHyperplanes ψ  hvφ) :=
Function.rightInverse_of_injective_of_leftInverse 
  (MorphismBetweenTwoClosedHyperplanes_injective hvφ hvψ)
  (MorphismBetweenTwoClosedHyperplanesLeftInverse hvφ hvψ)


def IsomorphismBetweenTwoClosedHyperplanes {φ ψ :E →L[𝕜] 𝕜} {v : E} (hvφ : φ v = 1) (hvψ : ψ v = 1) : 
LinearMap.ker φ ≃L[𝕜] LinearMap.ker ψ := 
ContinuousLinearEquiv.equivOfInverse 
(MorphismBetweenTwoClosedHyperplanes φ hvψ)
(MorphismBetweenTwoClosedHyperplanes ψ hvφ)
(MorphismBetweenTwoClosedHyperplanesLeftInverse hvψ hvφ)
(MorphismBetweenTwoClosedHyperplanesRightInverse hvψ hvφ)


/- Let's add a choice of isomorphism between any two hyperplanes. -/

def GoodChoiceTwoClosedHyperplanes (φ ψ : E →L[𝕜] 𝕜) : E :=
Classical.epsilon (fun (v : E) => (φ v = 1) ∧ (ψ v = 1))


lemma GoodChoiceTwoClosedHyperplanesIsGood {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) 
(h : LinearMap.ker φ ≠ LinearMap.ker ψ) :
(φ (GoodChoiceTwoClosedHyperplanes φ ψ) = 1) ∧ (ψ (GoodChoiceTwoClosedHyperplanes φ ψ) = 1) :=
Classical.epsilon_spec (GoodChoiceForRetractionOnTwoClosedHyperplanes hφ hψ h)


def IdAsContinuousLinearMapOfHyperplanes {φ ψ : E →L[𝕜] 𝕜} (h : LinearMap.ker φ = LinearMap.ker ψ) :
LinearMap.ker φ →L[𝕜] LinearMap.ker ψ := 
{toFun := fun x => by set hx := x.2; simp_rw [h] at hx; exact ⟨x, hx⟩
 map_add' := by tauto
 map_smul' := by tauto 
 cont := by continuity 
}

def IdAsContinuousLinearEquivOfHyperplanes {φ ψ : E →L[𝕜] 𝕜} (h : LinearMap.ker φ = LinearMap.ker ψ) :
LinearMap.ker φ ≃L[𝕜] LinearMap.ker ψ := by 
  apply ContinuousLinearEquiv.equivOfInverse (IdAsContinuousLinearMapOfHyperplanes h)
    (IdAsContinuousLinearMapOfHyperplanes (Eq.symm h))
  . intro u 
    unfold IdAsContinuousLinearMapOfHyperplanes 
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_eta]
  . intro u 
    unfold IdAsContinuousLinearMapOfHyperplanes 
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_eta]

def OneIsomorphismBetweenTwoClosedHyperplanes_aux {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) 
(h : LinearMap.ker φ ≠ LinearMap.ker ψ): LinearMap.ker φ ≃L[𝕜] LinearMap.ker ψ := 
IsomorphismBetweenTwoClosedHyperplanes (GoodChoiceTwoClosedHyperplanesIsGood hφ hψ h).1
(GoodChoiceTwoClosedHyperplanesIsGood hφ hψ h).2


def OneIsomorphismBetweenTwoClosedHyperplanes {φ ψ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) : 
LinearMap.ker φ ≃L[𝕜] LinearMap.ker ψ :=
dite (LinearMap.ker φ = LinearMap.ker ψ)
(fun h => IdAsContinuousLinearEquivOfHyperplanes h)
(fun h => OneIsomorphismBetweenTwoClosedHyperplanes_aux hφ hψ h)


section NonemptyEstar

/- If FiniteDimensional.finrank E is ≥ 1, then {u : E // u ≠ 0} is nonempty.-/

def NonemptyEstar (hrank : FiniteDimensional.finrank 𝕜 E ≥ 1) : Nonempty {u : E // u ≠ 0} := by
  by_contra habs 
  have hsin : Subsingleton E := by
    apply Subsingleton.intro
    intro u v 
    simp only [ne_eq, nonempty_subtype, not_exists, not_not] at habs 
    rw [habs u, habs v]
  rw [@FiniteDimensional.finrank_zero_of_subsingleton 𝕜 E _ _ _ _ _ hsin] at hrank
  exact not_lt_of_le hrank zero_lt_one 


end NonemptyEstar 



section FiniteDimensional
/- Finite-dimensional case.-/

variable [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

/- Proof that continuous linear forms (= linear forms in this case) separate points.-/

instance FiniteDimensional.SeparatingDual : SeparatingDual 𝕜 E := 
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


/- If FiniteDimensional.finrank E = n + 1, then {u : E // u ≠ 0} is nonempty.-/


def NonemptyEstar' {n : ℕ} [Fact (FiniteDimensional.finrank 𝕜 E = n + 1)] : Nonempty {u : E // u ≠ 0} := by
  have hrank : FiniteDimensional.finrank 𝕜 E = n + 1 := Fact.elim inferInstance 
  have h : FiniteDimensional.finrank 𝕜 E ≥ 1 := by
    rw [hrank]
    simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
  exact NonemptyEstar h   


-- I don't think that this is needed anymore. Commenting.
/-
/- If E is finite-dimensiional of dimension n + 1, we also define an isomorphism between
any closed hyperplane and (Fin n → 𝕜).-/
 
variable (n : ℕ) (hdim : (FiniteDimensional.finrank 𝕜 E = n + 1))


def ClosedHyperplaneToFixedSpace {φ : E →L[𝕜] 𝕜} (hφ : φ ≠ 0) :
LinearMap.ker φ ≃L[𝕜] (Fin n → 𝕜) := by 
  have hrank : FiniteDimensional.finrank 𝕜 (LinearMap.ker φ) = (n : ℕ) := by 
    have hadd := @LinearMap.finrank_range_add_finrank_ker 𝕜 E _ _ _ 𝕜 _ _ _ φ  
    have hsurj : LinearMap.range φ = ⊤ := by 
      rw [LinearMap.range_eq_top]
      have hφ' : (φ : E →ₗ[𝕜] 𝕜) ≠ 0 := by
        by_contra habs 
        have : φ = 0 := ContinuousLinearMap.coe_injective habs 
        exact hφ this
      exact LinearMap.surjective_of_ne_zero hφ'   
    have h : FiniteDimensional.finrank 𝕜 (LinearMap.range φ) = 1 := by 
      rw [hsurj]
      simp only [finrank_top, FiniteDimensional.finrank_self]
    erw [hdim, h] at hadd
    rw [add_comm] at hadd 
    exact Nat.succ_injective hadd   
  have hrankeq : FiniteDimensional.finrank 𝕜 (LinearMap.ker φ) = 
    FiniteDimensional.finrank 𝕜 (Fin n → 𝕜) := by 
    rw [hrank]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact ContinuousLinearEquiv.ofFinrankEq hrankeq    
-/

end FiniteDimensional


end 