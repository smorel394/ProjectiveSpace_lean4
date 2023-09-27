import Mathlib.Tactic 
import ProjectiveSpace.Lemmas 
import Mathlib.LinearAlgebra.FiniteDimensional 
import Mathlib.Algebra.Module.Projective


noncomputable section 

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
(r : ℕ)

/- First definition of the Grassmannian, as the set of sub-vector spaces of V of
dimension r.-/

def Grassmannian := 
{W : Submodule K V | FiniteDimensional K W ∧ FiniteDimensional.finrank K W = r}

/- Second definition of the Grassmannian, as a quotient.-/



/-- The setoid whose quotient is the projectivization of `V`. -/
def grassmannianSetoid : Setoid { v : Fin r → V // LinearIndependent K v} := 
Setoid.comap (fun v => Submodule.span K (Set.range v.1)) 
⟨(· = ·), eq_equivalence⟩ 

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
def QGrassmannian := Quotient (grassmannianSetoid K V r)

variable {V r}

/-- Construct an element of the projectivization from a nonzero vector. -/
def QGrassmannian.mk (v : Fin r → V) (hv : LinearIndependent K v) : QGrassmannian K V r :=
  Quotient.mk'' ⟨v, hv⟩


/-- A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def QGrassmannian.mk' (v : { v : Fin r → V // LinearIndependent K v }) : QGrassmannian K V r :=
  Quotient.mk'' v

@[simp]
theorem QGrassmannian.mk'_eq_mk (v : { v : Fin r → V // LinearIndependent K v}) : 
QGrassmannian.mk' K v = QGrassmannian.mk K v.1 v.2 := rfl

/-- Choose a representative of `v : Projectivization K V` in `V`. -/
protected noncomputable def QGrassmannian.rep (x : QGrassmannian K V r) : Fin r → V :=
  x.out' 


theorem QGrassmannian.rep_linearIndependent (x : QGrassmannian K V r) : 
LinearIndependent K x.rep  :=
  x.out'.2

@[simp]
theorem QGrassmannian.mk_rep (x : QGrassmannian K V r) : 
QGrassmannian.mk K x.rep x.rep_linearIndependent = x := Quotient.out_eq' _

lemma QGrassmannian.mk_eq_mk_iff_span (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ 
Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by 
  unfold QGrassmannian.mk
  change (Setoid.ker (@Quotient.mk'' _ (grassmannianSetoid K V r))).r _ _  ↔ _ 
  rw [Setoid.ker_mk_eq]
  unfold grassmannianSetoid 
  change Submodule.span K (Set.range v) = _ ↔ _ 
  simp only


def MatrixAction (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) : Fin r -> V := 
  (Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun 
    ((Basis.constr (Pi.basisFun K (Fin r)) ℤ  v).comp f)

lemma MatrixAction_vs_comp (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v w : Fin r → V) :
v = MatrixAction K f w ↔ Basis.constr (Pi.basisFun K (Fin r)) ℤ v = 
  (Basis.constr (Pi.basisFun K (Fin r)) ℤ w).comp f := by 
  unfold MatrixAction
  constructor 
  . intro h 
    rw [h]
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply]
  . intro h 
    apply_fun (Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun at h 
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply] at h 
    exact h 
    

lemma MatrixAction_id (v : Fin r → V) : MatrixAction K LinearMap.id v = v := by
  unfold MatrixAction
  simp only [LinearMap.comp_id, LinearEquiv.invFun_eq_symm, LinearEquiv.symm_apply_apply]

lemma MatrixAction_mul (f g : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) :
MatrixAction K (f.comp g) v = MatrixAction K g (MatrixAction K f v) := by 
  unfold MatrixAction
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
  apply LinearMap.comp_assoc 

def MatrixAction_inv (f : (Fin r → K) ≃ₗ[K] (Fin r → K)) (v w : Fin r → V) : 
w = MatrixAction K f v ↔ v = MatrixAction K f.symm w := by
  constructor 
  . intro h 
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]
  . intro h 
    rw [h, ←MatrixAction_mul]
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap]
    rw [MatrixAction_id]


lemma MatrixAction_apply (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) (i : Fin r) :
MatrixAction K f v i = Finset.sum ⊤ (fun j => (f (Pi.basisFun K (Fin r) i) j) • v j) := by
  unfold MatrixAction
  conv => lhs
          rw [←(Basis.constr_basis (Pi.basisFun K (Fin r)) ℤ 
            ((Basis.constr (M' := V) (Pi.basisFun K (Fin r)) ℤ).invFun 
            ((Basis.constr (Pi.basisFun K (Fin r)) ℤ  v).comp f)) i)]
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply, Pi.basisFun_apply, LinearMap.coe_comp,
    Function.comp_apply, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply, Finset.top_eq_univ]
  

lemma MatrixAction_span (f : (Fin r → K) →ₗ[K] (Fin r → K)) (v : Fin r → V) :
Submodule.span K (Set.range (MatrixAction K f v)) ≤ Submodule.span K (Set.range v) := by 
  rw [Submodule.span_le]
  intro u 
  simp only [Set.mem_range, SetLike.mem_coe, forall_exists_index]
  intro i heq
  rw [←heq, MatrixAction_apply]
  apply Submodule.sum_mem
  intro j _ 
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simp only [Set.mem_range, exists_apply_eq_apply]


lemma MatrixAction_vs_SubmoduleSpan (v w : Fin r → V) :
Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w) ↔
∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), v = MatrixAction K f w := by
  constructor 
  . intro h 
    set f := Basis.constr (Pi.basisFun K (Fin r)) ℤ v with hfdef
    set g := Basis.constr (Pi.basisFun K (Fin r)) ℤ w with hgdef
    have hsub : LinearMap.range f ≤ LinearMap.range g := by 
      rw [Basis.constr_range, Basis.constr_range]
      exact h
    set f' := f.codRestrict (LinearMap.range g) 
      (by intro u; apply hsub; simp only [Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
        LinearMap.mem_range, exists_apply_eq_apply])
    set g' := g.rangeRestrict
    have hsur : Function.Surjective g' := by rw [←LinearMap.range_eq_top]; apply LinearMap.range_rangeRestrict
    obtain ⟨h, prop⟩ := Module.projective_lifting_property g' f' hsur 
    existsi h
    simp_rw [MatrixAction_vs_comp]
    rw [←hfdef, ←hgdef]
    have heq : g = (Submodule.subtype (LinearMap.range g)).comp g' := by 
      simp only [LinearMap.subtype_comp_codRestrict]
    rw [heq, LinearMap.comp_assoc, prop]
    simp only [LinearMap.subtype_comp_codRestrict]
  . intro h 
    obtain ⟨f, hf⟩ := h 
    rw [hf]
    apply MatrixAction_span 


lemma MatrixAction_uniqueness {v : Fin r → V} (hv : LinearIndependent K v)
(f g : (Fin r → K) →ₗ[K] (Fin r → K)) (heq : MatrixAction K f v = MatrixAction K g v) :
f = g := by 
  unfold MatrixAction at heq 
  apply_fun (fun h => (Basis.constr (Pi.basisFun K (Fin r)) ℤ) h) at heq
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.apply_symm_apply] at heq
  have hinj : Function.Injective (Basis.constr (Pi.basisFun K (Fin r)) ℤ v) := by 
    rw [←LinearMap.ker_eq_bot]
    apply Basis.constr_ker 
    exact hv 
  apply LinearMap.ext 
  intro u 
  apply_fun (fun h => h u) at heq
  simp only [LinearMap.coe_comp, Function.comp_apply] at heq
  exact hinj heq   




lemma QGrassmannian.mk_eq_mk_iff_matrixAction (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_span]
  constructor 
  . intro heq 
    obtain ⟨f, hf⟩ := (MatrixAction_vs_SubmoduleSpan K v w).mp (le_of_eq heq)
    obtain ⟨g, hg⟩ := (MatrixAction_vs_SubmoduleSpan K w v).mp (le_of_eq (Eq.symm heq))
    have hgf : LinearMap.comp g f = LinearMap.id := by 
      rw [hg, ←MatrixAction_mul] at hf
      conv at hf => lhs
                    rw [←(MatrixAction_id K v)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hv _ _ hf 
    have hfg : LinearMap.comp f g = LinearMap.id := by 
      rw [hf, ←MatrixAction_mul] at hg 
      conv at hg => lhs
                    rw [←(MatrixAction_id K w)]
      apply Eq.symm
      exact MatrixAction_uniqueness K hw _ _ hg 
    existsi LinearEquiv.ofLinear g f hgf hfg 
    exact hg
  . intro h 
    obtain ⟨f, hf⟩ := h
    apply le_antisymm
    . have heq : v = MatrixAction K f.symm.toLinearMap w := by 
        rw [MatrixAction_inv] at hf 
        exact hf 
      rw [heq]
      apply MatrixAction_span 
    . rw [hf]
      apply MatrixAction_span 

lemma QGrassmannian.mk_eq_mk_iff_matrixAction' (v w : Fin r → V) (hv : LinearIndependent K v)
(hw : LinearIndependent K w) :
QGrassmannian.mk K v hv = QGrassmannian.mk K w hw ↔ ∃ (f : (Fin r → K) →ₗ[K] (Fin r → K)), 
w = MatrixAction K f v := by
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction]
  constructor 
  . exact fun h => by obtain ⟨f, hf⟩ := h; existsi f.toLinearMap; exact hf 
  . intro h 
    obtain ⟨f, hf⟩ := h
    have hf' := hf 
    rw [MatrixAction_vs_comp] at hf
    apply_fun (fun f => f.toFun) at hf 
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp] at hf  
    have hinj : Function.Injective f := by
      apply Function.Injective.of_comp (f := (Basis.constr (Pi.basisFun K (Fin r)) ℤ) v)
      rw [←hf, ←LinearMap.ker_eq_bot]
      apply Basis.constr_ker
      exact hw  
    existsi LinearEquiv.ofInjectiveEndo f hinj 
    exact hf' 

lemma QGrassmannian.exists_matrixAction_eq_mk_rep (v : Fin r → V) (hv : LinearIndependent K v) :
∃ (f : (Fin r → K) ≃ₗ[K] (Fin r → K)), MatrixAction K f v = QGrassmannian.rep K (QGrassmannian.mk K v hv) := by
  have heq := Eq.symm (QGrassmannian.mk_rep K (QGrassmannian.mk K v hv))
  rw [QGrassmannian.mk_eq_mk_iff_matrixAction] at heq 
  obtain ⟨f, hf⟩ := heq 
  existsi f 
  exact Eq.symm hf 

variable {K}

/-- An induction principle for `QGrassmannian`.
Use as `induction v using QGrassmannian.ind`. -/
@[elab_as_elim]
lemma QGrassmannian.ind {P : QGrassmannian K V r → Prop} (h : ∀ (v : Fin r → V) (h : LinearIndependent K v), 
P (QGrassmannian.mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h


/-- Consider an element of the QGrassmannian as a submodule of `V`. -/
protected def QGrassmannian.submodule (x : QGrassmannian K V r) : Submodule K V :=
  (Quotient.liftOn' x fun v => Submodule.span K (Set.range v.1)) <| by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    exact hvw 

@[simp]
lemma QGrassmannian.submodule_mk (v : Fin r → V) (hv : LinearIndependent K v) : 
(QGrassmannian.mk K v hv).submodule = Submodule.span K (Set.range v) := rfl 

lemma QGrassmannian.submodule_eq (x : QGrassmannian K V r) : x.submodule = Submodule.span K (Set.range x.rep) := by 
  conv_lhs => rw [← x.mk_rep]

instance QGrassmannian.finiteDimensional_submodule (x : QGrassmannian K V r) : FiniteDimensional K x.submodule := by 
  rw [QGrassmannian.submodule_eq]
  apply FiniteDimensional.span_of_finite 
  apply Set.finite_range 

lemma QGrassmannian.finrank_submodule (x : QGrassmannian K V r) : FiniteDimensional.finrank K x.submodule = r := by 
  rw [QGrassmannian.submodule_eq]
  rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent K x)]
  simp only [Fintype.card_fin]


    

variable (K)



/- Comparison of the two definitions.-/

variable (V r)

-- This could probably be optimized now we have QGrassmannian.submodule and its associated lemmas.
def QGrassmannianToGrassmannian : QGrassmannian K V r → Grassmannian K V r := 
fun x => ⟨QGrassmannian.submodule x, ⟨QGrassmannian.finiteDimensional_submodule x, QGrassmannian.finrank_submodule x⟩⟩

lemma QGrassmannianToGrassmannian_apply' {v : Fin r → V} (hv : LinearIndependent K v) :
(QGrassmannianToGrassmannian K V r (QGrassmannian.mk K v hv)).1 = Submodule.span K (Set.range v) := by 
  unfold QGrassmannianToGrassmannian QGrassmannian.mk 
  simp only
  apply QGrassmannian.submodule_mk 


lemma QGrassmannianToGrassmannian_apply (x : QGrassmannian K V r) :
QGrassmannianToGrassmannian K V r x = ⟨Submodule.span K (Set.range x.rep),
⟨FiniteDimensional.span_of_finite K (Set.finite_range x.rep), 
by rw [finrank_span_eq_card (QGrassmannian.rep_linearIndependent K x)]; simp only [Fintype.card_fin]⟩⟩ := by
  conv => lhs 
          rw [←(QGrassmannian.mk_rep K x)]
  --rw [QGrassmannianToGrassmannian_apply']
  

def GrassmannianToQGrassmannian : Grassmannian K V r → QGrassmannian K V r := by 
  intro ⟨W, hW⟩
  haveI := hW.1 
  set B := FiniteDimensional.finBasisOfFinrankEq K W hW.2 
  refine QGrassmannian.mk K ((Submodule.subtype W) ∘ (FunLike.coe B)) ?_ 
  apply LinearIndependent.map' (Basis.linearIndependent B) _ (Submodule.ker_subtype W)


lemma QGrassmannianToGrassmannianToQGrassmannian (x : QGrassmannian K V r) :
GrassmannianToQGrassmannian K V r (QGrassmannianToGrassmannian K V r x) = x := by
  rw [QGrassmannianToGrassmannian_apply]
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  conv => rhs 
          rw [←(QGrassmannian.mk_rep K x)]
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [Set.range_comp]
  conv => lhs
          erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]  

lemma GrassmannianToQGrassmannianToGrassmannian (W : Grassmannian K V r) :
QGrassmannianToGrassmannian K V r (GrassmannianToQGrassmannian K V r W) = W := by
  unfold GrassmannianToQGrassmannian
  simp only [Submodule.coeSubtype]
  rw [←SetCoe.ext_iff, QGrassmannianToGrassmannian_apply', Set.range_comp]
  erw [←(LinearMap.map_span (Submodule.subtype _))]
  simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  

variable {K V}
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- An injective semilinear map of vector spaces induces a map on QGrassmannians. -/
-- Less general than the version for projective spaces because LinearIndependent.map' requires the two rings to be equal.
def QGrassmannian.map (f : V →ₗ[K] W) (hf : Function.Injective f) : QGrassmannian K V r → QGrassmannian K W r :=
  Quotient.map' (fun v => ⟨f ∘ v.1, by simp only; rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' v.2 f hf⟩)
    (by rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
        change Submodule.span K _ = _ at hvw
        change Submodule.span K _ = _
        simp only at hvw ⊢ 
        rw [Set.range_comp, Set.range_comp]
        rw [←LinearMap.map_span, ←LinearMap.map_span]
        rw [hvw])

lemma QGrassmannian.map_mk (f : V →ₗ[K] W) (hf : Function.Injective f) (v : Fin r → V) (hv : LinearIndependent K v) :
    QGrassmannian.map r f hf (mk K v hv) = QGrassmannian.mk K (f ∘ v) 
    (by rw [←LinearMap.ker_eq_bot] at hf; exact LinearIndependent.map' hv f hf) := rfl

/-- The map we have defined is injective. -/
theorem QGrassmannian.map_injective (f : V →ₗ[K] W) (hf : Function.Injective f) : 
Function.Injective (QGrassmannian.map r f hf) := by 
  intro x y hxy 
  induction' x using QGrassmannian.ind with v hv  
  induction' y using QGrassmannian.ind with w hw 
  rw [QGrassmannian.mk_eq_mk_iff_span]
  rw [QGrassmannian.map_mk, QGrassmannian.map_mk, QGrassmannian.mk_eq_mk_iff_span, Set.range_comp, Set.range_comp,
    ←LinearMap.map_span, ←LinearMap.map_span] at hxy 
  apply_fun (fun p => SetLike.coe p) at hxy 
  rw [Submodule.map_coe, Submodule.map_coe] at hxy  
  apply SetLike.coe_injective'  
  exact Function.Injective.image_injective hf hxy 

@[simp]
lemma QGrassmannian.map_id : QGrassmannian.map r (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl


lemma QGrassmannian.map_comp {U : Type*} [AddCommGroup U] [Module K U] (f : V →ₗ[K] W) (hf : Function.Injective f)
    (g : W →ₗ[K] U) (hg : Function.Injective g) :
    QGrassmannian.map r (g.comp f) (hg.comp hf) = QGrassmannian.map r g hg ∘ QGrassmannian.map r f hf := by 
  ext ⟨v⟩
  rfl 


-- TODO : comparison with ℙ if r = 1; define an Equiv between QGrass and Grass


  