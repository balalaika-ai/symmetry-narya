export "37-two-element-sets"

def native_mere_equiv (A B : Type) (e : Equiv A B) : Equiv (Mere A) (Mere B)
  ≔ iff_equiv (Mere A) (Mere B) (mere_isprop A) (mere_isprop B)
      (trunc_map native_truncation A B (e .map))
      (trunc_map native_truncation B A (equiv_inverse_map A B e))

{` The inclusion of a subtype induces an equivalence on each inhabited component. `}
def component_subtype_to (A : Type) (B : A → Type) (u : Σ A B)
  (c : NativeComponent (Σ A B) u) : NativeComponent A (u .fst)
  ≔ (c .fst .fst, trunc_map native_truncation (Id (Σ A B) u (c .fst))
      (Id A (u .fst) (c .fst .fst)) (p ↦ p .fst) (c .snd))

def component_subtype_from (A : Type) (B : A → Type) (hb : (a : A) → isProp (B a))
  (u : Σ A B) (c : NativeComponent A (u .fst)) : NativeComponent (Σ A B) u
  ≔ let b ≔ mere_transport native_truncation A B hb (u .fst) (c .fst) (c .snd) (u .snd) in
    ((c .fst, b), trunc_map native_truncation (Id A (u .fst) (c .fst))
      (Id (Σ A B) u (c .fst, b)) (subtype_equal A B hb u (c .fst, b)) (c .snd))

def component_subtype_equiv (A : Type) (B : A → Type) (hb : (a : A) → isProp (B a))
  (u : Σ A B) : Equiv (NativeComponent (Σ A B) u) (NativeComponent A (u .fst))
  ≔ quasi_inverse_equiv (NativeComponent (Σ A B) u) (NativeComponent A (u .fst))
      (component_subtype_to A B u) (component_subtype_from A B hb u)
      (c ↦ subtype_equal (Σ A B) (v ↦ Mere (Id (Σ A B) u v))
        (v ↦ mere_isprop (Id (Σ A B) u v))
        (component_subtype_from A B hb u (component_subtype_to A B u c)) c
        (subtype_equal A B hb
          (component_subtype_from A B hb u (component_subtype_to A B u c) .fst) (c .fst)
          (refl (c .fst .fst))))
      (c ↦ subtype_equal A (a ↦ Mere (Id A (u .fst) a)) (a ↦ mere_isprop (Id A (u .fst) a))
        (component_subtype_to A B u (component_subtype_from A B hb u c)) c (refl (c .fst)))

def finite_sets_at_set_component (n : Nat)
  : Equiv (FiniteSetsAt n) (NativeComponent SetTypes (Fin n, fin_set n))
  ≔ family_equiv SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst)))
      (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S))
      (S ↦ native_mere_equiv (Id Type (Fin n) (S .fst)) (Id SetTypes (Fin n, fin_set n) S)
        (canonical_inverse_equiv (Id SetTypes (Fin n, fin_set n) S) (Id Type (Fin n) (S .fst))
          (subtype_path_equiv Type isSet isset_isprop (Fin n, fin_set n) S)))

def finite_sets_at_universe_component (n : Nat)
  : Equiv (FiniteSetsAt n) (NativeComponent Type (Fin n))
  ≔ compose_equiv (FiniteSetsAt n) (NativeComponent SetTypes (Fin n, fin_set n))
      (NativeComponent Type (Fin n)) (finite_sets_at_set_component n)
      (component_subtype_equiv Type isSet isset_isprop (Fin n, fin_set n))

def finite_sets_at_finite_component (n : Nat)
  : Equiv (FiniteSetsAt n) (NativeComponent FiniteSets (standard_finite_set n))
  ≔ compose_equiv (FiniteSetsAt n) (NativeComponent SetTypes (Fin n, fin_set n))
      (NativeComponent FiniteSets (standard_finite_set n)) (finite_sets_at_set_component n)
      (canonical_inverse_equiv (NativeComponent FiniteSets (standard_finite_set n))
        (NativeComponent SetTypes (Fin n, fin_set n))
        (component_subtype_equiv SetTypes (S ↦ IsFinite (S .fst)) (S ↦ isfinite_prop (S .fst))
          (standard_finite_set n)))

{` First footnote of def:groupoidFin: summing over sets or over types. `}
def finite_sets_forget_sethood : FiniteSets → Σ Type IsFinite
  ≔ S ↦ (S .fst .fst, S .snd)

def finite_sets_add_sethood : Σ Type IsFinite → FiniteSets
  ≔ S ↦ ((S .fst, finite_sethood (S .fst) (S .snd)), S .snd)

def finite_sets_universe_equiv : Equiv FiniteSets (Σ Type IsFinite)
  ≔ quasi_inverse_equiv FiniteSets (Σ Type IsFinite)
      finite_sets_forget_sethood finite_sets_add_sethood
      (S ↦ subtype_equal SetTypes (X ↦ IsFinite (X .fst)) (X ↦ isfinite_prop (X .fst))
        (finite_sets_add_sethood (finite_sets_forget_sethood S)) S
        (subtype_equal Type isSet isset_isprop (S .fst .fst, finite_sethood (S .fst .fst) (S .snd))
          (S .fst) (refl (S .fst .fst)))) (S ↦ refl S)

def proposition_component_member (P : Type) (hp : isProp P) (c : NativeComponent Type P)
  : isProp (c .fst)
  ≔ mere_transport native_truncation Type isProp isprop_isprop P (c .fst) (c .snd) hp

def proposition_universe_component_contractible (P : Type) (hp : isProp P)
  : isContr (NativeComponent Type P)
  ≔ ((P, mere (Id Type P P) (refl P)), c ↦
      subtype_equal Type (X ↦ Mere (Id Type P X)) (X ↦ mere_isprop (Id Type P X))
        c (P, mere (Id Type P P) (refl P))
        (inverse Type P (c .fst)
          (mere_rec (Id Type P (c .fst)) (Id Type P (c .fst))
            (proposition_type_paths_prop P (c .fst) (proposition_component_member P hp c))
            (identity (Id Type P (c .fst))) (c .snd))))

def contractible_domain_of_equiv (A B : Type) (e : Equiv A B) (hb : isContr B) : isContr A
  ≔ contractible_retract B A hb (equiv_inverse_map A B e) (e .map) (equiv_retraction A B e)

def finite_sets_zero_contractible : isContr (FiniteSetsAt zero.)
  ≔ contractible_domain_of_equiv (FiniteSetsAt zero.) (NativeComponent Type Empty)
      (finite_sets_at_universe_component zero.) (proposition_universe_component_contractible Empty empty_prop)

def finite_sets_one_contractible : isContr (FiniteSetsAt (suc. zero.))
  ≔ contractible_domain_of_equiv (FiniteSetsAt (suc. zero.)) (NativeComponent Type (Fin (suc. zero.)))
      (finite_sets_at_universe_component (suc. zero.))
      (proposition_universe_component_contractible (Fin (suc. zero.))
        (contractible_prop (Fin (suc. zero.))
          (contractible_domain_of_equiv (Fin (suc. zero.)) Unit fin_one_equiv unit_contractible)))

def contractible_unit_equiv (A : Type) (ha : isContr A) : Equiv A Unit
  ≔ quasi_inverse_equiv A Unit (_ ↦ star.) (_ ↦ ha .center)
      (a ↦ inverse A a (ha .center) (ha .contract a)) (unit_prop star.)

{` The unnumbered identifications following def:groupoidFin. `}
def finite_sets_zero_one_path : Id Type (FiniteSetsAt zero.) (FiniteSetsAt (suc. zero.))
  ≔ ua (FiniteSetsAt zero.) (FiniteSetsAt (suc. zero.))
      (compose_equiv (FiniteSetsAt zero.) Unit (FiniteSetsAt (suc. zero.))
        (contractible_unit_equiv (FiniteSetsAt zero.) finite_sets_zero_contractible)
        (canonical_inverse_equiv (FiniteSetsAt (suc. zero.)) Unit
          (contractible_unit_equiv (FiniteSetsAt (suc. zero.)) finite_sets_one_contractible)))

def finite_sets_one_unit_path : Id Type (FiniteSetsAt (suc. zero.)) (Fin (suc. zero.))
  ≔ ua (FiniteSetsAt (suc. zero.)) (Fin (suc. zero.))
      (compose_equiv (FiniteSetsAt (suc. zero.)) Unit (Fin (suc. zero.))
        (contractible_unit_equiv (FiniteSetsAt (suc. zero.)) finite_sets_one_contractible)
        (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv))
