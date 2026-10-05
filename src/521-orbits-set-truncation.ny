export "520-orbit-relations"

{` Chapter 5, sec:fixpts-orbits: the set of orbits as a quotient.
   lem:X/G=setTruncX_hG (X/G with [-]_0 is uniquely the set truncation of
   X_hG, also as an identification in Σ_{S:Set}(X_hG → S)), cor:orbit-equiv
   ([-] factors uniquely through the quotient of X(sh_G) by ∃_g (g · x = y)),
   rem:SubGX=Sub(X/G) and xca:transX-just1orbit. `}

{` A surjection f : A → B into a set whose identifications f x = f y are
   logically equivalent to an equivalence relation R factors uniquely
   through A/R by an equivalence (the pattern of rem:set-trunc-as-quotient
   and xca:map-induces-quotient used for both orbit maps). `}
def surjection_quotient_reflects (A B : Type) (hb : isSet B) (R : EquivalenceRelation A) (f : A → B)
  (resp : Respects A B R f) (back : (x y : A) → Id B (f x) (f y) → Rel A R x y)
  : PathReflecting (Quotient A R) B (quotient_rec A B R hb f resp)
  ≔ let Q ≔ Quotient A R in
    let g ≔ quotient_rec A B R hb f resp in
    z w e ↦
      mere_rec (BookFiber A Q (quotient_class A R) z) (Id Q z w) (quotient_set A R z w)
        (a ↦ mere_rec (BookFiber A Q (quotient_class A R) w) (Id Q z w) (quotient_set A R z w)
          (b ↦
            let fab : Id B (f (a .fst)) (f (b .fst))
              ≔ concat B (f (a .fst)) (g z) (f (b .fst))
                  (inverse B (g z) (f (a .fst)) (map_path Q B g z (quotient_class A R (a .fst)) (a .snd)))
                  (concat B (g z) (g w) (f (b .fst)) e
                    (map_path Q B g w (quotient_class A R (b .fst)) (b .snd))) in
            concat Q z (quotient_class A R (a .fst)) w (a .snd)
              (concat Q (quotient_class A R (a .fst)) (quotient_class A R (b .fst)) w
                (quotient_encode A R (a .fst) (b .fst) (back (a .fst) (b .fst) fab))
                (inverse Q w (quotient_class A R (b .fst)) (b .snd))))
          (quotient_surjective A R w))
        (quotient_surjective A R z)

def surjection_quotient_surjective (A B : Type) (hb : isSet B) (R : EquivalenceRelation A) (f : A → B)
  (hf : Surjective A B f) (resp : Respects A B R f)
  : Surjective (Quotient A R) B (quotient_rec A B R hb f resp)
  ≔ let Q ≔ Quotient A R in
    let g ≔ quotient_rec A B R hb f resp in
    b ↦ mere_rec (BookFiber A B f b) (Mere (BookFiber Q B g b)) (mere_isprop (BookFiber Q B g b))
      (t ↦ mere (BookFiber Q B g b) (quotient_class A R (t .fst), t .snd)) (hf b)

def surjection_quotient_equiv (A B : Type) (hb : isSet B) (R : EquivalenceRelation A) (f : A → B)
  (hf : Surjective A B f) (resp : Respects A B R f) (back : (x y : A) → Id B (f x) (f y) → Rel A R x y)
  : BookEquiv (Quotient A R) B
  ≔ embedding_surjection_equiv native_truncation (Quotient A R) B (quotient_rec A B R hb f resp)
      (path_reflecting_set_embedding (Quotient A R) B hb (quotient_rec A B R hb f resp)
        (surjection_quotient_reflects A B hb R f resp back))
      (surjection_quotient_surjective A B hb R f hf resp)

def surjection_quotient_unique (A B : Type) (hb : isSet B) (R : EquivalenceRelation A) (f : A → B)
  (hf : Surjective A B f) (resp : Respects A B R f) (back : (x y : A) → Id B (f x) (f y) → Rel A R x y)
  : BookIsContr (QuotientEquivalenceLifts A B R f)
  ≔ let c : QuotientEquivalenceLifts A B R f ≔ (surjection_quotient_equiv A B hb R f hf resp back, refl f) in
    (c, quotient_equivalence_lifts_prop A B R hb f c)

{` cor:orbit-equiv. [-] : X(sh_G) → X/G is surjective (orbit_of_point_surjective,
   module 520) and factors uniquely by an equivalence through the quotient
   of X(sh_G) by the relation ∃_g (g · x = y): the type of pairs of an
   equivalence e : X(sh_G)/~ ≃ X/G and an identification [-] = e ∘ class
   is contractible. `}
def orbit_quotient_unique (G : Group) (X : GSet G)
  : BookIsContr (QuotientEquivalenceLifts (gset_underlying G X) (Orbits G X) (orbit_equivalence_relation G X)
      (orbit_of_point G X))
  ≔ surjection_quotient_unique (gset_underlying G X) (Orbits G X) (orbits_set G X) (orbit_equivalence_relation G X)
      (orbit_of_point G X) (orbit_of_point_surjective G X) (orbit_relation_to_path G X) (orbit_relation_from_path G X)

def orbit_quotient_equiv (G : Group) (X : GSet G)
  : BookEquiv (Quotient (gset_underlying G X) (orbit_equivalence_relation G X)) (Orbits G X)
  ≔ surjection_quotient_equiv (gset_underlying G X) (Orbits G X) (orbits_set G X) (orbit_equivalence_relation G X)
      (orbit_of_point G X) (orbit_of_point_surjective G X) (orbit_relation_to_path G X) (orbit_relation_from_path G X)

def orbit_quotient_equiv_class (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (Orbits G X) (orbit_quotient_equiv G X .map (quotient_class (gset_underlying G X) (orbit_equivalence_relation G X) x))
      (orbit_of_point G X x)
  ≔ refl (orbit_of_point G X x)

{` lem:X/G=setTruncX_hG and the sentence after it: [-]_0 factors as
   |-|_0 followed by a unique equivalence ‖X_hG‖_0 ≃ X/G. SetTrunc A is by
   definition the quotient of A by ‖x = y‖. `}
def orbits_set_trunc_unique (G : Group) (X : GSet G)
  : BookIsContr (QuotientEquivalenceLifts (ActionType G X) (Orbits G X) (mere_path_relation (ActionType G X))
      (orbit_map G X))
  ≔ surjection_quotient_unique (ActionType G X) (Orbits G X) (orbits_set G X) (mere_path_relation (ActionType G X))
      (orbit_map G X) (orbit_map_surjective G X) (orbit_map_path_from_mere G X) (orbit_map_path_to_mere G X)

def orbits_set_trunc_equiv (G : Group) (X : GSet G) : BookEquiv (SetTrunc (ActionType G X)) (Orbits G X)
  ≔ surjection_quotient_equiv (ActionType G X) (Orbits G X) (orbits_set G X) (mere_path_relation (ActionType G X))
      (orbit_map G X) (orbit_map_surjective G X) (orbit_map_path_from_mere G X) (orbit_map_path_to_mere G X)

def orbits_set_trunc_equiv_class (G : Group) (X : GSet G) (u : ActionType G X)
  : Id (Orbits G X) (orbits_set_trunc_equiv G X .map (set_trunc (ActionType G X) u)) (orbit_map G X u)
  ≔ refl (orbit_map G X u)

{` The type Σ_{S:Set}(A → S) of sets under A. `}
def SetsWithMapFrom (A : Type) : Type ≔ Σ SetTypes (S ↦ A → S .fst)

{` Transport in the family S ↦ S of underlying types of sets. Along
   set_types_path S T e it is e by definition. `}
def set_types_transport (S T : SetTypes) (q : Id SetTypes S T) (s : S .fst) : T .fst
  ≔ transport SetTypes (R ↦ R .fst) S T q s

def set_types_path_transport (S T : SetTypes) (e : Equiv (S .fst) (T .fst)) (s : S .fst)
  : Id (T .fst) (set_types_transport S T (set_types_path S T e) s) (e .map s)
  ≔ refl (e .map s)

def sets_with_map_path_base (A : Type) (S : SetTypes) (f : A → S .fst)
  : Id (SetsWithMapFrom A) (S, f) (S, a ↦ set_types_transport S S (refl S) (f a))
  ≔ map_path (A → S .fst) (SetsWithMapFrom A) (g ↦ (S, g)) f (a ↦ set_types_transport S S (refl S) (f a))
      (funext A (_ ↦ S .fst) f (a ↦ set_types_transport S S (refl S) (f a))
        (a ↦ inverse (S .fst) (set_types_transport S S (refl S) (f a)) (f a)
          (transport_refl SetTypes (R ↦ R .fst) S (f a))))

def sets_with_map_path_transport (A : Type) (S T : SetTypes) (q : Id SetTypes S T) (f : A → S .fst)
  : Id (SetsWithMapFrom A) (S, f) (T, a ↦ set_types_transport S T q (f a))
  ≔ J SetTypes S (T q ↦ Id (SetsWithMapFrom A) (S, f) (T, a ↦ set_types_transport S T q (f a)))
      (sets_with_map_path_base A S f) T q

{` An equivalence e : S ≃ T with e ∘ f = f' gives (S, f) = (T, f'). `}
def sets_with_map_path (A : Type) (u v : SetsWithMapFrom A) (e : Equiv (u .fst .fst) (v .fst .fst))
  (h : (a : A) → Id (v .fst .fst) (e .map (u .snd a)) (v .snd a)) : Id (SetsWithMapFrom A) u v
  ≔ let q ≔ set_types_path (u .fst) (v .fst) e in
    let f1 : A → v .fst .fst ≔ a ↦ set_types_transport (u .fst) (v .fst) q (u .snd a) in
    concat (SetsWithMapFrom A) u (v .fst, f1) v
      (sets_with_map_path_transport A (u .fst) (v .fst) q (u .snd))
      (map_path (A → v .fst .fst) (SetsWithMapFrom A) (g ↦ (v .fst, g)) f1 (v .snd)
        (funext A (_ ↦ v .fst .fst) f1 (v .snd)
          (a ↦ concat (v .fst .fst) (f1 a) (e .map (u .snd a)) (v .snd a)
            (set_types_path_transport (u .fst) (v .fst) e (u .snd a)) (h a))))

{` Conversely every identification r : (S, f) = (T, f') transports f to f'. `}
def sets_with_map_path_commutes (A : Type) (u v : SetsWithMapFrom A) (r : Id (SetsWithMapFrom A) u v) (a : A)
  : Id (v .fst .fst) (set_types_transport (u .fst) (v .fst) (r .fst) (u .snd a)) (v .snd a)
  ≔ J (SetsWithMapFrom A) u
      (w r ↦ Id (w .fst .fst) (set_types_transport (u .fst) (w .fst) (r .fst) (u .snd a)) (w .snd a))
      (transport_refl SetTypes (R ↦ R .fst) (u .fst) (u .snd a)) v r

{` Identifications of sets are determined by their transport functions. `}
def set_types_transport_reflects (S T : SetTypes) (q q' : Id SetTypes S T)
  (h : (s : S .fst) → Id (T .fst) (set_types_transport S T q s) (set_types_transport S T q' s))
  : Id (Id SetTypes S T) q q'
  ≔ let E ≔ compose_equiv (Id SetTypes S T) (Id Type (S .fst) (T .fst)) (Equiv (S .fst) (T .fst))
        (subtype_path_equiv Type isSet isset_isprop S T) (transport_univalence_equiv (S .fst) (T .fst)) in
    equivalence_injective (Id SetTypes S T) (Equiv (S .fst) (T .fst)) E q q'
      (equiv_path (S .fst) (T .fst) (E .map q) (E .map q')
        (funext (S .fst) (_ ↦ T .fst) (E .map q .map) (E .map q' .map) h))

{` If f : A → S is surjective, then (S, f) = (T, f') is a proposition:
   the identification of first components is determined by f' (via the
   transport functions), and the second components are paths over it in a
   family of sets. `}
def sets_with_map_paths_prop (A : Type) (u v : SetsWithMapFrom A) (hu : Surjective A (u .fst .fst) (u .snd))
  : isProp (Id (SetsWithMapFrom A) u v)
  ≔ let F : SetTypes → Type ≔ R ↦ A → R .fst in
    let S ≔ u .fst in
    let T ≔ v .fst in
    let po_prop : (q : Id SetTypes S T) → isProp (Id F q (u .snd) (v .snd))
      ≔ q ↦ hlevel_one_to_prop (Id F q (u .snd) (v .snd))
          (pathover_hlevel (suc. zero.) SetTypes F
            (R ↦ set_to_hlevel_two (F R) (pi_set A (_ ↦ R .fst) (_ ↦ R .snd))) S T q (u .snd) (v .snd)) in
    r r' ↦
      let tr ≔ set_types_transport S T (r .fst) in
      let tr' ≔ set_types_transport S T (r' .fst) in
      let t : Id (S .fst → T .fst) tr tr'
        ≔ surjection_function_ext A (S .fst) (T .fst) (u .snd) hu (T .snd) tr tr'
            (funext A (_ ↦ T .fst) (a ↦ tr (u .snd a)) (a ↦ tr' (u .snd a))
              (a ↦ concat (T .fst) (tr (u .snd a)) (v .snd a) (tr' (u .snd a))
                (sets_with_map_path_commutes A u v r a)
                (inverse (T .fst) (tr' (u .snd a)) (v .snd a) (sets_with_map_path_commutes A u v r' a)))) in
      let p1 : Id (Id SetTypes S T) (r .fst) (r' .fst)
        ≔ set_types_transport_reflects S T (r .fst) (r' .fst) (happly (S .fst) (_ ↦ T .fst) tr tr' t) in
      map_path (SigmaPath SetTypes F u v) (Id (SetsWithMapFrom A) u v) (sigma_path_pair SetTypes F u v)
        (r .fst, r .snd) (r' .fst, r' .snd)
        (subtype_equal (Id SetTypes S T) (q ↦ Id F q (u .snd) (v .snd)) po_prop
          (r .fst, r .snd) (r' .fst, r' .snd) p1)

{` lem:X/G=setTruncX_hG, second part: the (unique) identification of
   (X/G, [-]_0) and (‖X_hG‖_0, |-|_0) in Σ_{S:Set}(X_hG → S); the identity
   type is contractible. `}
def orbits_pair (G : Group) (X : GSet G) : SetsWithMapFrom (ActionType G X)
  ≔ ((Orbits G X, orbits_set G X), orbit_map G X)

def set_trunc_pair (A : Type) : SetsWithMapFrom A ≔ ((SetTrunc A, set_trunc_set A), set_trunc A)

def orbits_set_trunc_path (G : Group) (X : GSet G)
  : Id (SetsWithMapFrom (ActionType G X)) (orbits_pair G X) (set_trunc_pair (ActionType G X))
  ≔ let T ≔ ActionType G X in
    let e ≔ canonical_inverse_equiv (SetTrunc T) (Orbits G X)
      (native_equivalence (SetTrunc T) (Orbits G X) (orbits_set_trunc_equiv G X)) in
    sets_with_map_path T (orbits_pair G X) (set_trunc_pair T) e
      (u ↦ inverse (SetTrunc T) (set_trunc T u) (e .map (orbit_map G X u))
        (equiv_unit (SetTrunc T) (Orbits G X)
          (native_equivalence (SetTrunc T) (Orbits G X) (orbits_set_trunc_equiv G X)) (set_trunc T u)))

def orbits_set_trunc_path_unique (G : Group) (X : GSet G)
  : BookIsContr (Id (SetsWithMapFrom (ActionType G X)) (orbits_pair G X) (set_trunc_pair (ActionType G X)))
  ≔ (orbits_set_trunc_path G X,
     sets_with_map_paths_prop (ActionType G X) (orbits_pair G X) (set_trunc_pair (ActionType G X))
       (orbit_map_surjective G X) (orbits_set_trunc_path G X))

{` rem:SubGX=Sub(X/G). Sub_G(X) ≡ Π_{z:BG}(X(z) → Prop) ≃ (X_hG → Prop)
   (currying) ≃ (‖X_hG‖_0 → Prop) (Prop is a set) ≃ (X/G → Prop)
   (lem:X/G=setTruncX_hG) ≡ Sub(X/G). `}
def orbit_subsets_curry_equiv (G : Group) (X : GSet G) : Equiv (GSubsets G X) (ActionType G X → PropTypes)
  ≔ quasi_inverse_equiv (GSubsets G X) (ActionType G X → PropTypes)
      (P u ↦ P (u .fst) (u .snd)) (Q z x ↦ Q (z, x)) (P ↦ refl P) (Q ↦ refl Q)

def orbit_subsets_set_trunc_equiv (A : Type) : Equiv (A → PropTypes) (SetTrunc A → PropTypes)
  ≔ canonical_inverse_equiv (SetTrunc A → PropTypes) (A → PropTypes)
      (native_equivalence (SetTrunc A → PropTypes) (A → PropTypes)
        (set_trunc_universal_property A PropTypes propositions_set))

def orbit_subsets_precompose_equiv (A B C : Type) (e : Equiv A B) : Equiv (A → C) (B → C)
  ≔ quasi_inverse_equiv (A → C) (B → C)
      (f b ↦ f (equiv_inverse_map A B e b)) (g a ↦ g (e .map a))
      (f ↦ funext A (_ ↦ C) (a ↦ f (equiv_inverse_map A B e (e .map a))) f
        (a ↦ refl f (equiv_retraction A B e a)))
      (g ↦ funext B (_ ↦ C) (b ↦ g (e .map (equiv_inverse_map A B e b))) g
        (b ↦ refl g (equiv_counit A B e b)))

def gsubsets_orbit_subsets_equiv (G : Group) (X : GSet G) : Equiv (GSubsets G X) (Subtypes (Orbits G X))
  ≔ let T ≔ ActionType G X in
    compose_equiv (GSubsets G X) (T → PropTypes) (Subtypes (Orbits G X))
      (orbit_subsets_curry_equiv G X)
      (compose_equiv (T → PropTypes) (SetTrunc T → PropTypes) (Orbits G X → PropTypes)
        (orbit_subsets_set_trunc_equiv T)
        (orbit_subsets_precompose_equiv (SetTrunc T) (Orbits G X) PropTypes
          (native_equivalence (SetTrunc T) (Orbits G X) (orbits_set_trunc_equiv G X))))

{` The inverse direction sends a subset S of X/G to the G-subset
   z ↦ x ↦ S([(z, x)]_0), i.e. precomposition with [-]_0. `}
def gsubsets_orbit_subsets_inverse (G : Group) (X : GSet G) (S : Subtypes (Orbits G X))
  : Id (GSubsets G X)
      (equiv_inverse_map (GSubsets G X) (Subtypes (Orbits G X)) (gsubsets_orbit_subsets_equiv G X) S)
      (z x ↦ S (orbit_map G X (z, x)))
  ≔ refl ((z x ↦ S (orbit_map G X (z, x))) : GSubsets G X)

{` xca:transX-just1orbit. X/G is contractible iff X is transitive. `}
def transitive_orbits_contractible (G : Group) (X : GSet G) (t : IsTransitive G X) : BookIsContr (Orbits G X)
  ≔ let T ≔ ActionType G X in
    let c ≔ transitive_action_type_connected G X t in
    mere_rec T (BookIsContr (Orbits G X)) (book_iscontr_isprop (Orbits G X))
      (u ↦ (orbit_map G X u,
            O ↦ mere_rec (BookFiber T (Orbits G X) (orbit_map G X) O) (Id (Orbits G X) (orbit_map G X u) O)
              (orbits_set G X (orbit_map G X u) O)
              (w ↦ concat (Orbits G X) (orbit_map G X u) (orbit_map G X (w .fst)) O
                (orbit_map_path_from_mere G X u (w .fst) (c .snd u (w .fst)))
                (inverse (Orbits G X) O (orbit_map G X (w .fst)) (w .snd)))
              (orbit_map_surjective G X O)))
      (c .fst)

def contractible_orbits_transitive (G : Group) (X : GSet G) (h : BookIsContr (Orbits G X)) : IsTransitive G X
  ≔ let T ≔ ActionType G X in
    connected_action_type_transitive G X
      (mere_rec (BookFiber T (Orbits G X) (orbit_map G X) (h .center)) (Mere T) (mere_isprop T)
         (w ↦ mere T (w .fst)) (orbit_map_surjective G X (h .center)),
       u v ↦ orbit_map_path_to_mere G X u v
         (concat (Orbits G X) (orbit_map G X u) (h .center) (orbit_map G X v)
           (inverse (Orbits G X) (h .center) (orbit_map G X u) (h .contract (orbit_map G X u)))
           (h .contract (orbit_map G X v))))

def orbits_contractible_transitive_equiv (G : Group) (X : GSet G)
  : Equiv (BookIsContr (Orbits G X)) (IsTransitive G X)
  ≔ iff_equiv (BookIsContr (Orbits G X)) (IsTransitive G X) (book_iscontr_isprop (Orbits G X))
      (is_transitive_prop G X) (contractible_orbits_transitive G X) (transitive_orbits_contractible G X)
