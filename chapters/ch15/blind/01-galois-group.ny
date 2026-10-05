{` Blind statements for chapter 15 (galois.tex), section "Covering spaces and field extensions":
   field extensions, the Galois group, the structure identity principle for fields. `}
export "../../../src/1302-vector-spaces"
export "../../../src/702-abstract-group-identity"
export "../../../src/25-coverings"

{` A morphism of fields is a ring homomorphism of the underlying rings. `}
def BlindFieldHom (k K : Field) : Type ≔ RingHom (k .fst) (K .fst)

{` k\Fields ≔ Σ (K : Fields) hom_Fields(k, K) (running text before def:galois-group). `}
def BlindFieldExt (k : Field) : Type ≔ Σ Field (K ↦ BlindFieldHom k K)

{` ---- Groupoid-ness of k\Fields (needed to form Aut_{k\Fields}(K,i) as a group). ---- `}

def blind_distr_laws_prop (S : Type) (hS : isSet S) (mul add : S → S → S) : isProp (DistrLaws S mul add)
  ≔ product_prop ((a b c : S) → Id S (mul a (add b c)) (add (mul a b) (mul a c)))
      ((a b c : S) → Id S (mul (add a b) c) (add (mul a c) (mul b c)))
      (pi_prop S (a ↦ (b c : S) → Id S (mul a (add b c)) (add (mul a b) (mul a c)))
        (a ↦ pi_prop S (b ↦ (c : S) → Id S (mul a (add b c)) (add (mul a b) (mul a c)))
          (b ↦ pi_prop S (c ↦ Id S (mul a (add b c)) (add (mul a b) (mul a c)))
            (c ↦ hS (mul a (add b c)) (add (mul a b) (mul a c))))))
      (pi_prop S (a ↦ (b c : S) → Id S (mul (add a b) c) (add (mul a c) (mul b c)))
        (a ↦ pi_prop S (b ↦ (c : S) → Id S (mul (add a b) c) (add (mul a c) (mul b c)))
          (b ↦ pi_prop S (c ↦ Id S (mul (add a b) c) (add (mul a c) (mul b c)))
            (c ↦ hS (mul (add a b) c) (add (mul a c) (mul b c))))))

def BlindRingStruct (G : AbstractGroup) : Type
  ≔ Σ (G .carrier) (e ↦ Σ (G .carrier → G .carrier → G .carrier) (μ ↦
      Product (MonoidLaws (G .carrier) e μ) (DistrLaws (G .carrier) μ (G .mul))))

def blind_ring_struct_set (G : AbstractGroup) : isSet (BlindRingStruct G)
  ≔ let S ≔ G .carrier in let hS ≔ abstract_group_set G in
    sigma_set S (e ↦ Σ (S → S → S) (μ ↦ Product (MonoidLaws S e μ) (DistrLaws S μ (G .mul))))
      hS
      (e ↦ sigma_set (S → S → S) (μ ↦ Product (MonoidLaws S e μ) (DistrLaws S μ (G .mul)))
        (pi_set S (_ ↦ S → S) (_ ↦ pi_set S (_ ↦ S) (_ ↦ hS)))
        (μ ↦ prop_is_set (Product (MonoidLaws S e μ) (DistrLaws S μ (G .mul)))
          (product_prop (MonoidLaws S e μ) (DistrLaws S μ (G .mul))
            (monoid_laws_prop S e μ) (blind_distr_laws_prop S hS μ (G .mul)))))

def blind_three : Nat ≔ suc. (suc. (suc. zero.))

def blind_ring_sigma_hlevel : HLevel blind_three AbstractRingSigma
  ≔ hlevel_sigma blind_three AbstractGroup BlindRingStruct
      (groupoid_to_hlevel AbstractGroup abstract_group_groupoid)
      (G ↦ hlevel_raise (suc. (suc. zero.)) (BlindRingStruct G)
        (set_to_hlevel_two (BlindRingStruct G) (blind_ring_struct_set G)))

def blind_ring_hlevel : HLevel blind_three AbstractRing
  ≔ hlevel_equiv blind_three AbstractRingSigma AbstractRing
      (quasi_inverse_equiv AbstractRingSigma AbstractRing abstract_ring_from_sigma abstract_ring_to_sigma
        (t ↦ refl t) (R ↦ refl R))
      blind_ring_sigma_hlevel

def blind_is_field_prop (R : AbstractRing) : isProp (IsField R)
  ≔ product_prop (IsNonTrivialCRing R) (BookIsContr (NonInvertibles R))
      (product_prop (IsCommutativeRing R) (IsNonTrivialRing R) (is_commutative_ring_prop R) (is_non_trivial_ring_prop R))
      (book_iscontr_isprop (NonInvertibles R))

def blind_field_hlevel : HLevel blind_three Field
  ≔ hlevel_sigma blind_three AbstractRing IsField blind_ring_hlevel
      (R ↦ prop_hlevel (suc. (suc. zero.)) (IsField R) (blind_is_field_prop R))

def blind_ring_hom_set (R S : AbstractRing) : isSet (RingHom R S)
  ≔ sigma_set (AbstractHom (ring_additive_group R) (ring_additive_group S))
      (φ ↦ Product (Id (S .carrier) (φ .fst (R .one)) (S .one))
        ((s s' : R .carrier) → Id (S .carrier) (φ .fst (R .mul s s')) (S .mul (φ .fst s) (φ .fst s'))))
      (abstract_hom_set (ring_additive_group R) (ring_additive_group S))
      (φ ↦ prop_is_set (Product (Id (S .carrier) (φ .fst (R .one)) (S .one))
          ((s s' : R .carrier) → Id (S .carrier) (φ .fst (R .mul s s')) (S .mul (φ .fst s) (φ .fst s'))))
        (is_ring_hom_extra_prop R S (φ .fst)))

def blind_field_ext_groupoid (k : Field) : isGroupoid (BlindFieldExt k)
  ≔ hlevel_to_groupoid (BlindFieldExt k)
      (hlevel_sigma blind_three Field (K ↦ BlindFieldHom k K) blind_field_hlevel
        (K ↦ hlevel_raise (suc. (suc. zero.)) (BlindFieldHom k K)
          (set_to_hlevel_two (BlindFieldHom k K) (blind_ring_hom_set (k .fst) (K .fst)))))

{` def:galois-group. Gal(K, i) ≔ Aut_{k\Fields}(K, i). (The book writes "an extension (K,i) of a field K";
   the field being extended is k.) `}
def BlindGaloisGroup (k : Field) (E : BlindFieldExt k) : Group
  ≔ automorphism_group (BlindFieldExt k) (blind_field_ext_groupoid k) E

{` ---- rem:sip-univalence ---- `}

{` Iso(K, L): equivalences of the carriers that are homomorphisms of fields
   (preserve +, ·, 0, 1), as in the last display of the remark. `}
def BlindFieldIso (K L : Field) : Type
  ≔ let A ≔ K .fst in let B ≔ L .fst in
    Σ (Equiv (A .carrier) (B .carrier)) (φ ↦
      Product ((x y : A .carrier) → Id (B .carrier) (φ .map (A .add x y)) (B .add (φ .map x) (φ .map y)))
        (Product ((x y : A .carrier) → Id (B .carrier) (φ .map (A .mul x y)) (B .mul (φ .map x) (φ .map y)))
          (Product (Id (B .carrier) (φ .map (A .zero)) (B .zero))
            (Id (B .carrier) (φ .map (A .one)) (B .one)))))

{` Transport of a binary operation / an element along a path of carrier types. `}
def blind_trp_op (X Y : Type) (p : Id Type X Y) (op : X → X → X) : Y → Y → Y
  ≔ transport Type (Z ↦ Z → Z → Z) X Y p op

def blind_trp_elt (X Y : Type) (p : Id Type X Y) (x : X) : Y ≔ transport Type (Z ↦ Z) X Y p x

{` First display: (K = L) ≃ Σ (p : K =_U L) (trp p (+K) = +L) × (trp p (·K) = ·L) × (trp p 0K = 0L) × (trp p 1K = 1L). `}
def blind_field_paths_structure : Type
  ≔ (K L : Field) →
    let A ≔ K .fst in let B ≔ L .fst in
    Equiv (Id Field K L)
      (Σ (Id Type (A .carrier) (B .carrier)) (p ↦
        Product (Id (B .carrier → B .carrier → B .carrier) (blind_trp_op (A .carrier) (B .carrier) p (A .add)) (B .add))
          (Product (Id (B .carrier → B .carrier → B .carrier) (blind_trp_op (A .carrier) (B .carrier) p (A .mul)) (B .mul))
            (Product (Id (B .carrier) (blind_trp_elt (A .carrier) (B .carrier) p (A .zero)) (B .zero))
              (Id (B .carrier) (blind_trp_elt (A .carrier) (B .carrier) p (A .one)) (B .one))))))

{` Second display: for p = ua(φ), the transported structure is conjugation by φ. `}
def blind_field_transport_structure : Type
  ≔ (K L : Field) (φ : Equiv (K .fst .carrier) (L .fst .carrier)) →
    let A ≔ K .fst in let B ≔ L .fst in
    let p ≔ ua (A .carrier) (B .carrier) φ in
    let ψ ≔ equiv_inverse_map (A .carrier) (B .carrier) φ in
    Product (Id (B .carrier → B .carrier → B .carrier) (blind_trp_op (A .carrier) (B .carrier) p (A .add))
              (x y ↦ φ .map (A .add (ψ x) (ψ y))))
      (Product (Id (B .carrier → B .carrier → B .carrier) (blind_trp_op (A .carrier) (B .carrier) p (A .mul))
                 (x y ↦ φ .map (A .mul (ψ x) (ψ y))))
        (Product (Id (B .carrier) (blind_trp_elt (A .carrier) (B .carrier) p (A .zero)) (φ .map (A .zero)))
          (Id (B .carrier) (blind_trp_elt (A .carrier) (B .carrier) p (A .one)) (φ .map (A .one)))))

{` Structure identity principle for fields: (K = L) ≃ Iso(K, L). `}
def blind_field_sip : Type ≔ (K L : Field) → Equiv (Id Field K L) (BlindFieldIso K L)

{` Last display: USym Gal(K,i) ≃ Σ (p : K = K) trp p i = i ≃ Σ (σ : Iso(K,K)) σ ∘ i = i.
   (σ ∘ i = i is read as equality of the underlying functions k → K; ring homomorphisms are determined
   by their functions.) `}
def blind_galois_usym_paths : Type
  ≔ (k : Field) (E : BlindFieldExt k) →
    Equiv (USym (BlindGaloisGroup k E))
      (Σ (Id Field (E .fst) (E .fst)) (p ↦
        Id (BlindFieldHom k (E .fst)) (transport Field (X ↦ BlindFieldHom k X) (E .fst) (E .fst) p (E .snd)) (E .snd)))

def blind_galois_usym_isos : Type
  ≔ (k : Field) (E : BlindFieldExt k) →
    Equiv (USym (BlindGaloisGroup k E))
      (Σ (BlindFieldIso (E .fst) (E .fst)) (σ ↦
        Id (k .fst .carrier → E .fst .fst .carrier) (x ↦ σ .fst .map (E .snd .fst .fst x)) (E .snd .fst .fst)))
