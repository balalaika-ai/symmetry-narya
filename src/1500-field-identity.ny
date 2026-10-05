export "1303-two-element-field"
export "702-abstract-group-identity"

{` Chapter 15 (galois.tex), rem:sip-univalence: the structure identity
   principle for rings and fields. Iso(K, L) is the book's type of
   equivalences φ : K ≃ L with φ(x + y) = φ(x) + φ(y), φ(x · y) = φ(x) · φ(y),
   φ(0) = 0 and φ(1) = 1 (RingIso / FieldIso, exactly these four laws).
   (K = L) ≃ Iso(K, L) is proved as rem:abs-iso (module 702) and the module
   SIP (module 1304): an identification of the ring data (carrier, 0, +, -,
   1, ·) over ua(φ) gives an identification of rings since the laws are a
   proposition. The abstract rings of chapter 13 also carry the negation;
   it is preserved by every additive homomorphism, so Iso is unchanged.
   Fields are Σ AbstractRing IsField with IsField a proposition. `}

{` Equality of two binary (ternary) operations into a set is a proposition. `}
def binop_eq_prop (A T : Type) (hT : isSet T) (l r : A → A → T) : isProp ((x y : A) → Id T (l x y) (r x y))
  ≔ pi_prop A (x ↦ (y : A) → Id T (l x y) (r x y))
      (x ↦ pi_prop A (y ↦ Id T (l x y) (r x y)) (y ↦ hT (l x y) (r x y)))

def ternop_eq_prop (A T : Type) (hT : isSet T) (l r : A → A → A → T)
  : isProp ((x y z : A) → Id T (l x y z) (r x y z))
  ≔ pi_prop A (x ↦ (y z : A) → Id T (l x y z) (r x y z)) (x ↦ binop_eq_prop A T hT (l x) (r x))

{` The four laws of the book's Iso(K, L) for a map f. `}
def RingIsoLaws (R S : AbstractRing) (f : R .carrier → S .carrier) : Type
  ≔ Product ((x y : R .carrier) → Id (S .carrier) (f (R .add x y)) (S .add (f x) (f y)))
      (Product ((x y : R .carrier) → Id (S .carrier) (f (R .mul x y)) (S .mul (f x) (f y)))
        (Product (Id (S .carrier) (f (R .zero)) (S .zero)) (Id (S .carrier) (f (R .one)) (S .one))))

def ring_iso_laws_prop (R S : AbstractRing) (f : R .carrier → S .carrier) : isProp (RingIsoLaws R S f)
  ≔ let T ≔ S .carrier in let hT ≔ ring_set S in
    product_prop ((x y : R .carrier) → Id T (f (R .add x y)) (S .add (f x) (f y)))
      (Product ((x y : R .carrier) → Id T (f (R .mul x y)) (S .mul (f x) (f y)))
        (Product (Id T (f (R .zero)) (S .zero)) (Id T (f (R .one)) (S .one))))
      (binop_eq_prop (R .carrier) T hT (x y ↦ f (R .add x y)) (x y ↦ S .add (f x) (f y)))
      (product_prop ((x y : R .carrier) → Id T (f (R .mul x y)) (S .mul (f x) (f y)))
        (Product (Id T (f (R .zero)) (S .zero)) (Id T (f (R .one)) (S .one)))
        (binop_eq_prop (R .carrier) T hT (x y ↦ f (R .mul x y)) (x y ↦ S .mul (f x) (f y)))
        (product_prop (Id T (f (R .zero)) (S .zero)) (Id T (f (R .one)) (S .one))
          (hT (f (R .zero)) (S .zero)) (hT (f (R .one)) (S .one))))

{` Iso(R, S): equivalences of carriers preserving +, ·, 0, 1. `}
def RingIso (R S : AbstractRing) : Type ≔ Σ (Equiv (R .carrier) (S .carrier)) (f ↦ RingIsoLaws R S (f .map))

def ring_iso_map (R S : AbstractRing) (φ : RingIso R S) : R .carrier → S .carrier ≔ φ .fst .map

def ring_iso_path (R S : AbstractRing) (φ ψ : RingIso R S)
  (h : Id (R .carrier → S .carrier) (φ .fst .map) (ψ .fst .map)) : Id (RingIso R S) φ ψ
  ≔ subtype_equal (Equiv (R .carrier) (S .carrier)) (f ↦ RingIsoLaws R S (f .map))
      (f ↦ ring_iso_laws_prop R S (f .map)) φ ψ
      (equiv_path (R .carrier) (S .carrier) (φ .fst) (ψ .fst) h)

def ring_iso_set (R S : AbstractRing) : isSet (RingIso R S)
  ≔ sigma_set (Equiv (R .carrier) (S .carrier)) (f ↦ RingIsoLaws R S (f .map))
      (equivalences_set (R .carrier) (S .carrier) (ring_set S))
      (f ↦ prop_is_set (RingIsoLaws R S (f .map)) (ring_iso_laws_prop R S (f .map)))

{` The ring homomorphism underlying an isomorphism. `}
def ring_iso_hom (R S : AbstractRing) (φ : RingIso R S) : RingHom R S
  ≔ ((φ .fst .map, φ .snd .fst), (φ .snd .snd .snd .snd, φ .snd .snd .fst))

def ring_iso_id (R : AbstractRing) : RingIso R R
  ≔ (identity_equiv (R .carrier),
     (x y ↦ refl (R .add x y), (x y ↦ refl (R .mul x y), (refl (R .zero), refl (R .one)))))

def ring_hom_set (R S : AbstractRing) : isSet (RingHom R S)
  ≔ sigma_set (AbstractHom (ring_additive_group R) (ring_additive_group S))
      (χ ↦ Product (Id (S .carrier) (χ .fst (R .one)) (S .one))
        ((s s' : R .carrier) → Id (S .carrier) (χ .fst (R .mul s s')) (S .mul (χ .fst s) (χ .fst s'))))
      (abstract_hom_set (ring_additive_group R) (ring_additive_group S))
      (χ ↦ prop_is_set (Product (Id (S .carrier) (χ .fst (R .one)) (S .one))
          ((s s' : R .carrier) → Id (S .carrier) (χ .fst (R .mul s s')) (S .mul (χ .fst s) (χ .fst s'))))
        (is_ring_hom_extra_prop R S (χ .fst)))

{` The data (S, 0, +, -, 1, ·) of a ring and the laws over it. `}
def RingData : Type
  ≔ Σ Type (S ↦ Σ S (z ↦ Σ (S → S → S) (ad ↦ Σ (S → S) (ng ↦ Σ S (o ↦ S → S → S)))))

def ring_data (R : AbstractRing) : RingData ≔ (R .carrier, (R .zero, (R .add, (R .neg, (R .one, R .mul)))))

def RingLawsAt (d : RingData) : Type
  ≔ let S ≔ d .fst in let z ≔ d .snd .fst in let ad ≔ d .snd .snd .fst in
    let ng ≔ d .snd .snd .snd .fst in let o ≔ d .snd .snd .snd .snd .fst in
    let mu ≔ d .snd .snd .snd .snd .snd in
    Product (AbstractGroupLaws S z ad ng) (Product (MonoidLaws S o mu) (DistrLaws S mu ad))

def ring_laws (R : AbstractRing) : RingLawsAt (ring_data R) ≔ (R .add_laws, (R .mul_laws, R .distr))

def ring_laws_prop (d : RingData) : isProp (RingLawsAt d)
  ≔ let S ≔ d .fst in let z ≔ d .snd .fst in let ad ≔ d .snd .snd .fst in
    let ng ≔ d .snd .snd .snd .fst in let o ≔ d .snd .snd .snd .snd .fst in
    let mu ≔ d .snd .snd .snd .snd .snd in
    u v ↦ let hS ≔ u .fst .carrier_set in
    (abstract_group_laws_prop S z ad ng (u .fst) (v .fst),
     (monoid_laws_prop S o mu (u .snd .fst) (v .snd .fst),
      (ternop_eq_prop S S hS (a b c ↦ mu a (ad b c)) (a b c ↦ ad (mu a b) (mu a c))
         (u .snd .snd .fst) (v .snd .snd .fst),
       ternop_eq_prop S S hS (a b c ↦ mu (ad a b) c) (a b c ↦ ad (mu a c) (mu b c))
         (u .snd .snd .snd) (v .snd .snd .snd))))

def ring_laws_pathover (d d' : RingData) (q : Id RingData d d') (l : RingLawsAt d) (l' : RingLawsAt d')
  : Id RingLawsAt q l l'
  ≔ pathover_hlevel zero. RingData RingLawsAt (e ↦ prop_to_hlevel_one (RingLawsAt e) (ring_laws_prop e))
      d d' q l l' .center

def ring_path_of_data (R S : AbstractRing) (q : Id RingData (ring_data R) (ring_data S)) : Id AbstractRing R S
  ≔ let L ≔ ring_laws_pathover (ring_data R) (ring_data S) q (ring_laws R) (ring_laws S) in
    (q .fst, q .snd .fst, q .snd .snd .fst, q .snd .snd .snd .fst, L .fst,
     q .snd .snd .snd .snd .fst, q .snd .snd .snd .snd .snd, L .snd .fst, L .snd .snd)

{` The data identification over ua(φ) for an isomorphism φ. `}
def ring_data_path_from_iso (R S : AbstractRing) (φ : RingIso R S) : Id RingData (ring_data R) (ring_data S)
  ≔ let A ≔ R .carrier in let T ≔ S .carrier in let f ≔ φ .fst in let l ≔ φ .snd in
    let G ≔ ring_additive_group R in let H ≔ ring_additive_group S in
    (ua A T f,
     ((unglue ≔ l .snd .snd .fst),
      (x y ⤇ (unglue ≔ concat T (f .map (R .add x.0 y.0)) (S .add (f .map x.0) (f .map y.0)) (S .add x.1 y.1)
                (l .fst x.0 y.0) (refl (S .add) (x.2 .unglue) (y.2 .unglue))),
       (x ⤇ (unglue ≔ concat T (f .map (R .neg x.0)) (S .neg (f .map x.0)) (S .neg x.1)
                (abstract_hom_preserves_inv G H (f .map) (l .fst) x.0) (refl (S .neg) (x.2 .unglue))),
        ((unglue ≔ l .snd .snd .snd),
         x y ⤇ (unglue ≔ concat T (f .map (R .mul x.0 y.0)) (S .mul (f .map x.0) (f .map y.0)) (S .mul x.1 y.1)
                (l .snd .fst x.0 y.0) (refl (S .mul) (x.2 .unglue) (y.2 .unglue))))))))

{` The identification of rings given by an isomorphism; its carrier
   component is ua(φ), so transport along it is φ by computation. `}
def ring_path_from_iso (R S : AbstractRing) (φ : RingIso R S) : Id AbstractRing R S
  ≔ ring_path_of_data R S (ring_data_path_from_iso R S φ)

{` The isomorphism underlying an identification: transport along the carrier. `}
def ring_path_to_iso (R S : AbstractRing) (p : Id AbstractRing R S) : RingIso R S
  ≔ let P ≔ p .carrier in let A ≔ R .carrier in let T ≔ S .carrier in
    (transport_equiv A T P,
     (s s' ↦ type_pathover_transport A T P (R .add s s') (S .add (P .trr s) (P .trr s'))
        (p .add (P .liftr s) (P .liftr s')),
      (s s' ↦ type_pathover_transport A T P (R .mul s s') (S .mul (P .trr s) (P .trr s'))
         (p .mul (P .liftr s) (P .liftr s')),
       (type_pathover_transport A T P (R .zero) (S .zero) (p .zero),
        type_pathover_transport A T P (R .one) (S .one) (p .one)))))

def ring_iso_path_section (R S : AbstractRing) (φ : RingIso R S)
  : Id (RingIso R S) (ring_path_to_iso R S (ring_path_from_iso R S φ)) φ
  ≔ ring_iso_path R S (ring_path_to_iso R S (ring_path_from_iso R S φ)) φ (refl (φ .fst .map))

def ring_iso_total_contractible (R : AbstractRing) : isContr (Σ AbstractRing (RingIso R))
  ≔ contractible_retract (Σ AbstractRing (S ↦ Id AbstractRing R S)) (Σ AbstractRing (RingIso R))
      (iscontr_idfrom AbstractRing R)
      (totalize AbstractRing (S ↦ Id AbstractRing R S) (RingIso R) (ring_path_to_iso R))
      (totalize AbstractRing (RingIso R) (S ↦ Id AbstractRing R S) (ring_path_from_iso R))
      (u ↦ (refl (u .fst), ring_iso_path_section R (u .fst) (u .snd)))

def ring_path_to_iso_is_equiv (R S : AbstractRing)
  : isEquiv (Id AbstractRing R S) (RingIso R S) (ring_path_to_iso R S)
  ≔ fiberwise_from_total AbstractRing (S ↦ Id AbstractRing R S) (RingIso R) (ring_path_to_iso R)
      (cat_contractible_map_is_equiv (Σ AbstractRing (S ↦ Id AbstractRing R S)) (Σ AbstractRing (RingIso R))
        (totalize AbstractRing (S ↦ Id AbstractRing R S) (RingIso R) (ring_path_to_iso R))
        (iscontr_idfrom AbstractRing R) (ring_iso_total_contractible R)) S

{` (R = S) ≃ Iso(R, S) for abstract rings. `}
def ring_path_iso_equiv (R S : AbstractRing) : Equiv (Id AbstractRing R S) (RingIso R S)
  ≔ (ring_path_to_iso R S, ring_path_to_iso_is_equiv R S)

def ring_paths_set (R S : AbstractRing) : isSet (Id AbstractRing R S)
  ≔ hlevel_two_to_set (Id AbstractRing R S)
      (hlevel_equiv (suc. (suc. zero.)) (RingIso R S) (Id AbstractRing R S)
        (canonical_inverse_equiv (Id AbstractRing R S) (RingIso R S) (ring_path_iso_equiv R S))
        (set_to_hlevel_two (RingIso R S) (ring_iso_set R S)))

def ring_groupoid : isGroupoid AbstractRing ≔ R S ↦ ring_paths_set R S

{` Fields. IsField is a proposition, so identifications of fields are
   identifications of the underlying rings. `}
def is_field_prop (R : AbstractRing) : isProp (IsField R)
  ≔ product_prop (IsNonTrivialCRing R) (BookIsContr (NonInvertibles R))
      (product_prop (IsCommutativeRing R) (IsNonTrivialRing R) (is_commutative_ring_prop R) (is_non_trivial_ring_prop R))
      (book_iscontr_isprop (NonInvertibles R))

{` The book's Iso(K, L) for fields K, L. `}
def FieldIso (K L : Field) : Type ≔ RingIso (K .fst) (L .fst)

def field_path_to_iso (K L : Field) (p : Id Field K L) : FieldIso K L ≔ ring_path_to_iso (K .fst) (L .fst) (p .fst)

def field_path_from_iso (K L : Field) (φ : FieldIso K L) : Id Field K L
  ≔ let r ≔ ring_path_from_iso (K .fst) (L .fst) φ in
    (r, pathover_hlevel zero. AbstractRing IsField (R ↦ prop_to_hlevel_one (IsField R) (is_field_prop R))
          (K .fst) (L .fst) r (K .snd) (L .snd) .center)

{` rem:sip-univalence, principal statement: (K = L) ≃ Iso(K, L); the map
   sends p to transport along the carrier of p. `}
def field_path_iso_equiv (K L : Field) : Equiv (Id Field K L) (FieldIso K L)
  ≔ compose_equiv (Id Field K L) (Id AbstractRing (K .fst) (L .fst)) (FieldIso K L)
      (subtype_path_equiv AbstractRing IsField is_field_prop K L)
      (ring_path_iso_equiv (K .fst) (L .fst))

def field_path_iso_equiv_map (K L : Field) (p : Id Field K L)
  : Id (FieldIso K L) (field_path_iso_equiv K L .map p) (field_path_to_iso K L p)
  ≔ refl (field_path_to_iso K L p)

def field_iso_path_section (K L : Field) (φ : FieldIso K L)
  : Id (FieldIso K L) (field_path_to_iso K L (field_path_from_iso K L φ)) φ
  ≔ ring_iso_path_section (K .fst) (L .fst) φ

{` Litmus: transport along the identification given by φ is φ, by computation. `}
def field_path_from_iso_transport (K L : Field) (φ : FieldIso K L) (x : field_carrier K)
  : Id (field_carrier L) (field_path_from_iso K L φ .fst .carrier .trr x) (φ .fst .map x)
  ≔ refl (φ .fst .map x)

def field_paths_set (K L : Field) : isSet (Id Field K L)
  ≔ hlevel_two_to_set (Id Field K L)
      (hlevel_equiv (suc. (suc. zero.)) (FieldIso K L) (Id Field K L)
        (canonical_inverse_equiv (Id Field K L) (FieldIso K L) (field_path_iso_equiv K L))
        (set_to_hlevel_two (FieldIso K L) (ring_iso_set (K .fst) (L .fst))))

{` The type Fields of the book is a groupoid. `}
def fields_groupoid : isGroupoid Field ≔ K L ↦ field_paths_set K L

{` rem:sip-univalence, the transport formulas. Any p : K =_U L is ua(φ)
   for φ = id_to_equiv(p); along ua(φ) transport of the operations is
   conjugation by φ, by computation (φ⁻¹ = equiv_inverse_map, see ua_trl).
   For a general p the same formulas hold with p .trr, p .trl. `}
def field_transport_add_ua (K L : Field) (φ : Equiv (field_carrier K) (field_carrier L))
  : Id (field_carrier L → field_carrier L → field_carrier L)
      (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L)
        (ua (field_carrier K) (field_carrier L) φ) (K .fst .add))
      (x y ↦ φ .map (K .fst .add (equiv_inverse_map (field_carrier K) (field_carrier L) φ x)
                                 (equiv_inverse_map (field_carrier K) (field_carrier L) φ y)))
  ≔ refl (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L)
        (ua (field_carrier K) (field_carrier L) φ) (K .fst .add))

def field_transport_mul_ua (K L : Field) (φ : Equiv (field_carrier K) (field_carrier L))
  : Id (field_carrier L → field_carrier L → field_carrier L)
      (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L)
        (ua (field_carrier K) (field_carrier L) φ) (K .fst .mul))
      (x y ↦ φ .map (K .fst .mul (equiv_inverse_map (field_carrier K) (field_carrier L) φ x)
                                 (equiv_inverse_map (field_carrier K) (field_carrier L) φ y)))
  ≔ refl (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L)
        (ua (field_carrier K) (field_carrier L) φ) (K .fst .mul))

def field_transport_zero_ua (K L : Field) (φ : Equiv (field_carrier K) (field_carrier L))
  : Id (field_carrier L)
      (transport Type (X ↦ X) (field_carrier K) (field_carrier L) (ua (field_carrier K) (field_carrier L) φ) (K .fst .zero))
      (φ .map (K .fst .zero))
  ≔ refl (φ .map (K .fst .zero))

def field_transport_one_ua (K L : Field) (φ : Equiv (field_carrier K) (field_carrier L))
  : Id (field_carrier L)
      (transport Type (X ↦ X) (field_carrier K) (field_carrier L) (ua (field_carrier K) (field_carrier L) φ) (K .fst .one))
      (φ .map (K .fst .one))
  ≔ refl (φ .map (K .fst .one))

def field_transport_add (K L : Field) (P : Id Type (field_carrier K) (field_carrier L))
  : Id (field_carrier L → field_carrier L → field_carrier L)
      (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L) P (K .fst .add))
      (x y ↦ P .trr (K .fst .add (P .trl x) (P .trl y)))
  ≔ refl (transport Type (X ↦ X → X → X) (field_carrier K) (field_carrier L) P (K .fst .add))

{` Round trips of transport along a path of types. `}
def type_path_trr_trl (A B : Type) (e : Id Type A B) (b : B) : Id B (e .trr (e .trl b)) b
  ≔ J Type A (B' e' ↦ (b' : B') → Id B' (e' .trr (e' .trl b')) b')
      (b' ↦ concat A (refl A .trr (refl A .trl b')) (refl A .trl b') b'
         (inverse A (refl A .trl b') (refl A .trr (refl A .trl b')) (refl A .liftr (refl A .trl b')))
         (refl A .liftl b')) B e b

{` The same statement as type_path_trl_trr of module 586 (chapter 5), which
   is outside this import closure. `}
def carrier_path_trl_trr (A B : Type) (e : Id Type A B) (a : A) : Id A (e .trl (e .trr a)) a
  ≔ J Type A (B' e' ↦ (a' : A) → Id A (e' .trl (e' .trr a')) a')
      (a' ↦ concat A (refl A .trl (refl A .trr a')) (refl A .trr a') a' (refl A .liftl (refl A .trr a'))
         (inverse A a' (refl A .trr a') (refl A .liftr a'))) B e a

{` The middle step of rem:sip-univalence:
   (K = L) ≃ Σ_{p : K =_U L} (trp_p(+_K) = +_L) × (trp_p(·_K) = ·_L) × (trp_p(0_K) = 0_L) × (trp_p(1_K) = 1_L). `}
def FieldTransportStructure (K L : Field) (P : Id Type (field_carrier K) (field_carrier L)) : Type
  ≔ let A ≔ field_carrier K in let T ≔ field_carrier L in
    Product (Id (T → T → T) (transport Type (X ↦ X → X → X) A T P (K .fst .add)) (L .fst .add))
      (Product (Id (T → T → T) (transport Type (X ↦ X → X → X) A T P (K .fst .mul)) (L .fst .mul))
        (Product (Id T (transport Type (X ↦ X) A T P (K .fst .zero)) (L .fst .zero))
          (Id T (transport Type (X ↦ X) A T P (K .fst .one)) (L .fst .one))))

def field_binop_set (L : Field) : isSet (field_carrier L → field_carrier L → field_carrier L)
  ≔ pi_set (field_carrier L) (_ ↦ field_carrier L → field_carrier L)
      (_ ↦ pi_set (field_carrier L) (_ ↦ field_carrier L) (_ ↦ ring_set (L .fst)))

def field_transport_structure_prop (K L : Field) (P : Id Type (field_carrier K) (field_carrier L))
  : isProp (FieldTransportStructure K L P)
  ≔ let A ≔ field_carrier K in let T ≔ field_carrier L in let hT ≔ ring_set (L .fst) in
    let hB ≔ field_binop_set L in
    product_prop (Id (T → T → T) (transport Type (X ↦ X → X → X) A T P (K .fst .add)) (L .fst .add))
      (Product (Id (T → T → T) (transport Type (X ↦ X → X → X) A T P (K .fst .mul)) (L .fst .mul))
        (Product (Id T (transport Type (X ↦ X) A T P (K .fst .zero)) (L .fst .zero))
          (Id T (transport Type (X ↦ X) A T P (K .fst .one)) (L .fst .one))))
      (hB (transport Type (X ↦ X → X → X) A T P (K .fst .add)) (L .fst .add))
      (product_prop (Id (T → T → T) (transport Type (X ↦ X → X → X) A T P (K .fst .mul)) (L .fst .mul))
        (Product (Id T (transport Type (X ↦ X) A T P (K .fst .zero)) (L .fst .zero))
          (Id T (transport Type (X ↦ X) A T P (K .fst .one)) (L .fst .one)))
        (hB (transport Type (X ↦ X → X → X) A T P (K .fst .mul)) (L .fst .mul))
        (product_prop (Id T (transport Type (X ↦ X) A T P (K .fst .zero)) (L .fst .zero))
          (Id T (transport Type (X ↦ X) A T P (K .fst .one)) (L .fst .one))
          (hT (transport Type (X ↦ X) A T P (K .fst .zero)) (L .fst .zero))
          (hT (transport Type (X ↦ X) A T P (K .fst .one)) (L .fst .one))))

{` A binary operation transported along P agrees with the target operation
   iff P .trr is a homomorphism for it. `}
def transported_binop_to_hom (A T : Type) (P : Id Type A T) (m : A → A → A) (n : T → T → T)
  (h : Id (T → T → T) (transport Type (X ↦ X → X → X) A T P m) n) (x y : A)
  : Id T (P .trr (m x y)) (n (P .trr x) (P .trr y))
  ≔ concat T (P .trr (m x y)) (P .trr (m (P .trl (P .trr x)) (P .trl (P .trr y)))) (n (P .trr x) (P .trr y))
      (refl (P .trr) (refl m (inverse A (P .trl (P .trr x)) x (carrier_path_trl_trr A T P x))
                             (inverse A (P .trl (P .trr y)) y (carrier_path_trl_trr A T P y))))
      (h (refl (P .trr x)) (refl (P .trr y)))

def hom_to_transported_binop (A T : Type) (P : Id Type A T) (m : A → A → A) (n : T → T → T)
  (h : (x y : A) → Id T (P .trr (m x y)) (n (P .trr x) (P .trr y)))
  : Id (T → T → T) (transport Type (X ↦ X → X → X) A T P m) n
  ≔ funext T (_ ↦ T → T) (transport Type (X ↦ X → X → X) A T P m) n
      (u ↦ funext T (_ ↦ T) (transport Type (X ↦ X → X → X) A T P m u) (n u)
        (v ↦ concat T (P .trr (m (P .trl u) (P .trl v))) (n (P .trr (P .trl u)) (P .trr (P .trl v))) (n u v)
           (h (P .trl u) (P .trl v))
           (refl n (type_path_trr_trl A T P u) (type_path_trr_trl A T P v))))

def field_transport_structure_to_laws (K L : Field) (P : Id Type (field_carrier K) (field_carrier L))
  (t : FieldTransportStructure K L P) : RingIsoLaws (K .fst) (L .fst) (P .trr)
  ≔ let A ≔ field_carrier K in let T ≔ field_carrier L in
    (transported_binop_to_hom A T P (K .fst .add) (L .fst .add) (t .fst),
     (transported_binop_to_hom A T P (K .fst .mul) (L .fst .mul) (t .snd .fst),
      (t .snd .snd .fst, t .snd .snd .snd)))

def field_laws_to_transport_structure (K L : Field) (P : Id Type (field_carrier K) (field_carrier L))
  (l : RingIsoLaws (K .fst) (L .fst) (P .trr)) : FieldTransportStructure K L P
  ≔ let A ≔ field_carrier K in let T ≔ field_carrier L in
    (hom_to_transported_binop A T P (K .fst .add) (L .fst .add) (l .fst),
     (hom_to_transported_binop A T P (K .fst .mul) (L .fst .mul) (l .snd .fst),
      (l .snd .snd .fst, l .snd .snd .snd)))

def field_transport_structure_iso_equiv (K L : Field)
  : Equiv (Σ (Id Type (field_carrier K) (field_carrier L)) (FieldTransportStructure K L)) (FieldIso K L)
  ≔ let A ≔ field_carrier K in let T ≔ field_carrier L in
    compose_equiv (Σ (Id Type A T) (FieldTransportStructure K L))
      (Σ (Id Type A T) (P ↦ RingIsoLaws (K .fst) (L .fst) (transport_univalence_equiv A T .map P .map)))
      (FieldIso K L)
      (family_equiv (Id Type A T) (FieldTransportStructure K L)
        (P ↦ RingIsoLaws (K .fst) (L .fst) (transport_univalence_equiv A T .map P .map))
        (P ↦ iff_equiv (FieldTransportStructure K L P) (RingIsoLaws (K .fst) (L .fst) (P .trr))
           (field_transport_structure_prop K L P) (ring_iso_laws_prop (K .fst) (L .fst) (P .trr))
           (field_transport_structure_to_laws K L P) (field_laws_to_transport_structure K L P)))
      (sigma_reindex_equiv (Id Type A T) (Equiv A T) (transport_univalence_equiv A T)
        (f ↦ RingIsoLaws (K .fst) (L .fst) (f .map)))

def field_path_transport_structure_equiv (K L : Field)
  : Equiv (Id Field K L) (Σ (Id Type (field_carrier K) (field_carrier L)) (FieldTransportStructure K L))
  ≔ compose_equiv (Id Field K L) (FieldIso K L)
      (Σ (Id Type (field_carrier K) (field_carrier L)) (FieldTransportStructure K L))
      (field_path_iso_equiv K L)
      (canonical_inverse_equiv (Σ (Id Type (field_carrier K) (field_carrier L)) (FieldTransportStructure K L))
        (FieldIso K L) (field_transport_structure_iso_equiv K L))

{` Litmus: the identity of a field is an isomorphism; ring_path_to_iso of
   refl has the identity as its map up to the transport along refl. `}
def field_iso_id (K : Field) : FieldIso K K ≔ ring_iso_id (K .fst)

def f2_iso_id_map (b : Bool) : Id Bool (field_iso_id f2_field .fst .map b) b ≔ refl b
