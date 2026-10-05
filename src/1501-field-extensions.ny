export "1500-field-identity"

{` Chapter 15 (galois.tex), section "Covering spaces and field
   extensions". A field extension of k is a field homomorphism i : k → K
   (homomorphisms of fields are ring homomorphisms, def:ringhom); the type
   of extensions of k is k\Fields ≔ Σ_{K : Fields} hom(k, K) (FieldExt).
   Identifications (L, j) = (L', j') are isomorphisms φ : L ≅ L' with
   φ ∘ j = j' (field_ext_path_equiv), so k\Fields is a groupoid and the
   Galois group Gal(K, i) ≔ Aut_{k\Fields}(K, i) (def:galois-group) is a
   group. rem:sip-univalence, last display: USym Gal(K, i) ≃ Σ_{p : K = K}
   trp_p(i) = i ≃ Σ_{σ : Iso(K, K)} σ ∘ i = i. Composition j ∘ i is written
   ring_hom_compose k K L i j (i first), the book's ji. `}

def FieldExt (k : Field) : Type ≔ Σ Field (K ↦ RingHom (k .fst) (K .fst))

def field_ext_field (k : Field) (E : FieldExt k) : Field ≔ E .fst

def field_ext_hom (k : Field) (E : FieldExt k) : RingHom (k .fst) (E .fst .fst) ≔ E .snd

{` φ ∘ j for an isomorphism φ : L ≅ L' and j : k → L. `}
def field_iso_after (k L L' : Field) (j : RingHom (k .fst) (L .fst)) (φ : FieldIso L L') : RingHom (k .fst) (L' .fst)
  ≔ ring_hom_compose (k .fst) (L .fst) (L' .fst) j (ring_iso_hom (L .fst) (L' .fst) φ)

{` Isomorphisms of extensions: φ : L ≅ L' with φ ∘ j = j'. `}
def FieldExtIso (k : Field) (E F : FieldExt k) : Type
  ≔ Σ (FieldIso (E .fst) (F .fst)) (φ ↦ Id (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd))

def field_ext_iso_set (k : Field) (E F : FieldExt k) : isSet (FieldExtIso k E F)
  ≔ sigma_set (FieldIso (E .fst) (F .fst))
      (φ ↦ Id (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd))
      (ring_iso_set (E .fst .fst) (F .fst .fst))
      (φ ↦ prop_is_set (Id (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd))
        (ring_hom_set (k .fst) (F .fst .fst) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd)))

{` Transport of a homomorphism j : k → K along p : K = L is, pointwise,
   transport along the carrier of p (up to the transport of k along refl). `}
def refl_type_trl (A : Type) (x : A) : Id A (refl A .trl x) x ≔ refl A .liftl x

def ext_hom_transport_compare (k K L : Field) (p : Id Field K L) (j : RingHom (k .fst) (K .fst))
  : Id (RingHom (k .fst) (L .fst))
      (field_iso_after k K L j (field_path_to_iso K L p))
      (transport Field (X ↦ RingHom (k .fst) (X .fst)) K L p j)
  ≔ ring_hom_ext (k .fst) (L .fst)
      (field_iso_after k K L j (field_path_to_iso K L p))
      (transport Field (X ↦ RingHom (k .fst) (X .fst)) K L p j)
      (x ↦ refl ((y ↦ p .fst .carrier .trr (j .fst .fst y)) : k .fst .carrier → L .fst .carrier)
             (inverse (k .fst .carrier) (refl (k .fst .carrier) .trl x) x (refl_type_trl (k .fst .carrier) x)))

{` For p : K = L: (j = j' over p) ≃ (φ_p ∘ j = j'). `}
def ext_hom_pathover_equiv (k K L : Field) (p : Id Field K L) (j : RingHom (k .fst) (K .fst)) (j' : RingHom (k .fst) (L .fst))
  : Equiv (Id (X ↦ RingHom (k .fst) (X .fst)) p j j')
      (Id (RingHom (k .fst) (L .fst)) (field_iso_after k K L j (field_path_to_iso K L p)) j')
  ≔ let H ≔ RingHom (k .fst) (L .fst) in
    let a ≔ field_iso_after k K L j (field_path_to_iso K L p) in
    let t ≔ transport Field (X ↦ RingHom (k .fst) (X .fst)) K L p j in
    let c ≔ ext_hom_transport_compare k K L p j in
    compose_equiv (Id (X ↦ RingHom (k .fst) (X .fst)) p j j') (Id H t j') (Id H a j')
      (pathover_transport_equiv Field (X ↦ RingHom (k .fst) (X .fst)) K L p j j')
      (iff_equiv (Id H t j') (Id H a j') (ring_hom_set (k .fst) (L .fst) t j') (ring_hom_set (k .fst) (L .fst) a j')
        (h ↦ concat H a t j' c h) (h ↦ concat H t a j' (inverse H a t c) h))

{` (E = F) ≃ FieldExtIso k E F: an identification of extensions is an
   isomorphism φ of the fields with φ ∘ j = j'. The map sends r to
   (transport along the carrier of r .fst, _). `}
def field_ext_path_equiv (k : Field) (E F : FieldExt k) : Equiv (Id (FieldExt k) E F) (FieldExtIso k E F)
  ≔ let B ≔ (X ↦ RingHom (k .fst) (X .fst)) : Field → Type in
    let K ≔ E .fst in let L ≔ F .fst in
    let C ≔ (φ ↦ Id (RingHom (k .fst) (L .fst)) (field_iso_after k K L (E .snd) φ) (F .snd)) : FieldIso K L → Type in
    compose_equiv (Id (FieldExt k) E F) (SigmaPath Field B E F) (FieldExtIso k E F)
      (canonical_inverse_equiv (SigmaPath Field B E F) (Id (FieldExt k) E F) (sigma_path_equiv Field B E F))
      (compose_equiv (SigmaPath Field B E F) (Σ (Id Field K L) (p ↦ C (field_path_iso_equiv K L .map p)))
        (FieldExtIso k E F)
        (family_equiv (Id Field K L) (p ↦ Id B p (E .snd) (F .snd)) (p ↦ C (field_path_iso_equiv K L .map p))
          (p ↦ ext_hom_pathover_equiv k K L p (E .snd) (F .snd)))
        (sigma_reindex_equiv (Id Field K L) (FieldIso K L) (field_path_iso_equiv K L) C))

def field_ext_paths_set (k : Field) (E F : FieldExt k) : isSet (Id (FieldExt k) E F)
  ≔ hlevel_two_to_set (Id (FieldExt k) E F)
      (hlevel_equiv (suc. (suc. zero.)) (FieldExtIso k E F) (Id (FieldExt k) E F)
        (canonical_inverse_equiv (Id (FieldExt k) E F) (FieldExtIso k E F) (field_ext_path_equiv k E F))
        (set_to_hlevel_two (FieldExtIso k E F) (field_ext_iso_set k E F)))

{` k\Fields is a groupoid. `}
def field_ext_groupoid (k : Field) : isGroupoid (FieldExt k) ≔ E F ↦ field_ext_paths_set k E F

{` def:galois-group. Gal(K, i) ≔ Aut_{k\Fields}(K, i). `}
def galois_group (k : Field) (E : FieldExt k) : Group ≔ automorphism_group (FieldExt k) (field_ext_groupoid k) E

{` rem:sip-univalence, last display, second form: USym Gal(K, i) ≃ Σ_{σ : Iso(K, K)} σ ∘ i = i
   (the k-automorphisms of K, "how the Galois group is defined in ordinary mathematics"). `}
def galois_usym_kaut_equiv (k : Field) (E : FieldExt k) : Equiv (USym (galois_group k E)) (FieldExtIso k E E)
  ≔ compose_equiv (USym (galois_group k E)) (Id (FieldExt k) E E) (FieldExtIso k E E)
      (automorphism_group_usym_equiv (FieldExt k) (field_ext_groupoid k) E)
      (field_ext_path_equiv k E E)

{` rem:sip-univalence, last display, first form: USym Gal(K, i) ≃ Σ_{p : K = K} trp_p(i) = i. `}
def GaloisTransportForm (k : Field) (E : FieldExt k) : Type
  ≔ Σ (Id Field (E .fst) (E .fst)) (p ↦ Id (RingHom (k .fst) (E .fst .fst))
      (transport Field (X ↦ RingHom (k .fst) (X .fst)) (E .fst) (E .fst) p (E .snd)) (E .snd))

def galois_usym_transport_equiv (k : Field) (E : FieldExt k) : Equiv (USym (galois_group k E)) (GaloisTransportForm k E)
  ≔ let B ≔ (X ↦ RingHom (k .fst) (X .fst)) : Field → Type in
    let K ≔ E .fst in
    compose_equiv (USym (galois_group k E)) (Id (FieldExt k) E E) (GaloisTransportForm k E)
      (automorphism_group_usym_equiv (FieldExt k) (field_ext_groupoid k) E)
      (compose_equiv (Id (FieldExt k) E E) (SigmaPath Field B E E) (GaloisTransportForm k E)
        (canonical_inverse_equiv (SigmaPath Field B E E) (Id (FieldExt k) E E) (sigma_path_equiv Field B E E))
        (family_equiv (Id Field K K) (p ↦ Id B p (E .snd) (E .snd))
          (p ↦ Id (RingHom (k .fst) (K .fst)) (transport Field B K K p (E .snd)) (E .snd))
          (p ↦ pathover_transport_equiv Field B K K p (E .snd) (E .snd))))

{` Litmus: the identity extension (K, id_K) has trivial Galois group; its
   only k-automorphism is the identity. `}
def identity_extension (K : Field) : FieldExt K ≔ (K, ring_hom_id (K .fst))

def identity_ext_kaut_center (K : Field) : FieldExtIso K (identity_extension K) (identity_extension K)
  ≔ (field_iso_id K,
     ring_hom_ext (K .fst) (K .fst) (field_iso_after K K K (ring_hom_id (K .fst)) (field_iso_id K)) (ring_hom_id (K .fst))
       (x ↦ refl x))

def identity_ext_kaut_contractible (K : Field) : isContr (FieldExtIso K (identity_extension K) (identity_extension K))
  ≔ let R ≔ K .fst in let A ≔ R .carrier in
    let P ≔ (φ ↦ Id (RingHom R R) (field_iso_after K K K (ring_hom_id R) φ) (ring_hom_id R)) : FieldIso K K → Type in
    (identity_ext_kaut_center K,
     u ↦ subtype_equal (FieldIso K K) P (φ ↦ ring_hom_set R R (field_iso_after K K K (ring_hom_id R) φ) (ring_hom_id R))
       u (identity_ext_kaut_center K)
       (ring_iso_path R R (u .fst) (field_iso_id K)
         (funext A (_ ↦ A) (u .fst .fst .map) (x ↦ x)
           (x ↦ refl ((φ ↦ φ .fst .fst x) : RingHom R R → A) (u .snd)))))

def galois_identity_extension_trivial (K : Field) : isContr (USym (galois_group K (identity_extension K)))
  ≔ let E ≔ identity_extension K in
    let e ≔ galois_usym_kaut_equiv K E in
    contractible_retract (FieldExtIso K E E) (USym (galois_group K E)) (identity_ext_kaut_contractible K)
      (equiv_inverse_map (USym (galois_group K E)) (FieldExtIso K E E) e) (e .map)
      (g ↦ inverse (USym (galois_group K E)) g (equiv_inverse_map (USym (galois_group K E)) (FieldExtIso K E E) e (e .map g))
         (equiv_unit (USym (galois_group K E)) (FieldExtIso K E E) e g))
