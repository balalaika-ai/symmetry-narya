export "1501-field-extensions"

{` Chapter 15 (galois.tex), section "Covering spaces and field
   extensions", after rem:sip-univalence. For an extension (K, i) of k the
   restriction map restr_i : K\Fields → k\Fields, (L, j) ↦ (L, j i), is a
   set bundle (lem:field-ext-restriction-set-bundle). The running text
   computes its fiber at an extension (L, j) of k:
     fiber ≃ Σ_{L'} Σ_{j' : K → L'} (L, j) = (L', j' i)
           ≃ Σ_{L'} Σ_{j'} Σ_{p : L = L'} p j = j' i
           ≃ Σ_{j' : K → L} j = j' i ≃ hom_k(K, L)
   (KAlgHom, the k-algebra homomorphisms; restriction_fiber_kalg_equiv).
   The proof here goes through this fiber computation; the middle steps are
   the computation of identifications in a Σ-type (Id of a Σ-type is the
   Σ of a path and a dependent path) and contract_away for (L', p).
   The map t : USym Gal(K, i) → fiber over (K, i), g ↦ trp_g(id_K),
   corresponds to the inclusion of the k-automorphisms into the
   k-endomorphisms (galois_t_identification). `}

def field_ext_restriction (k : Field) (E : FieldExt k) (F : FieldExt (E .fst)) : FieldExt k
  ≔ (F .fst, ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) (F .snd))

{` hom_k(K, L) for extensions (K, i), (L, j) of k: Σ_{j' : K → L} j = j' i. `}
def KAlgHom (k : Field) (E F : FieldExt k) : Type
  ≔ Σ (RingHom (E .fst .fst) (F .fst .fst)) (j' ↦
      Id (RingHom (k .fst) (F .fst .fst)) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))

def kalg_hom_set (k : Field) (E F : FieldExt k) : isSet (KAlgHom k E F)
  ≔ sigma_set (RingHom (E .fst .fst) (F .fst .fst))
      (j' ↦ Id (RingHom (k .fst) (F .fst .fst)) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))
      (ring_hom_set (E .fst .fst) (F .fst .fst))
      (j' ↦ prop_is_set (Id (RingHom (k .fst) (F .fst .fst)) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))
        (ring_hom_set (k .fst) (F .fst .fst) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j')))

def kalg_hom_path (k : Field) (E F : FieldExt k) (φ ψ : KAlgHom k E F)
  (h : (x : E .fst .fst .carrier) → Id (F .fst .fst .carrier) (φ .fst .fst .fst x) (ψ .fst .fst .fst x))
  : Id (KAlgHom k E F) φ ψ
  ≔ subtype_equal (RingHom (E .fst .fst) (F .fst .fst))
      (j' ↦ Id (RingHom (k .fst) (F .fst .fst)) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))
      (j' ↦ ring_hom_set (k .fst) (F .fst .fst) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))
      φ ψ (ring_hom_ext (E .fst .fst) (F .fst .fst) (φ .fst) (ψ .fst) h)

{` A dependent identification over P : S = T relates u to the backward transport of v. `}
def type_pathover_trl (S T : Type) (P : Id Type S T) (u : S) (v : T) (r : P u v) : Id S u (P .trl v)
  ≔ J Type S (T' P' ↦ (u' : S) (v' : T') (r' : P' u' v') → Id S u' (P' .trl v'))
      (u' v' r' ↦ concat S u' v' (refl S .trl v') r' (inverse S (refl S .trl v') v' (refl S .liftl v')))
      T P u v r

{` The map fiber → hom_k(K, L): ((L', j'), q) ↦ j' transported back along q. `}
def restriction_fiber_to_kalg (k : Field) (E F : FieldExt k)
  (u : BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F) : KAlgHom k E F
  ≔ let K ≔ E .fst in let L ≔ F .fst in let G ≔ u .fst in let q ≔ u .snd in
    let i ≔ E .snd .fst .fst in let j ≔ F .snd .fst .fst in let g ≔ G .snd .fst .fst in
    let Kc ≔ K .fst .carrier in let Lc ≔ L .fst .carrier in
    let P ≔ q .fst .fst .carrier in
    let T ≔ refl ((X ↦ RingHom (K .fst) (X .fst)) : Field → Type) (q .fst) .trl (G .snd) in
    (T, ring_hom_ext (k .fst) (L .fst) (F .snd) (ring_hom_compose (k .fst) (K .fst) (L .fst) (E .snd) T)
          (a ↦ concat Lc (j a) (P .trl (g (i a))) (P .trl (g (refl Kc .trr (i a))))
                 (type_pathover_trl Lc (G .fst .fst .carrier) P (j a) (g (i a)) (q .snd .fst .fst (refl a)))
                 (refl ((y ↦ P .trl (g y)) : Kc → Lc) (refl Kc .liftr (i a)))))

def restriction_fiber_family (k : Field) (E F : FieldExt k) (L' : Field) (q1 : Id Field (F .fst) L') : Type
  ≔ Σ (RingHom (E .fst .fst) (L' .fst)) (j' ↦
      Id ((X ↦ RingHom (k .fst) (X .fst)) : Field → Type) q1 (F .snd)
        (ring_hom_compose (k .fst) (E .fst .fst) (L' .fst) (E .snd) j'))

def restriction_fiber_reshuffle (k : Field) (E F : FieldExt k)
  : Equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
      (Σ Field (L' ↦ Σ (Id Field (F .fst) L') (restriction_fiber_family k E F L')))
  ≔ quasi_inverse_equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
      (Σ Field (L' ↦ Σ (Id Field (F .fst) L') (restriction_fiber_family k E F L')))
      (u ↦ (u .fst .fst, (u .snd .fst, (u .fst .snd, u .snd .snd))))
      (t ↦ ((t .fst, t .snd .snd .fst), (t .snd .fst, t .snd .snd .snd)))
      (u ↦ refl u) (t ↦ refl t)

def restriction_fiber_contract_equiv (k : Field) (E F : FieldExt k)
  : Equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F) (KAlgHom k E F)
  ≔ compose_equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
      (Σ Field (L' ↦ Σ (Id Field (F .fst) L') (restriction_fiber_family k E F L')))
      (KAlgHom k E F)
      (restriction_fiber_reshuffle k E F)
      (contract_away_equiv Field (F .fst) (restriction_fiber_family k E F))

def restriction_fiber_compare_base (k : Field) (E F : FieldExt k)
  (j' : RingHom (E .fst .fst) (F .fst .fst))
  (q2 : Id (RingHom (k .fst) (F .fst .fst)) (F .snd) (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j'))
  : Id (KAlgHom k E F)
      (contract_away_map Field (F .fst) (restriction_fiber_family k E F) (F .fst) (refl (F .fst)) (j', q2))
      (restriction_fiber_to_kalg k E F ((F .fst, j'), (refl (F .fst), q2)))
  ≔ let Kc ≔ E .fst .fst .carrier in let Lc ≔ F .fst .fst .carrier in
    concat (KAlgHom k E F)
      (contract_away_map Field (F .fst) (restriction_fiber_family k E F) (F .fst) (refl (F .fst)) (j', q2))
      (j', q2)
      (restriction_fiber_to_kalg k E F ((F .fst, j'), (refl (F .fst), q2)))
      (contract_away_beta Field (F .fst) (restriction_fiber_family k E F) (j', q2))
      (kalg_hom_path k E F (j', q2) (restriction_fiber_to_kalg k E F ((F .fst, j'), (refl (F .fst), q2)))
        (x ↦ concat Lc (j' .fst .fst x) (j' .fst .fst (refl Kc .trr x)) (refl Lc .trl (j' .fst .fst (refl Kc .trr x)))
               (refl (j' .fst .fst) (refl Kc .liftr x))
               (inverse Lc (refl Lc .trl (j' .fst .fst (refl Kc .trr x))) (j' .fst .fst (refl Kc .trr x))
                 (refl Lc .liftl (j' .fst .fst (refl Kc .trr x))))))

def restriction_fiber_compare (k : Field) (E F : FieldExt k) (L' : Field) (q1 : Id Field (F .fst) L')
  : (t : restriction_fiber_family k E F L' q1)
    → Id (KAlgHom k E F)
        (contract_away_map Field (F .fst) (restriction_fiber_family k E F) L' q1 t)
        (restriction_fiber_to_kalg k E F ((L', t .fst), (q1, t .snd)))
  ≔ J Field (F .fst)
      (L'' q'' ↦ (t : restriction_fiber_family k E F L'' q'')
         → Id (KAlgHom k E F)
             (contract_away_map Field (F .fst) (restriction_fiber_family k E F) L'' q'' t)
             (restriction_fiber_to_kalg k E F ((L'', t .fst), (q'', t .snd))))
      (t ↦ restriction_fiber_compare_base k E F (t .fst) (t .snd)) L' q1

{` The fiber of restr_i over (L, j) is hom_k(K, L) (running text after
   lem:field-ext-restriction-set-bundle); the map is restriction_fiber_to_kalg. `}
def restriction_fiber_kalg_equiv (k : Field) (E F : FieldExt k)
  : Equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F) (KAlgHom k E F)
  ≔ equiv_change_map (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F) (KAlgHom k E F)
      (restriction_fiber_contract_equiv k E F) (restriction_fiber_to_kalg k E F)
      (u ↦ restriction_fiber_compare k E F (u .fst .fst) (u .snd .fst) (u .fst .snd, u .snd .snd))

{` lem:field-ext-restriction-set-bundle: restr_i is a set bundle (covering). `}
def field_ext_restriction_set_bundle (k : Field) (E : FieldExt k)
  : IsCovering (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E)
  ≔ F ↦ hlevel_two_to_set (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
      (hlevel_equiv (suc. (suc. zero.)) (KAlgHom k E F)
        (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
        (canonical_inverse_equiv (BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F)
          (KAlgHom k E F) (restriction_fiber_kalg_equiv k E F))
        (set_to_hlevel_two (KAlgHom k E F) (kalg_hom_set k E F)))

{` The inclusion of k-isomorphisms (k-automorphisms for E = F) into k-homomorphisms. `}
def kaut_to_kalg (k : Field) (E F : FieldExt k) (σ : FieldExtIso k E F) : KAlgHom k E F
  ≔ (ring_iso_hom (E .fst .fst) (F .fst .fst) (σ .fst),
     inverse (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) (σ .fst)) (F .snd) (σ .snd))

def kaut_to_kalg_embedding (k : Field) (E F : FieldExt k)
  : IsEmbedding (FieldExtIso k E F) (KAlgHom k E F) (kaut_to_kalg k E F)
  ≔ path_reflecting_set_embedding (FieldExtIso k E F) (KAlgHom k E F) (kalg_hom_set k E F) (kaut_to_kalg k E F)
      (σ τ e ↦ subtype_equal (FieldIso (E .fst) (F .fst))
         (φ ↦ Id (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd))
         (φ ↦ ring_hom_set (k .fst) (F .fst .fst) (field_iso_after k (E .fst) (F .fst) (E .snd) φ) (F .snd))
         σ τ
         (ring_iso_path (E .fst .fst) (F .fst .fst) (σ .fst) (τ .fst)
           (refl ((ψ ↦ ψ .fst .fst .fst) : KAlgHom k E F → (E .fst .fst .carrier → F .fst .fst .carrier)) e)))

{` id_K as a point of the fiber of restr_i over (K, i). `}
def restriction_identity_point (k : Field) (E : FieldExt k)
  : BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) E
  ≔ ((E .fst, ring_hom_id (E .fst .fst)),
     (refl (E .fst),
      ring_hom_ext (k .fst) (E .fst .fst) (E .snd)
        (ring_hom_compose (k .fst) (E .fst .fst) (E .fst .fst) (E .snd) (ring_hom_id (E .fst .fst)))
        (a ↦ refl (E .snd .fst .fst a))))

def restriction_fiber_over (k : Field) (E : FieldExt k) (F : FieldExt k) : Type
  ≔ BookFiber (FieldExt (E .fst)) (FieldExt k) (field_ext_restriction k E) F

{` t : USym Gal(K, i) → fiber over (K, i), g ↦ trp_g(id_K). `}
def galois_t (k : Field) (E : FieldExt k) (g : USym (galois_group k E)) : restriction_fiber_over k E E
  ≔ transport (FieldExt k) (restriction_fiber_over k E) E E
      (automorphism_group_usym_equiv (FieldExt k) (field_ext_groupoid k) E .map g) (restriction_identity_point k E)

def galois_t_general (k : Field) (E F : FieldExt k) (g : Id (FieldExt k) E F)
  : Id (KAlgHom k E F)
      (restriction_fiber_to_kalg k E F (transport (FieldExt k) (restriction_fiber_over k E) E F g (restriction_identity_point k E)))
      (kaut_to_kalg k E F (field_ext_path_equiv k E F .map g))
  ≔ J (FieldExt k) E
      (F' g' ↦ Id (KAlgHom k E F')
        (restriction_fiber_to_kalg k E F' (transport (FieldExt k) (restriction_fiber_over k E) E F' g' (restriction_identity_point k E)))
        (kaut_to_kalg k E F' (field_ext_path_equiv k E F' .map g')))
      (let Kc ≔ E .fst .fst .carrier in
       let pt ≔ restriction_identity_point k E in
       concat (KAlgHom k E E)
         (restriction_fiber_to_kalg k E E (transport (FieldExt k) (restriction_fiber_over k E) E E (refl E) pt))
         (restriction_fiber_to_kalg k E E pt)
         (kaut_to_kalg k E E (field_ext_path_equiv k E E .map (refl E)))
         (refl (restriction_fiber_to_kalg k E E) (transport_refl (FieldExt k) (restriction_fiber_over k E) E pt))
         (kalg_hom_path k E E (restriction_fiber_to_kalg k E E pt) (kaut_to_kalg k E E (field_ext_path_equiv k E E .map (refl E)))
           (x ↦ concat Kc (refl Kc .trl (refl Kc .trr x)) x (refl Kc .trr x)
                  (carrier_path_trl_trr Kc Kc (refl Kc) x) (refl Kc .liftr x))))
      F g

{` The square of the running text: under fiber ≃ hom_k(K, K) and
   USym Gal(K, i) ≃ Aut_k(K), t is the inclusion Aut_k(K) → End_k(K). `}
def galois_t_identification (k : Field) (E : FieldExt k) (g : USym (galois_group k E))
  : Id (KAlgHom k E E) (restriction_fiber_to_kalg k E E (galois_t k E g))
      (kaut_to_kalg k E E (galois_usym_kaut_equiv k E .map g))
  ≔ galois_t_general k E E (automorphism_group_usym_equiv (FieldExt k) (field_ext_groupoid k) E .map g)
