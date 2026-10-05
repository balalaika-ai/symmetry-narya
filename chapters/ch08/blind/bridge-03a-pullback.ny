export "03-pullback"
export "../../../src/823-pullback-group-homomorphisms"
export "../../../src/820-subset-intersections"
export "../../../src/822-pullback-group-symmetries"
export "../../../src/827-pullback-not-connected"
export "../../../src/223-constructed-circle"

{` Bridges for congp.tex, the pullback section: intersections and
   unions of subsets, xca:intersectionpullbackofsets, def:intersectionofgroups,
   xca 479 and the remark 497.

   Blind and our pullback groups have the same pointed type (BH ×_{BG} BH',
   point (sh, sh, p_f⁻¹ · p_f')) and differ only in the proof that it is a
   groupoid, a proposition; statements about them are transported along
   that proposition (bp_transport). The blind cardinality exercise assumes
   the four subsets finite; finiteness of a subset of a finite set gives its
   decidability (subset_finite_decidable), so ours applies, and cardinality
   does not depend on the finiteness proof. `}

{` def:intersectionand unionofsets: identical families. `}
def bridge_def_set_intersection (S : SetTypes) (P Q : Subtypes (S .fst))
  : Product (Id (Subtypes (S .fst)) (BlindSetIntersection S P Q) (SubsetIntersection (S .fst) P Q))
            (Id (Subtypes (S .fst)) (BlindSetUnion S P Q) (SubsetUnion (S .fst) P Q))
  ≔ (refl (SubsetIntersection (S .fst) P Q), refl (SubsetUnion (S .fst) P Q))

{` xca:intersectionpullbackofsets (1). `}
def bridge_xca_intersectionpullbackofsets : blind_xca_intersectionpullbackofsets
  ≔ S P Q ↦ (subset_pullback_intersection_book_equiv (S .fst) P Q,
      t ↦ inverse (S .fst) (t .fst .fst .fst) (t .fst .snd .fst) (t .snd))

{` xca:cardinalityintersectionunion (2). `}
def bp_card_irrelevant (A : Type) (h h' : IsFinite A) : Id Nat (cardinality A h) (cardinality A h')
  ≔ refl (cardinality A) (isfinite_prop A h h')

def bridge_xca_cardinalityintersectionunion : blind_xca_cardinalityintersectionunion
  ≔ S hS P Q hA hB hU hI ↦
    let T ≔ S .fst in
    let dP ≔ subset_finite_decidable T hS P hA in
    let dQ ≔ subset_finite_decidable T hS Q hB in
    let U ≔ SubsetUnion T P Q in let I ≔ SubsetIntersection T P Q in
    let hA' ≔ subset_finite T hS P dP in let hB' ≔ subset_finite T hS Q dQ in
    let hU' ≔ subset_finite T hS U (subset_union_decidable T P Q dP dQ) in
    let hI' ≔ subset_finite T hS I (subset_intersection_decidable T P Q dP dQ) in
    calc
      add (cardinality (SubtypeCarrier T P) hA) (cardinality (SubtypeCarrier T Q) hB)
      = add (cardinality (SubtypeCarrier T P) hA') (cardinality (SubtypeCarrier T Q) hB')
        by refl add (bp_card_irrelevant (SubtypeCarrier T P) hA hA') (bp_card_irrelevant (SubtypeCarrier T Q) hB hB')
      = add (cardinality (SubtypeCarrier T U) hU') (cardinality (SubtypeCarrier T I) hI')
        by subset_cardinality_union_intersection T hS P Q dP dQ
      = add (cardinality (SubtypeCarrier T U) hU) (cardinality (SubtypeCarrier T I) hI)
        by refl add (bp_card_irrelevant (SubtypeCarrier T U) hU' hU) (bp_card_irrelevant (SubtypeCarrier T I) hI' hI) ∎

{` Converse (bonus): with the blind hypotheses replaced by decidability, ours follows from the blind one. `}
def bridge_xca_cardinality_converse (k : blind_xca_cardinalityintersectionunion) (S : SetTypes) (hS : IsFinite (S .fst))
  (P Q : Subtypes (S .fst)) (dP : (s : S .fst) → Decidable (P s .fst)) (dQ : (s : S .fst) → Decidable (Q s .fst))
  : Id Nat
      (add (cardinality (SubtypeCarrier (S .fst) P) (subset_finite (S .fst) hS P dP))
        (cardinality (SubtypeCarrier (S .fst) Q) (subset_finite (S .fst) hS Q dQ)))
      (add (cardinality (SubtypeCarrier (S .fst) (SubsetUnion (S .fst) P Q))
             (subset_finite (S .fst) hS (SubsetUnion (S .fst) P Q) (subset_union_decidable (S .fst) P Q dP dQ)))
        (cardinality (SubtypeCarrier (S .fst) (SubsetIntersection (S .fst) P Q))
             (subset_finite (S .fst) hS (SubsetIntersection (S .fst) P Q) (subset_intersection_decidable (S .fst) P Q dP dQ))))
  ≔ k S hS P Q (subset_finite (S .fst) hS P dP) (subset_finite (S .fst) hS Q dQ)
      (subset_finite (S .fst) hS (SubsetUnion (S .fst) P Q) (subset_union_decidable (S .fst) P Q dP dQ))
      (subset_finite (S .fst) hS (SubsetIntersection (S .fst) P Q) (subset_intersection_decidable (S .fst) P Q dP dQ))

{` def:intersectionofgroups: same pointed type; groups identified along the groupoid proofs. `}
def bridge_def_group_pullback_type (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Product (Id Type (BlindGroupPullbackType H H' G f f') (pbg_space G H H' f f'))
      (Id (pbg_space G H H' f f') (blind_group_pullback_point H H' G f f') (pbg_point G H H' f f'))
  ≔ (refl (pbg_space G H H' f f'), refl (pbg_point G H H' f f'))

def bp_grp (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (h : isGroupoid (pbg_space G H H' f f')) : Group
  ≔ automorphism_group (pbg_space G H H' f f') h (pbg_point G H H' f f')

def bp_transport (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (Q : isGroupoid (pbg_space G H H' f f') → Type) (q : Q (pbg_space_groupoid G H H' f f'))
  : Q (blind_group_pullback_groupoid H H' G f f')
  ≔ transport (isGroupoid (pbg_space G H H' f f')) Q (pbg_space_groupoid G H H' f f') (blind_group_pullback_groupoid H H' G f f')
      (isgroupoid_isprop (pbg_space G H H' f f') (pbg_space_groupoid G H H' f f') (blind_group_pullback_groupoid H H' G f f')) q

def bridge_def_group_pullback (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id Group (pullback_group G H H' f f') (blind_group_pullback H H' G f f')
  ≔ refl (bp_grp H H' G f f')
      (isgroupoid_isprop (pbg_space G H H' f f') (pbg_space_groupoid G H H' f f') (blind_group_pullback_groupoid H H' G f f'))

def bp_proj1 (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (h : isGroupoid (pbg_space G H H' f f'))
  : GroupHom (bp_grp H H' G f f' h) H
  ≔ mkhom (bp_grp H H' G f f' h) H (c ↦ c .fst .fst .fst, refl (shape H))

def bp_proj2 (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (h : isGroupoid (pbg_space G H H' f f'))
  : GroupHom (bp_grp H H' G f f' h) H'
  ≔ mkhom (bp_grp H H' G f f' h) H' (c ↦ c .fst .fst .snd, refl (shape H'))

{` congp.tex:479 (1). `}
def bp_homs_type (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  (h : isGroupoid (pbg_space G H H' f f')) : Type
  ≔ Σ (BookEquiv (GroupHom K (bp_grp H H' G f f' h)) (BlindHomPullback H H' G f f' K)) (e ↦
      (g : GroupHom K (bp_grp H H' G f f' h))
      → Product
          (Id (GroupHom K H) (e .map g .fst .fst) (group_hom_compose K (bp_grp H H' G f f' h) H g (bp_proj1 H H' G f f' h)))
          (Id (GroupHom K H') (e .map g .fst .snd) (group_hom_compose K (bp_grp H H' G f f' h) H' g (bp_proj2 H H' G f f' h))))

def bridge_xca_pullback_homs : blind_xca_pullback_homs
  ≔ H H' G f f' K ↦
    bp_transport H H' G f f' (bp_homs_type H H' G f f' K)
      (book_equivalence (GroupHom K (pullback_group G H H' f f')) (HomPullback G H H' f f' K)
         (pullback_group_hom_equiv G H H' f f' K),
       g ↦ (pullback_group_hom_equiv_left G H H' f f' K g, pullback_group_hom_equiv_right G H H' f f' K g))

{` congp.tex:479 (2) and (3). `}
def bp_usym_type (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G) (h : isGroupoid (pbg_space G H H' f f')) : Type
  ≔ Σ (Σ (BookEquiv (USym (bp_grp H H' G f f' h)) (BlindUSymPullback H H' G f f')) (e ↦
        (w : USym (bp_grp H H' G f f' h))
        → Product
            (Id (USym H) (e .map w .fst .fst) (usym_hom (bp_grp H H' G f f' h) H (bp_proj1 H H' G f f' h) w))
            (Id (USym H') (e .map w .fst .snd) (usym_hom (bp_grp H H' G f f' h) H' (bp_proj2 H H' G f f' h) w))))
      (E ↦ (w w' : USym (bp_grp H H' G f f' h))
        → Id (Product (USym H) (USym H'))
            (E .fst .map (usym_mul (bp_grp H H' G f f' h) w w') .fst)
            (usym_mul H (E .fst .map w .fst .fst) (E .fst .map w' .fst .fst),
             usym_mul H' (E .fst .map w .fst .snd) (E .fst .map w' .fst .snd)))

def bp_usym_ours (H H' G : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : bp_usym_type H H' G f f' (pbg_space_groupoid G H H' f f')
  ≔ let P ≔ pullback_group G H H' f f' in
    ((book_equivalence (USym P) (PullbackUSym G H H' f f') (pullback_group_usym_equiv G H H' f f'),
      w ↦ (refl (usym_hom P H (pullback_group_proj_left G H H' f f') w),
           refl (usym_hom P H' (pullback_group_proj_right G H H' f f') w))),
     w w' ↦ pullback_group_usym_map_hom G H H' f f' w w' .fst)

def bridge_xca_pullback_usym : blind_xca_pullback_usym
  ≔ H H' G f f' ↦ bp_transport H H' G f f' (bp_usym_type H H' G f f') (bp_usym_ours H H' G f f') .fst

def bridge_xca_pullback_abstract : blind_xca_pullback_abstract
  ≔ H H' G f f' ↦ bp_transport H H' G f f' (bp_usym_type H H' G f f') (bp_usym_ours H H' G f f')

{` congp.tex:497: 1 ×_{BZ} 1 for the constructed circle (the base-point
   homomorphism from the trivial group) is not connected. `}
def bp_base_hom (C : CircleSignature) : GroupHom unit_group (circle_group C)
  ≔ mkhom unit_group (circle_group C) ((_ ↦ C .base), refl (C .base))

def bridge_rem_pullback_not_connected : blind_rem_pullback_not_connected
  ≔ all ↦ circle_point_pullback_not_connected constructed_circle
      (all unit_group unit_group (circle_group constructed_circle)
        (bp_base_hom constructed_circle) (bp_base_hom constructed_circle))
