export "1204-double-delooping"
export "432-pointed-maps-truncation-level"
export "289-book-equivalence-maps-two"
export "403-abstract-groups"

{` Chapter 12, sec:ab-hom (abelian.tex 779-822): the group Hom(G, H) of
   homomorphisms into an abelian group H, Hom(G, H) ≔ Aut_{BG →* BB H}(cst),
   and the construction USym(Hom(G, H)) ≃ Hom(G, H) ≃ absHom(G, H).

   Generality: the book assumes G and H abelian in the construction; only H
   abelian is used (the identification Ω(BB H) ≃* BH). The type
   BG →* BB H is a groupoid for every group H (BB H is a 2-type for every H);
   following the book, the group is formed for abelian H. `}

def bb_hlevel_four (H : Group) : HLevel (suc. (suc. (suc. (suc. zero.)))) (BB H .carrier)
  ≔ u v ↦ groupoid_to_hlevel (Id (BB H .carrier) u v) (bb_two_type H u v)

{` Running text (abelian.tex 799): since BB H is a 2-type, BG →* BB H is a
   1-type (pointed maps from a connected type lower the truncation level,
   ft:ptd-decr-h-lev, module 432). `}
def pointed_maps_bb_groupoid (G H : Group) : isGroupoid (BookPointedMap (BG G) (BB H))
  ≔ hlevel_to_groupoid (BookPointedMap (BG G) (BB H))
      (pointed_maps_truncation_level (suc. zero.) (suc. (suc. (suc. zero.))) (BG G) (BB H)
        (equiv_inverse_map (NConnectedType (suc. zero.) (BG G .carrier)) (Connected (BG G .carrier))
          (zero_connected_connected (BG G .carrier)) (bg_connected G))
        (bb_hlevel_four H))

{` Definition (abelian.tex 792): Hom(G, H) ≔ Aut_{BG →* BB H}(cst_{pt_{BB H}}),
   the constant map pointed by refl. `}
def abelian_hom_group (G : Group) (H : AbelianGroup) : Group
  ≔ automorphism_group (BookPointedMap (BG G) (BB (H .fst))) (pointed_maps_bb_groupoid G (H .fst))
      (book_pointed_constant (BG G) (BB (H .fst)))

{` ptw_*: identifications of the constant pointed map with itself are
   pointed maps into the loop space. The underlying function of the image of
   r is x ↦ ptw(r₁)(x) = happly(r₁)(x). `}
def constant_pointed_homotopy_equiv (X Y : Pointed)
  : Equiv (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y)) (BookPointedMap X (Omega Y))
  ≔ let y ≔ Y .point in let L ≔ Id (Y .carrier) y y in
    family_equiv (X .carrier → L)
      (h ↦ Id L (concat (Y .carrier) y y y (refl y) (h (X .point))) (refl y))
      (h ↦ Id L (refl y) (h (X .point)))
      (h ↦ compose_equiv (Id L (concat (Y .carrier) y y y (refl y) (h (X .point))) (refl y))
        (Id L (h (X .point)) (refl y)) (Id L (refl y) (h (X .point)))
        (path_endpoints_equiv L (concat (Y .carrier) y y y (refl y) (h (X .point))) (h (X .point)) (refl y) (refl y)
          (inverse L (concat (Y .carrier) y y y (refl y) (h (X .point))) (h (X .point))
            (concat_1p (Y .carrier) y y (h (X .point))))
          (refl (refl y)))
        (inverse_path_equiv L (h (X .point)) (refl y)))

def pointed_map_path_explicit_equiv (X Y : Pointed) (f g : BookPointedMap X Y)
  : Equiv (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
  ≔ native_equivalence (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
      ((p ↦ (happly (X .carrier) (_ ↦ Y .carrier) (f .fst) (g .fst) (p .fst),
         pathover_transport_equiv (X .carrier → Y .carrier)
           (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
           (f .fst) (g .fst) (p .fst) (f .snd) (g .snd) .map (p .snd))),
       pointed_map_path_equiv_book_map X Y f g)

def constant_loops_pointed_equiv (X Y : Pointed)
  : Equiv (Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y)) (BookPointedMap X (Omega Y))
  ≔ compose_equiv (Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y))
      (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y)) (BookPointedMap X (Omega Y))
      (pointed_map_path_explicit_equiv X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
      (constant_pointed_homotopy_equiv X Y)

{` Postcomposition with a pointed equivalence is an equivalence of pointed
   mapping types; the map is k ↦ e ∘ k (book_pointed_compose). `}
def postcompose_equiv (X Y Z : Type) (e : Equiv Y Z) : Equiv (X → Y) (X → Z)
  ≔ quasi_inverse_equiv (X → Y) (X → Z) (k x ↦ e .map (k x)) (k x ↦ equiv_inverse_map Y Z e (k x))
      (k ↦ funext X (_ ↦ Y) (x ↦ equiv_inverse_map Y Z e (e .map (k x))) k (x ↦ equiv_retraction Y Z e (k x)))
      (k ↦ funext X (_ ↦ Z) (x ↦ e .map (equiv_inverse_map Y Z e (k x))) k (x ↦ equiv_counit Y Z e (k x)))

def pointed_postcompose_equiv (X Y Z : Pointed) (e : BookPointedEquiv Y Z)
  : Equiv (BookPointedMap X Y) (BookPointedMap X Z)
  ≔ let eN ≔ native_equivalence (Y .carrier) (Z .carrier) (e .fst .fst, e .snd) in
    let post ≔ postcompose_equiv (X .carrier) (Y .carrier) (Z .carrier) eN in
    let Pz ≔ (k ↦ Id (Z .carrier) (Z .point) (k (X .point))) : (X .carrier → Z .carrier) → Type in
    let fib ≔ (k ↦ compose_equiv (Id (Y .carrier) (Y .point) (k (X .point)))
        (Id (Z .carrier) (e .fst .fst (Y .point)) (e .fst .fst (k (X .point))))
        (Id (Z .carrier) (Z .point) (e .fst .fst (k (X .point))))
        (equivalence_on_paths (Y .carrier) (Z .carrier) eN (Y .point) (k (X .point)))
        (concat_left_equiv (Z .carrier) (Z .point) (e .fst .fst (Y .point)) (e .fst .fst (k (X .point))) (e .fst .snd)))
      : (k : X .carrier → Y .carrier) → Equiv (Id (Y .carrier) (Y .point) (k (X .point))) (Pz (post .map k)) in
    equiv_change_map (BookPointedMap X Y) (BookPointedMap X Z)
      (compose_equiv (BookPointedMap X Y) (Σ (X .carrier → Y .carrier) (k ↦ Pz (post .map k))) (BookPointedMap X Z)
        (family_equiv (X .carrier → Y .carrier) (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
          (k ↦ Pz (post .map k)) fib)
        (sigma_pullback_equiv (X .carrier → Y .carrier) (X .carrier → Z .carrier) post Pz))
      (k ↦ book_pointed_compose X Y Z k (e .fst))
      (k ↦ sigma_pullback_equiv_map (X .carrier → Y .carrier) (X .carrier → Z .carrier) post Pz
        (k .fst, fib (k .fst) .map (k .snd)))

{` construction (abelian.tex 802), concrete part:
   USym(Hom(G, H)) ≃ (cst = cst) ≃ (BG →* Ω(BB H)) ≃ (BG →* BH) ≃ Hom(G, H). `}
def abelian_hom_usym_equiv (G : Group) (H : AbelianGroup)
  : Equiv (USym (abelian_hom_group G H)) (GroupHom G (H .fst))
  ≔ let P ≔ BookPointedMap (BG G) (BB (H .fst)) in
    let c ≔ book_pointed_constant (BG G) (BB (H .fst)) in
    compose_equiv (USym (abelian_hom_group G H)) (Id P c c) (GroupHom G (H .fst))
      (automorphism_group_usym_equiv P (pointed_maps_bb_groupoid G (H .fst)) c)
      (compose_equiv (Id P c c) (BookPointedMap (BG G) (Omega (BB (H .fst)))) (GroupHom G (H .fst))
        (constant_loops_pointed_equiv (BG G) (BB (H .fst)))
        (compose_equiv (BookPointedMap (BG G) (Omega (BB (H .fst)))) (BookPointedMap (BG G) (BG (H .fst)))
          (GroupHom G (H .fst))
          (pointed_postcompose_equiv (BG G) (Omega (BB (H .fst))) (BG (H .fst))
            (abelian_bb_loops_pointed_equiv (H .fst) (H .snd)))
          (canonical_inverse_equiv (GroupHom G (H .fst)) (BookPointedMap (BG G) (BG (H .fst)))
            (group_hom_classifying_equiv G (H .fst)))))

{` The underlying function of the homomorphism attached to p : USym(Hom(G, H))
   is x ↦ ev(ptw(p)(x)), with ev = bb_loops_evaluation. `}
def abelian_hom_usym_function (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H))
  : Id (BG G .carrier → BG (H .fst) .carrier) (hom_function G (H .fst) (abelian_hom_usym_equiv G H .map p))
      (x ↦ bb_loops_evaluation (H .fst) (p .fst .fst (refl x)))
  ≔ refl ((x ↦ bb_loops_evaluation (H .fst) (p .fst .fst (refl x))) : BG G .carrier → BG (H .fst) .carrier)

{` The last step of the construction, Hom(G, H) ≃ absHom(G, H), is
   lem:homomabstrconcr of chapter 7 (absgroup.tex 934), which is not yet
   available; it enters as the explicit hypothesis AbstrHomIsEquiv. `}
def AbstrHomIsEquiv (G H : Group) : Type
  ≔ BookIsEquiv (GroupHom G H) (AbstractHom (abstr G) (abstr H)) (abstr_hom G H)

def abelian_hom_abstract_map (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H))
  : AbstractHom (abstr G) (abstr (H .fst))
  ≔ abstr_hom G (H .fst) (abelian_hom_usym_equiv G H .map p)

def abelian_hom_abstract_equiv (G : Group) (H : AbelianGroup) (ff : AbstrHomIsEquiv G (H .fst))
  : BookEquiv (USym (abelian_hom_group G H)) (AbstractHom (abstr G) (abstr (H .fst)))
  ≔ book_equivalence (USym (abelian_hom_group G H)) (AbstractHom (abstr G) (abstr (H .fst)))
      (compose_equiv (USym (abelian_hom_group G H)) (GroupHom G (H .fst)) (AbstractHom (abstr G) (abstr (H .fst)))
        (abelian_hom_usym_equiv G H)
        (native_equivalence (GroupHom G (H .fst)) (AbstractHom (abstr G) (abstr (H .fst))) (abstr_hom G (H .fst), ff)))

{` Litmus: Hom(1, H) has a contractible type of symmetries, and
   USym(Hom(Z, H)) ≃ USym H (pointed circle universal property). `}
def unit_hom_group_usym_contractible (H : AbelianGroup) : BookIsContr (USym (abelian_hom_group unit_group H))
  ≔ book_contractibility_equiv (GroupHom unit_group (H .fst)) (USym (abelian_hom_group unit_group H))
      (canonical_inverse_equiv (USym (abelian_hom_group unit_group H)) (GroupHom unit_group (H .fst))
        (abelian_hom_usym_equiv unit_group H))
      .map (book_contractibility_equiv (BookPointedMap (BG unit_group) (BG (H .fst))) (GroupHom unit_group (H .fst))
        (canonical_inverse_equiv (GroupHom unit_group (H .fst)) (BookPointedMap (BG unit_group) (BG (H .fst)))
          (group_hom_classifying_equiv unit_group (H .fst)))
        .map (contractible_domain_pointed_maps (BG unit_group) (BG (H .fst)) (star., u ↦ unit_prop star. u)))

def circle_hom_group_usym_equiv (C : CircleSignature) (H : AbelianGroup)
  : Equiv (USym (abelian_hom_group (circle_group C) H)) (USym (H .fst))
  ≔ compose_equiv (USym (abelian_hom_group (circle_group C) H)) (GroupHom (circle_group C) (H .fst)) (USym (H .fst))
      (abelian_hom_usym_equiv (circle_group C) H)
      (compose_equiv (GroupHom (circle_group C) (H .fst)) (BookPointedMap (circle_pointed C) (BG (H .fst))) (USym (H .fst))
        (group_hom_classifying_equiv (circle_group C) (H .fst))
        (pointed_circle_universal_property C (BG (H .fst) .carrier) (shape (H .fst))))

{` Litmus: USym(Hom(Z, Z)) ≃ Z (as sets: the integers). `}
def circle_hom_group_integers (C : CircleSignature)
  : Equiv (USym (abelian_hom_group (circle_group C) (circle_abelian_group C))) Int
  ≔ compose_equiv (USym (abelian_hom_group (circle_group C) (circle_abelian_group C))) (USym (circle_group C)) Int
      (circle_hom_group_usym_equiv C (circle_abelian_group C))
      (canonical_inverse_equiv Int (USym (circle_group C))
        (native_equivalence Int (USym (circle_group C)) (circle_group_usym_integers C)))
