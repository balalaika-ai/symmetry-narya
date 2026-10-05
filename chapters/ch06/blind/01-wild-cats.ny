export "../../../src/193-replacement"
export "../../../src/98-pointed-universal-coverings"
export "../../../src/54-integer-order"
export "../../../src/69-orders-and-subgroups"
export "../../../src/21-subtypes"
export "../../../src/150-paths-over-and-pairs"

{` Blind statements, chapter 6 (cats.tex), section "Categories".
   Composition is written in the book's order: comp a b c g f = g ∘ f
   for f : a → b, g : b → c. `}

{` def:wild-cat. `}
def BlindWildPrecat : Type ≔ sig (
  ob : Type,
  hom : ob → ob → Type,
  idn : (a : ob) → hom a a,
  comp : (a b c : ob) → hom b c → hom a b → hom a c,
  lunit : (a b : ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f,
  runit : (a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f,
  assoc : (a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
    → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))

{` The same data with the objects and arrows fixed (used for "construct a
   wild precategory structure on ..."). `}
def BlindWildPrecatStr (Ob : Type) (hom : Ob → Ob → Type) : Type ≔ sig (
  idn : (a : Ob) → hom a a,
  comp : (a b c : Ob) → hom b c → hom a b → hom a c,
  lunit : (a b : Ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f,
  runit : (a b : Ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f,
  assoc : (a b c d : Ob) (f : hom a b) (g : hom b c) (h : hom c d)
    → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))

{` rem:wild. The universe as a wild precategory, all laws by reflexivity. `}
def blind_universe_wild_precat : BlindWildPrecat
  ≔ (Type, (A B ↦ A → B), (A ↦ x ↦ x), (A B C g f ↦ x ↦ g (f x)),
     (A B f ↦ refl f), (A B f ↦ refl f), (A B C D f g h ↦ refl (x ↦ h (g (f x)))))

{` rem:wild. Pointed types (book pointed maps, pointing path pt_B = f(pt_A)). `}
def blind_pointed_lunit (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) (book_pointed_compose A B B f (book_pointed_identity B)) f
  ≔ (refl (f .fst), concat_1p (B .carrier) (B .point) (f .fst (A .point)) (f .snd))

def blind_pointed_runit (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) (book_pointed_compose A A B (book_pointed_identity A) f) f
  ≔ (refl (f .fst), concat_p1 (B .carrier) (B .point) (f .fst (A .point)) (f .snd))

def blind_pointed_assoc (A B C D : Pointed) (f : BookPointedMap A B) (g : BookPointedMap B C)
  (h : BookPointedMap C D)
  : Id (BookPointedMap A D)
      (book_pointed_compose A C D (book_pointed_compose A B C f g) h)
      (book_pointed_compose A B D f (book_pointed_compose B C D g h))
  ≔ let hp ≔ h .snd in
    let gp ≔ g .snd in
    let fp ≔ f .snd in
    let h0 ≔ h .fst in
    let g0 ≔ g .fst in
    let pa ≔ A .point in
    let pb ≔ B .point in
    let pc ≔ C .point in
    let pd ≔ D .point in
    (refl (x ↦ h0 (g0 (f .fst x))),
     concat (Id (D .carrier) pd (h0 (g0 (f .fst pa))))
       (concat (D .carrier) pd (h0 pc) (h0 (g0 (f .fst pa))) hp
          (refl h0 (concat (C .carrier) pc (g0 pb) (g0 (f .fst pa)) gp (refl g0 fp))))
       (concat (D .carrier) pd (h0 pc) (h0 (g0 (f .fst pa))) hp
          (concat (D .carrier) (h0 pc) (h0 (g0 pb)) (h0 (g0 (f .fst pa))) (refl h0 gp) (refl h0 (refl g0 fp))))
       (concat (D .carrier) pd (h0 (g0 pb)) (h0 (g0 (f .fst pa)))
          (concat (D .carrier) pd (h0 pc) (h0 (g0 pb)) hp (refl h0 gp)) (refl h0 (refl g0 fp)))
       (refl (concat (D .carrier) pd (h0 pc) (h0 (g0 (f .fst pa))) hp)
          (map_path_concat (C .carrier) (D .carrier) h0 pc (g0 pb) (g0 (f .fst pa)) gp (refl g0 fp)))
       (inverse (Id (D .carrier) pd (h0 (g0 (f .fst pa))))
          (concat (D .carrier) pd (h0 (g0 pb)) (h0 (g0 (f .fst pa)))
            (concat (D .carrier) pd (h0 pc) (h0 (g0 pb)) hp (refl h0 gp)) (refl h0 (refl g0 fp)))
          (concat (D .carrier) pd (h0 pc) (h0 (g0 (f .fst pa))) hp
            (concat (D .carrier) (h0 pc) (h0 (g0 pb)) (h0 (g0 (f .fst pa))) (refl h0 gp) (refl h0 (refl g0 fp))))
          (concat_assoc (D .carrier) pd (h0 pc) (h0 (g0 pb)) (h0 (g0 (f .fst pa))) hp (refl h0 gp)
            (refl h0 (refl g0 fp)))))

def blind_pointed_wild_precat : BlindWildPrecat
  ≔ (Pointed, BookPointedMap, book_pointed_identity,
     (A B C g f ↦ book_pointed_compose A B C f g),
     blind_pointed_lunit, blind_pointed_runit, blind_pointed_assoc)

{` rem:wild / eq:pentagon: the coherences a wild precategory does NOT have.
   The identification of λ and ρ at an identity, and the pentagon filler for
   f : a → b, g : b → c, h : c → d, k : d → e. `}
def BlindUnitCoherence (C : BlindWildPrecat) : Type
  ≔ (a : C .ob) → Id (Id (C .hom a a) (C .comp a a a (C .idn a) (C .idn a)) (C .idn a))
      (C .lunit a a (C .idn a)) (C .runit a a (C .idn a))

def BlindPentagon (C : BlindWildPrecat) : Type
  ≔ (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) (k : C .hom d e)
    → let p0 ≔ C .comp a d e k (C .comp a c d h (C .comp a b c g f)) in
      let p1 ≔ C .comp a d e k (C .comp a b d (C .comp b c d h g) f) in
      let p2 ≔ C .comp a b e (C .comp b d e k (C .comp b c d h g)) f in
      let p3 ≔ C .comp a b e (C .comp b c e (C .comp c d e k h) g) f in
      let p4 ≔ C .comp a c e (C .comp c d e k h) (C .comp a b c g f) in
      Id (Id (C .hom a e) p0 p3)
        (concat (C .hom a e) p0 p2 p3
          (concat (C .hom a e) p0 p1 p2
            (refl (C .comp a d e k) (C .assoc a b c d f g h))
            (C .assoc a b d e f (C .comp b c d h g) k))
          (refl (x ↦ C .comp a b e x f) (C .assoc b c d e g h k)))
        (concat (C .hom a e) p0 p4 p3
          (C .assoc a c d e (C .comp a b c g f) h k)
          (C .assoc a b c e f g (C .comp c d e k h)))

{` def:precategory. `}
def BlindPrecat : Type ≔ Σ BlindWildPrecat (C ↦ (a b : C .ob) → isSet (C .hom a b))

{` def:iso-in-cat (the displayed type: f ∘ g = id_B and h ∘ f = id_A). `}
def BlindIsIso (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ Product (Σ (C .hom b a) (g ↦ Id (C .hom b b) (C .comp b a b f g) (C .idn b)))
      (Σ (C .hom b a) (h ↦ Id (C .hom a a) (C .comp a b a h f) (C .idn a)))

def BlindIso (C : BlindWildPrecat) (a b : C .ob) : Type ≔ Σ (C .hom a b) (BlindIsIso C a b)

{` def:univalent-cat. idtoiso by path induction, refl ↦ id. `}
def blind_id_iso (C : BlindWildPrecat) (a : C .ob) : BlindIso C a a
  ≔ (C .idn a, ((C .idn a, C .lunit a a (C .idn a)), (C .idn a, C .lunit a a (C .idn a))))

def blind_idtoiso (C : BlindWildPrecat) (a b : C .ob) (p : Id (C .ob) a b) : BlindIso C a b
  ≔ J (C .ob) a (y _ ↦ BlindIso C a y) (blind_id_iso C a) b p

def BlindIsUnivalent (C : BlindWildPrecat) : Type
  ≔ (a b : C .ob) → BookIsEquiv (Id (C .ob) a b) (BlindIso C a b) (blind_idtoiso C a b)

{` def:category. `}
def BlindWildCat : Type ≔ Σ BlindWildPrecat BlindIsUnivalent
def BlindCat : Type ≔ Σ BlindPrecat (C ↦ BlindIsUnivalent (C .fst))

{` def:full-subcat. Objects Ob(C)_P = Σ_{x} P(x) (def:subtype). `}
def blind_full_subcat (C : BlindWildPrecat) (P : C .ob → PropTypes) : BlindWildPrecat
  ≔ (Σ (C .ob) (x ↦ P x .fst), (x y ↦ C .hom (x .fst) (y .fst)), (x ↦ C .idn (x .fst)),
     (x y z g f ↦ C .comp (x .fst) (y .fst) (z .fst) g f),
     (x y f ↦ C .lunit (x .fst) (y .fst) f), (x y f ↦ C .runit (x .fst) (y .fst) f),
     (x y z w f g h ↦ C .assoc (x .fst) (y .fst) (z .fst) (w .fst) f g h))

def blind_full_subprecat (C : BlindPrecat) (P : C .fst .ob → PropTypes) : BlindPrecat
  ≔ (blind_full_subcat (C .fst) P, (x y ↦ C .snd (x .fst) (y .fst)))

{` def:full-subcat, claim "it is univalent if C is" (non-wildness is
   blind_full_subprecat). `}
def blind_full_subcat_univalent : Type
  ≔ (C : BlindWildPrecat) (P : C .ob → PropTypes)
    → BlindIsUnivalent C → BlindIsUnivalent (blind_full_subcat C P)

{` lem:obj-gpd. `}
def blind_obj_gpd : Type ≔ (C : BlindCat) → isGroupoid (C .fst .fst .ob)

{` ex:poset. `}
def BlindPreorder : Type ≔ Σ BlindPrecat (C ↦ (a b : C .fst .ob) → isProp (C .fst .hom a b))

def BlindPoset : Type ≔ Σ BlindPreorder (C ↦ BlindIsUnivalent (C .fst .fst))

{` "The types of λ, ρ, α are contractible". `}
def blind_ex_poset_laws_contractible : Type
  ≔ (C : BlindPreorder) → let W ≔ C .fst .fst in
    Product ((a b : W .ob) (f : W .hom a b) → isContr (Id (W .hom a b) (W .comp a b b (W .idn b) f) f))
      (Product ((a b : W .ob) (f : W .hom a b) → isContr (Id (W .hom a b) (W .comp a a b f (W .idn a)) f))
        ((a b c d : W .ob) (f : W .hom a b) (g : W .hom b c) (h : W .hom c d)
          → isContr (Id (W .hom a d) (W .comp a c d h (W .comp a b c g f)) (W .comp a b d (W .comp b c d h g) f))))

{` "the data of a preorder reduces to a type P with a reflexive, transitive
   Prop-valued relation". `}
def BlindPreorderRelData : Type
  ≔ Σ Type (P ↦ Σ (P → P → PropTypes) (le ↦
      Product ((x : P) → le x x .fst) ((x y z : P) → le x y .fst → le y z .fst → le x z .fst)))

def blind_ex_poset_preorder_data : Type ≔ BookEquiv BlindPreorder BlindPreorderRelData

{` The preorder of a relation (proofs are the trivial ones). `}
def blind_preorder_of_rel (P : Type) (le : P → P → Type) (hp : (x y : P) → isProp (le x y))
  (r : (x : P) → le x x) (t : (x y z : P) → le x y → le y z → le x z) : BlindPreorder
  ≔ (((P, le, r, (x y z g f ↦ t x y z f g),
       (x y f ↦ hp x y (t x y y f (r y)) f), (x y f ↦ hp x y (t x x y (r x) f) f),
       (x y z w f g h ↦ hp x w (t x z w (t x y z f g) h) (t x y w f (t y z w g h)))),
      (x y ↦ prop_is_set (le x y) (hp x y))),
     hp)

{` "(P, ≤) is a poset" for a concrete relation: it is a Prop-valued, reflexive,
   transitive relation whose preorder is univalent. `}
def BlindRelIsPoset (P : Type) (le : P → P → Type) : Type
  ≔ Σ ((x y : P) → isProp (le x y)) (hp ↦ Σ ((x : P) → le x x) (r ↦
      Σ ((x y z : P) → le x y → le y z → le x z) (t ↦
        BlindIsUnivalent (blind_preorder_of_rel P le hp r t .fst .fst))))

{` "In this case, the type of objects is a set." `}
def blind_ex_poset_objects_set : Type ≔ (C : BlindPoset) → isSet (C .fst .fst .fst .ob)

{` "This happens iff the relation is (anti)symmetric": for a preorder,
   univalence ⇔ (x ≤ y → y ≤ x → x = y). The book says "symmetric" but the
   "i.e." clause is antisymmetry, which is what is stated. `}
def blind_ex_poset_iff_antisymmetric : Type
  ≔ (C : BlindPreorder) → let W ≔ C .fst .fst in
    Product (BlindIsUnivalent W → (x y : W .ob) → W .hom x y → W .hom y x → Id (W .ob) x y)
      (((x y : W .ob) → W .hom x y → W .hom y x → Id (W .ob) x y) → BlindIsUnivalent W)

def blind_ex_poset_nat : Type ≔ BlindRelIsPoset Nat Le
def blind_ex_poset_int : Type ≔ BlindRelIsPoset Int IntLe
def blind_ex_poset_prop : Type ≔ BlindRelIsPoset PropTypes (P Q ↦ P .fst → Q .fst)
def blind_ex_poset_sub : Type ≔ (S : SetTypes) → BlindRelIsPoset (Subtypes (S .fst)) (Inclusion (S .fst))

{` "2 with the always true relation is a preorder (a precategory) that is not
   univalent". `}
def blind_ex_poset_bool_not_univalent : Type
  ≔ Σ ((x y : Bool) → isProp Unit) (hp ↦ Σ ((x : Bool) → Unit) (r ↦
      Σ ((x y z : Bool) → Unit → Unit → Unit) (t ↦
        BlindIsUnivalent (blind_preorder_of_rel Bool (_ _ ↦ Unit) hp r t .fst .fst) → Empty)))

{` xca:order-poset. d | k is OrderDivides d k (module 69). `}
def blind_xca_order_poset : Type ≔ BlindRelIsPoset Order OrderDivides

{` def:wild-pre-groupoid. `}
def BlindIsPregroupoid (C : BlindWildPrecat) : Type
  ≔ (a b : C .ob) (f : C .hom a b) → BlindIsIso C a b f

def BlindWildPregroupoid : Type ≔ Σ BlindWildPrecat BlindIsPregroupoid
def BlindPregroupoid : Type ≔ Σ BlindPrecat (C ↦ BlindIsPregroupoid (C .fst))
def BlindWildGroupoid : Type ≔ Σ BlindWildPregroupoid (C ↦ BlindIsUnivalent (C .fst))
def BlindGroupoid : Type ≔ Σ BlindPregroupoid (C ↦ BlindIsUnivalent (C .fst .fst))

{` ex:path-groupoid. Book g ∘ f for paths f : x = y, g : y = z is g·f, i.e.
   concat f g. `}
def blind_path_wild_precat (X : Type) : BlindWildPrecat
  ≔ (X, (x y ↦ Id X x y), (x ↦ refl x), (x y z g f ↦ concat X x y z f g),
     (x y f ↦ concat_p1 X x y f), (x y f ↦ concat_1p X x y f),
     (x y z w f g h ↦ concat_assoc X x y z w f g h))

def blind_ex_path_groupoid_wild : Type
  ≔ (X : Type) → Product (BlindIsPregroupoid (blind_path_wild_precat X))
      (BlindIsUnivalent (blind_path_wild_precat X))

def blind_ex_path_groupoid_one_type : Type
  ≔ (X : Type) → isGroupoid X
    → Product ((x y : X) → isSet (Id X x y))
        (Product (BlindIsPregroupoid (blind_path_wild_precat X)) (BlindIsUnivalent (blind_path_wild_precat X)))

{` rem:cat-sizes. A universe is a predicate `small` (module 190). `}
def BlindIsUSmall (U : Universe) (C : BlindWildPrecat) : Type
  ≔ Product (U .small (C .ob)) ((a b : C .ob) → U .small (C .hom a b))

def BlindIsLocallyUSmall (U : Universe) (C : BlindWildPrecat) : Type
  ≔ (a b : C .ob) → U .small (C .hom a b)

def blind_rem_cat_sizes_path_small : Type
  ≔ (U : Universe) (X : Type) → U .small X → BlindIsUSmall U (blind_path_wild_precat X)

{` The wild categories of U-types, U-sets and pointed U-types (objects: the
   types with `small`; arrows as before). `}
def blind_universe_wild_precat_in (U : Universe) : BlindWildPrecat
  ≔ blind_full_subcat blind_universe_wild_precat (A ↦ (U .small A, U .small_prop A))

def blind_sets_wild_precat_in (U : Universe) : BlindWildPrecat
  ≔ blind_full_subcat blind_universe_wild_precat
      (A ↦ (Product (U .small A) (isSet A),
            sigma_prop (U .small A) (_ ↦ isSet A) (U .small_prop A) (_ ↦ isset_isprop A)))

def blind_pointed_wild_precat_in (U : Universe) : BlindWildPrecat
  ≔ blind_full_subcat blind_pointed_wild_precat (A ↦ (U .small (A .carrier), U .small_prop (A .carrier)))

def blind_rem_cat_sizes_locally_small : Type
  ≔ (U : Universe) → Product (BlindIsLocallyUSmall U (blind_universe_wild_precat_in U))
      (Product (BlindIsLocallyUSmall U (blind_sets_wild_precat_in U))
        (BlindIsLocallyUSmall U (blind_pointed_wild_precat_in U)))

{` "This generalizes def:ess-loc-small for path groupoids": a type whose path
   groupoid is locally U-small is locally U-small in the sense of types. `}
def blind_rem_cat_sizes_generalizes : Type
  ≔ (U : Universe) (A : Type) → BlindIsLocallyUSmall U (blind_path_wild_precat A) → LocallySmall U A

{` def:slice-cat (example). Arrows (A,f) → (A',f') are g with f' ∘ g = f. `}
def BlindSliceHom (C : BlindPrecat) (c : C .fst .ob)
  (u v : Σ (C .fst .ob) (a ↦ C .fst .hom a c)) : Type
  ≔ Σ (C .fst .hom (u .fst) (v .fst)) (g ↦ Id (C .fst .hom (u .fst) c) (C .fst .comp (u .fst) (v .fst) c (v .snd) g) (u .snd))

def blind_slice_hom_path (C : BlindPrecat) (c : C .fst .ob) (u v : Σ (C .fst .ob) (a ↦ C .fst .hom a c))
  (g h : BlindSliceHom C c u v) (p : Id (C .fst .hom (u .fst) (v .fst)) (g .fst) (h .fst))
  : Id (BlindSliceHom C c u v) g h
  ≔ equiv_inverse_map (Id (BlindSliceHom C c u v) g h) (Id (C .fst .hom (u .fst) (v .fst)) (g .fst) (h .fst))
      (subtype_path_equiv (C .fst .hom (u .fst) (v .fst))
        (k ↦ Id (C .fst .hom (u .fst) c) (C .fst .comp (u .fst) (v .fst) c (v .snd) k) (u .snd))
        (k ↦ C .snd (u .fst) c (C .fst .comp (u .fst) (v .fst) c (v .snd) k) (u .snd)) g h) p

def blind_slice_comp (C : BlindPrecat) (c : C .fst .ob) (u v w : Σ (C .fst .ob) (a ↦ C .fst .hom a c))
  (k : BlindSliceHom C c v w) (g : BlindSliceHom C c u v) : BlindSliceHom C c u w
  ≔ let W ≔ C .fst in
    let a ≔ u .fst in let b ≔ v .fst in let d ≔ w .fst in
    (W .comp a b d (k .fst) (g .fst),
     concat (W .hom a c) (W .comp a d c (w .snd) (W .comp a b d (k .fst) (g .fst)))
       (W .comp a b c (W .comp b d c (w .snd) (k .fst)) (g .fst)) (u .snd)
       (W .assoc a b d c (g .fst) (k .fst) (w .snd))
       (concat (W .hom a c) (W .comp a b c (W .comp b d c (w .snd) (k .fst)) (g .fst))
          (W .comp a b c (v .snd) (g .fst)) (u .snd)
          (refl (x ↦ W .comp a b c x (g .fst)) (k .snd)) (g .snd)))

def blind_slice_precat (C : BlindPrecat) (c : C .fst .ob) : BlindPrecat
  ≔ let W ≔ C .fst in
    let O ≔ Σ (W .ob) (a ↦ W .hom a c) in
    ((O, BlindSliceHom C c,
      (u ↦ (W .idn (u .fst), W .runit (u .fst) c (u .snd))),
      blind_slice_comp C c,
      (u v g ↦ blind_slice_hom_path C c u v (blind_slice_comp C c u v v (W .idn (v .fst), W .runit (v .fst) c (v .snd)) g) g
         (W .lunit (u .fst) (v .fst) (g .fst))),
      (u v g ↦ blind_slice_hom_path C c u v (blind_slice_comp C c u u v g (W .idn (u .fst), W .runit (u .fst) c (u .snd))) g
         (W .runit (u .fst) (v .fst) (g .fst))),
      (u v w x f g h ↦ blind_slice_hom_path C c u x
         (blind_slice_comp C c u w x h (blind_slice_comp C c u v w g f))
         (blind_slice_comp C c u v x (blind_slice_comp C c v w x h g) f)
         (W .assoc (u .fst) (v .fst) (w .fst) (x .fst) (f .fst) (g .fst) (h .fst)))),
     (u v ↦ sigma_set (W .hom (u .fst) (v .fst))
        (g ↦ Id (W .hom (u .fst) c) (W .comp (u .fst) (v .fst) c (v .snd) g) (u .snd))
        (C .snd (u .fst) (v .fst))
        (g ↦ prop_is_set (Id (W .hom (u .fst) c) (W .comp (u .fst) (v .fst) c (v .snd) g) (u .snd))
           (C .snd (u .fst) c (W .comp (u .fst) (v .fst) c (v .snd) g) (u .snd)))))

{` def:slice-cat: "If C is univalent (hence a category), then so is C/C." `}
def blind_ex_slice_univalent : Type
  ≔ (C : BlindCat) (c : C .fst .fst .ob) → BlindIsUnivalent (blind_slice_precat (C .fst) c .fst)

{` xca:univ-slice-cat. Objects (A, f : A → B); arrows g : A → A' with an
   identification f' ∘ g = f of functions (as in def:slice-cat). `}
def BlindUnivSliceOb (B : Type) : Type ≔ Σ Type (A ↦ A → B)

def BlindUnivSliceHom (B : Type) (u v : BlindUnivSliceOb B) : Type
  ≔ Σ (u .fst → v .fst) (g ↦ Id (u .fst → B) (x ↦ v .snd (g x)) (u .snd))

def blind_xca_univ_slice_cat : Type
  ≔ (B : Type) → BlindWildPrecatStr (BlindUnivSliceOb B) (BlindUnivSliceHom B)
