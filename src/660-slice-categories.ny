export "604-wild-pointed-types"

{` Chapter 6 (cats.tex): def:slice-cat, xca:univ-slice-cat,
   ex:slice-projection and the coslice remark after lem:op-idem.

   An object of the slice C/c is a pair (A, f : A → c); an arrow
   (A, f) → (A', f') is an arrow g : A → A' with an identification
   f' ∘ g = f (the commuting triangle of the footnote). The identity is
   (id, ρ_f) and the composite of (h, q) after (g, p) is h ∘ g with the
   identification α · ap(- ∘ g)(q) · p. `}

def SliceOb (C : WildPrecat) (c : C .ob) : Type ≔ Σ (C .ob) (a ↦ C .hom a c)

def SliceTriangle (C : WildPrecat) (c : C .ob) (x y : SliceOb C c) (g : C .hom (x .fst) (y .fst)) : Type
  ≔ Id (C .hom (x .fst) c) (C .comp (x .fst) (y .fst) c (y .snd) g) (x .snd)

def SliceHom (C : WildPrecat) (c : C .ob) (x y : SliceOb C c) : Type
  ≔ Σ (C .hom (x .fst) (y .fst)) (SliceTriangle C c x y)

def slice_idn (C : WildPrecat) (c : C .ob) (x : SliceOb C c) : SliceHom C c x x
  ≔ (C .idn (x .fst), C .ru (x .fst) c (x .snd))

def slice_comp (C : WildPrecat) (c : C .ob) (x y z : SliceOb C c) (k : SliceHom C c y z)
  (h : SliceHom C c x y) : SliceHom C c x z
  ≔ (C .comp (x .fst) (y .fst) (z .fst) (k .fst) (h .fst),
     concat (C .hom (x .fst) c)
       (C .comp (x .fst) (z .fst) c (z .snd) (C .comp (x .fst) (y .fst) (z .fst) (k .fst) (h .fst)))
       (C .comp (x .fst) (y .fst) c (C .comp (y .fst) (z .fst) c (z .snd) (k .fst)) (h .fst))
       (x .snd)
       (C .assoc (x .fst) (y .fst) (z .fst) c (h .fst) (k .fst) (z .snd))
       (concat (C .hom (x .fst) c)
         (C .comp (x .fst) (y .fst) c (C .comp (y .fst) (z .fst) c (z .snd) (k .fst)) (h .fst))
         (C .comp (x .fst) (y .fst) c (y .snd) (h .fst))
         (x .snd)
         (cat_whisker_right C (x .fst) (y .fst) c (C .comp (y .fst) (z .fst) c (z .snd) (k .fst)) (y .snd)
           (h .fst) (k .snd))
         (h .snd)))

{` Footnote to def:slice-cat: "This is a proposition since C is a
   precategory." `}
def slice_triangle_prop (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) (x y : SliceOb C c)
  (g : C .hom (x .fst) (y .fst)) : isProp (SliceTriangle C c x y g)
  ≔ hs (x .fst) c (C .comp (x .fst) (y .fst) c (y .snd) g) (x .snd)

{` In a precategory, slice arrows are determined by their underlying
   arrows. `}
def slice_hom_path (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) (x y : SliceOb C c)
  (u v : SliceHom C c x y) (p : Id (C .hom (x .fst) (y .fst)) (u .fst) (v .fst)) : Id (SliceHom C c x y) u v
  ≔ (p, pathover_of_eq (C .hom (x .fst) (y .fst)) (SliceTriangle C c x y) (u .fst) (v .fst) p (u .snd) (v .snd)
        (slice_triangle_prop C hs c x y (v .fst)
          (transport (C .hom (x .fst) (y .fst)) (SliceTriangle C c x y) (u .fst) (v .fst) p (u .snd)) (v .snd)))

{` def:slice-cat: the slice precategory C/c of a precategory, with
   identities and composition inherited from C. `}
def slice_precat_wild (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) : WildPrecat
  ≔ (ob ≔ SliceOb C c,
     hom ≔ SliceHom C c,
     idn ≔ slice_idn C c,
     comp ≔ slice_comp C c,
     lu ≔ x y f ↦ slice_hom_path C hs c x y (slice_comp C c x y y (slice_idn C c y) f) f
       (C .lu (x .fst) (y .fst) (f .fst)),
     ru ≔ x y f ↦ slice_hom_path C hs c x y (slice_comp C c x x y f (slice_idn C c x)) f
       (C .ru (x .fst) (y .fst) (f .fst)),
     assoc ≔ x y z w f g h ↦ slice_hom_path C hs c x w
       (slice_comp C c x z w h (slice_comp C c x y z g f)) (slice_comp C c x y w (slice_comp C c y z w h g) f)
       (C .assoc (x .fst) (y .fst) (z .fst) (w .fst) (f .fst) (g .fst) (h .fst)))

def slice_homset (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) : HasHomSets (slice_precat_wild C hs c)
  ≔ x y ↦ sigma_set (C .hom (x .fst) (y .fst)) (SliceTriangle C c x y) (hs (x .fst) (y .fst))
      (g ↦ prop_is_set (SliceTriangle C c x y g) (slice_triangle_prop C hs c x y g))

def SlicePrecat (C : Precat) (c : C .wild .ob) : Precat
  ≔ (slice_precat_wild (C .wild) (C .homset) c, slice_homset (C .wild) (C .homset) c)

{` Isomorphisms of the slice are exactly the slice arrows whose underlying
   arrow is an isomorphism of C. `}
def slice_iso_to_base (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) (x y : SliceOb C c)
  (h : SliceHom C c x y) (i : CatIsIso (slice_precat_wild C hs c) x y h) : CatIsIso C (x .fst) (y .fst) (h .fst)
  ≔ ((i .fst .fst .fst, i .fst .snd .fst), (i .snd .fst .fst, i .snd .snd .fst))

def slice_inverse_triangle (C : WildPrecat) (c : C .ob) (x y : SliceOb C c) (h : SliceHom C c x y)
  (k : C .hom (y .fst) (x .fst))
  (hk : Id (C .hom (y .fst) (y .fst)) (C .comp (y .fst) (x .fst) (y .fst) (h .fst) k) (C .idn (y .fst)))
  : SliceTriangle C c y x k
  ≔ let a ≔ x .fst in
    let b ≔ y .fst in
    calc
      C .comp b a c (x .snd) k
      = C .comp b a c (C .comp a b c (y .snd) (h .fst)) k
        by cat_whisker_right C b a c (x .snd) (C .comp a b c (y .snd) (h .fst)) k
             (inverse (C .hom a c) (C .comp a b c (y .snd) (h .fst)) (x .snd) (h .snd))
      = C .comp b b c (y .snd) (C .comp b a b (h .fst) k)
        by inverse (C .hom b c) (C .comp b b c (y .snd) (C .comp b a b (h .fst) k))
             (C .comp b a c (C .comp a b c (y .snd) (h .fst)) k) (C .assoc b a b c k (h .fst) (y .snd))
      = C .comp b b c (y .snd) (C .idn b)
        by cat_whisker_left C b b c (y .snd) (C .comp b a b (h .fst) k) (C .idn b) hk
      = y .snd by C .ru b c (y .snd) ∎

def slice_iso_from_base (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) (x y : SliceOb C c)
  (h : SliceHom C c x y) (i : CatIsIso C (x .fst) (y .fst) (h .fst)) : CatIsIso (slice_precat_wild C hs c) x y h
  ≔ let k ≔ i .fst .fst in
    let hk ≔ i .fst .snd in
    let kh : Id (C .hom (x .fst) (x .fst)) (C .comp (x .fst) (y .fst) (x .fst) k (h .fst)) (C .idn (x .fst))
      ≔ cat_iso_inverse C (x .fst) (y .fst) (h .fst, i) .snd .fst .snd in
    let kk : SliceHom C c y x ≔ (k, slice_inverse_triangle C c x y h k hk) in
    ((kk, slice_hom_path C hs c y y (slice_comp C c y x y h kk) (slice_idn C c y) hk),
     (kk, slice_hom_path C hs c x x (slice_comp C c x y x kk h) (slice_idn C c x) kh))

{` def:slice-cat: "If C is univalent (and hence a category), then so is
   C/c." For a fixed (a, f), the type of pairs of an object (b, g) and an
   isomorphism (a, f) ≅ (b, g) is a retract of the type of pairs of an
   isomorphism e : a ≅ b and an element of the fiber of - ∘ e over f; the
   latter is contractible by univalence of C and since - ∘ e is an
   equivalence. `}
def slice_univalent (C : WildPrecat) (hs : HasHomSets C) (u : IsUnivalentCat C) (c : C .ob)
  : IsUnivalentCat (slice_precat_wild C hs c)
  ≔ cat_univalent_from_contractible (slice_precat_wild C hs c) (x ↦
      let S ≔ slice_precat_wild C hs c in
      let a ≔ x .fst in
      let BE ≔ Σ (C .ob) (b ↦ CatIso C a b) in
      let Fb : BE → Type
        ≔ be ↦ Fiber (C .hom (be .fst) c) (C .hom a c) (k ↦ C .comp a (be .fst) c k (be .snd .fst)) (x .snd) in
      let T ≔ Σ (SliceOb C c) (y ↦ CatIso S x y) in
      contractible_retract (Σ BE Fb) T
        (sigma_contractible BE Fb (cat_univalent_iso_total_contractible C u a)
          (be ↦ cat_precompose_equiv C a (be .fst) (be .snd .fst) (be .snd .snd) c .equiv (x .snd)))
        (t ↦ ((t .fst .fst, t .snd .fst),
              ((t .fst .snd .fst, t .snd .snd),
               slice_iso_from_base C hs c x (t .fst .fst, t .snd .fst) (t .fst .snd .fst, t .snd .snd)
                 (t .fst .snd .snd))))
        (s ↦ ((s .fst .fst, (s .snd .fst .fst, slice_iso_to_base C hs c x (s .fst) (s .snd .fst) (s .snd .snd))),
              (s .fst .snd, s .snd .fst .snd)))
        (s ↦ refl ((w ↦ (s .fst, w)) : CatIso S x (s .fst) → T)
          (cat_iso_path S x (s .fst)
            (s .snd .fst,
             slice_iso_from_base C hs c x (s .fst) (s .snd .fst)
               (slice_iso_to_base C hs c x (s .fst) (s .snd .fst) (s .snd .snd)))
            (s .snd) (refl (s .snd .fst)))))

def SliceCategory (C : Category) (c : C .wild .ob) : Category
  ≔ (slice_precat_wild (C .wild) (C .homset) c, slice_homset (C .wild) (C .homset) c,
     slice_univalent (C .wild) (C .homset) (C .univalent) c)

{` ex:slice-projection: taking the domain is a functor fst : C/c → C. `}
def slice_projection (C : WildPrecat) (hs : HasHomSets C) (c : C .ob)
  : WildFunctor (slice_precat_wild C hs c) C
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y g ↦ g .fst,
     map_id ≔ x ↦ refl (C .idn (x .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) (g .fst) (f .fst)))

def slice_precat_projection (C : Precat) (c : C .wild .ob) : WildFunctor (SlicePrecat C c .wild) (C .wild)
  ≔ slice_projection (C .wild) (C .homset) c

{` The coslice c/C (the prose after lem:op-idem): the dual of the slice,
   (C^op/c)^op. `}
def coslice_precat_wild (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) : WildPrecat
  ≔ OppositeWild (slice_precat_wild (OppositeWild C) (a b ↦ hs b a) c)

def CoslicePrecat (C : Precat) (c : C .wild .ob) : Precat
  ≔ (coslice_precat_wild (C .wild) (C .homset) c,
     x y ↦ slice_homset (OppositeWild (C .wild)) (a b ↦ C .homset b a) c y x)

{` Unfolded, objects of the coslice are pairs (A, f : c → A) and an arrow
   (A, f) → (A', f') is g : A → A' with g ∘ f = f'. `}
def coslice_ob_unfold (C : WildPrecat) (hs : HasHomSets C) (c : C .ob)
  : Id Type (coslice_precat_wild C hs c .ob) (Σ (C .ob) (a ↦ C .hom c a))
  ≔ refl (Σ (C .ob) (a ↦ C .hom c a))

def coslice_hom_unfold (C : WildPrecat) (hs : HasHomSets C) (c : C .ob) (x y : coslice_precat_wild C hs c .ob)
  : Id Type (coslice_precat_wild C hs c .hom x y)
      (Σ (C .hom (x .fst) (y .fst)) (g ↦ Id (C .hom c (y .fst)) (C .comp c (x .fst) (y .fst) g (x .snd)) (y .snd)))
  ≔ refl (Σ (C .hom (x .fst) (y .fst)) (g ↦ Id (C .hom c (y .fst)) (C .comp c (x .fst) (y .fst) g (x .snd)) (y .snd)))

{` Litmus: in the coslice of sets under Unit, not is an arrow from
   (Bool, const true) to (Bool, const false), since not ∘ const true is
   const false by refl. `}
def coslice_litmus_arrow
  : coslice_precat_wild (SetCat .wild) (SetCat .homset) (Unit, unit_set) .hom
      ((Bool, bool_set), _ ↦ true.) ((Bool, bool_set), _ ↦ false.)
  ≔ (bool_not, refl ((_ ↦ false.) : Unit → Bool))

{` Litmus checks in the slice of the category of sets over Bool. The
   objects (Bool, not) and (Bool, id); not is an arrow from the first to the
   second (id ∘ not = not by refl), and also from the second to the first. `}
def slice_litmus_base : SetCat .wild .ob ≔ (Bool, bool_set)

def slice_litmus_not : SliceOb (SetCat .wild) slice_litmus_base ≔ ((Bool, bool_set), bool_not)

def slice_litmus_id : SliceOb (SetCat .wild) slice_litmus_base ≔ ((Bool, bool_set), x ↦ x)

def slice_litmus_arrow
  : SliceHom (SetCat .wild) slice_litmus_base slice_litmus_not slice_litmus_id
  ≔ (bool_not, refl bool_not)

def slice_litmus_back
  : SliceHom (SetCat .wild) slice_litmus_base slice_litmus_id slice_litmus_not
  ≔ (bool_not, funext Bool (_ ↦ Bool) (x ↦ bool_not (bool_not x)) (x ↦ x) bool_not_involutive)

def slice_litmus_composite_value
  : Id Bool
      (slice_precat_wild (SetCat .wild) (SetCat .homset) slice_litmus_base .comp
         slice_litmus_not slice_litmus_id slice_litmus_not slice_litmus_back slice_litmus_arrow .fst true.)
      true.
  ≔ refl (true. : Bool)

def slice_litmus_projection
  : Id (Bool → Bool)
      (slice_precat_projection (category_precat SetCat) slice_litmus_base .mor
         slice_litmus_not slice_litmus_id slice_litmus_arrow)
      bool_not
  ≔ refl bool_not

{` Orientation check: from (Unit, const true) there is an arrow to
   (Bool, id), but no arrow back (it would identify const true with id). `}
def slice_litmus_point : SliceOb (SetCat .wild) slice_litmus_base ≔ ((Unit, unit_set), _ ↦ true.)

def slice_litmus_point_arrow
  : SliceHom (SetCat .wild) slice_litmus_base slice_litmus_point slice_litmus_id
  ≔ (_ ↦ true., refl ((_ ↦ true.) : Unit → Bool))

def slice_litmus_no_arrow_back
  (g : SliceHom (SetCat .wild) slice_litmus_base slice_litmus_id slice_litmus_point) : Empty
  ≔ bool_encode true. false. (g .snd (refl (false. : Bool)))

{` def:slice-cat for wild precategories. To define α of C/c from
   identifications f' ∘ g = f one needs the pentagon (WildPentagon,
   eq:pentagon, module 604); the unit laws λ, ρ of C/c likewise need the
   triangle coherence of the footnote to rem:wild (WildTriangleCoherence,
   module 604) and its analogue with the identity on the right,
   α · ρ_{f∘g} = ap_{f∘-}(ρ_g), stated here. We build the wild slice from
   these three coherences. `}
def WildRightTriangleFiller (C : WildPrecat) : Type
  ≔ (a b c : C .ob) (g : C .hom a b) (f : C .hom b c)
    → Id (Id (C .hom a c) (C .comp a b c f (C .comp a a b g (C .idn a))) (C .comp a b c f g))
        (concat (C .hom a c) (C .comp a b c f (C .comp a a b g (C .idn a)))
          (C .comp a a c (C .comp a b c f g) (C .idn a)) (C .comp a b c f g)
          (C .assoc a a b c (C .idn a) g f) (C .ru a c (C .comp a b c f g)))
        (cat_whisker_left C a b c f (C .comp a a b g (C .idn a)) g (C .ru a b g))

{` Identifications in Σ_x (F x = t) from an identification e : x = y and
   a commuting triangle P = ap_F(e) · P'. `}
def wild_slice_sigma_path (X H : Type) (F : X → H) (t : H) (x y : X) (e : Id X x y)
  (P : Id H (F x) t) (P' : Id H (F y) t)
  (s : Id (Id H (F x) t) P (concat H (F x) (F y) t (refl F e) P'))
  : Id (Σ X (z ↦ Id H (F z) t)) (x, P) (y, P')
  ≔ J X x (y e ↦ (P' : Id H (F y) t) → Id (Id H (F x) t) P (concat H (F x) (F y) t (refl F e) P')
        → Id (Σ X (z ↦ Id H (F z) t)) (x, P) (y, P'))
      (P' s ↦ refl ((w ↦ (x, w)) : Id H (F x) t → Σ X (z ↦ Id H (F z) t))
        (concat (Id H (F x) t) P (concat H (F x) (F x) t (refl (F x)) P') P' s (concat_1p H (F x) t P')))
      y e P' s

{` The path algebra behind λ, ρ and α of the wild slice. `}
def wild_slice_lu_algebra (H : Type) (u v w t : H) (A : Id H u v) (R : Id H v w) (L : Id H u w)
  (p : Id H w t) (tri : Id (Id H u w) (concat H u v w A R) L)
  : Id (Id H u t) (concat H u v t A (concat H v w t R p)) (concat H u w t L p)
  ≔ concat (Id H u t) (concat H u v t A (concat H v w t R p)) (concat H u w t (concat H u v w A R) p)
      (concat H u w t L p)
      (inverse (Id H u t) (concat H u w t (concat H u v w A R) p) (concat H u v t A (concat H v w t R p))
        (concat_assoc H u v w t A R p))
      (refl ((r ↦ concat H u w t r p) : Id H u w → Id H u t) tri)

def wild_slice_ru_algebra (H : Type) (n0 n1 n2 n3 m : H) (A : Id H n0 n1) (W : Id H n1 n2)
  (r0 : Id H n2 n3) (rm : Id H n1 m) (p : Id H m n3) (L : Id H n0 m)
  (nat : Id (Id H n1 n3) (concat H n1 n2 n3 W r0) (concat H n1 m n3 rm p))
  (tri : Id (Id H n0 m) (concat H n0 n1 m A rm) L)
  : Id (Id H n0 n3) (concat H n0 n1 n3 A (concat H n1 n2 n3 W r0)) (concat H n0 m n3 L p)
  ≔ calc
      concat H n0 n1 n3 A (concat H n1 n2 n3 W r0)
      = concat H n0 n1 n3 A (concat H n1 m n3 rm p) by refl (concat H n0 n1 n3 A) nat
      = concat H n0 m n3 (concat H n0 n1 m A rm) p
        by inverse (Id H n0 n3) (concat H n0 m n3 (concat H n0 n1 m A rm) p)
             (concat H n0 n1 n3 A (concat H n1 m n3 rm p)) (concat_assoc H n0 n1 m n3 A rm p)
      = concat H n0 m n3 L p by refl ((r ↦ concat H n0 m n3 r p) : Id H n0 m → Id H n0 n3) tri ∎

def wild_slice_assoc_algebra (H : Type) (n0 n1 n2 n3 n4 n5 m1 o1 o2 : H)
  (A1 : Id H n0 n1) (Wr : Id H n1 n2) (A2 : Id H n2 n3) (Wq : Id H n3 n4) (p : Id H n4 n5)
  (al : Id H n1 m1) (Whg : Id H m1 n3)
  (E : Id H n0 o1) (A3 : Id H o1 o2) (A4g : Id H o2 m1) (Rq : Id H o2 n4)
  (nat : Id (Id H n1 n3) (concat H n1 n2 n3 Wr A2) (concat H n1 m1 n3 al Whg))
  (pent : Id (Id H n0 m1) (concat H n0 o1 m1 E (concat H o1 o2 m1 A3 A4g)) (concat H n0 n1 m1 A1 al))
  (mpc : Id (Id H o2 n4) Rq (concat H o2 m1 n4 A4g (concat H m1 n3 n4 Whg Wq)))
  : Id (Id H n0 n5)
      (concat H n0 n1 n5 A1 (concat H n1 n2 n5 Wr (concat H n2 n3 n5 A2 (concat H n3 n4 n5 Wq p))))
      (concat H n0 o1 n5 E (concat H o1 o2 n5 A3 (concat H o2 n4 n5 Rq p)))
  ≔ let qp ≔ concat H n3 n4 n5 Wq p in
    calc
      concat H n0 n1 n5 A1 (concat H n1 n2 n5 Wr (concat H n2 n3 n5 A2 qp))
      = concat H n0 n1 n5 A1 (concat H n1 n3 n5 (concat H n1 n2 n3 Wr A2) qp)
        by refl (concat H n0 n1 n5 A1)
             (inverse (Id H n1 n5) (concat H n1 n3 n5 (concat H n1 n2 n3 Wr A2) qp)
               (concat H n1 n2 n5 Wr (concat H n2 n3 n5 A2 qp)) (concat_assoc H n1 n2 n3 n5 Wr A2 qp))
      = concat H n0 n1 n5 A1 (concat H n1 n3 n5 (concat H n1 m1 n3 al Whg) qp)
        by refl (concat H n0 n1 n5 A1)
             (refl ((r ↦ concat H n1 n3 n5 r qp) : Id H n1 n3 → Id H n1 n5) nat)
      = concat H n0 n1 n5 A1 (concat H n1 m1 n5 al (concat H m1 n3 n5 Whg qp))
        by refl (concat H n0 n1 n5 A1) (concat_assoc H n1 m1 n3 n5 al Whg qp)
      = concat H n0 m1 n5 (concat H n0 n1 m1 A1 al) (concat H m1 n3 n5 Whg qp)
        by inverse (Id H n0 n5) (concat H n0 m1 n5 (concat H n0 n1 m1 A1 al) (concat H m1 n3 n5 Whg qp))
             (concat H n0 n1 n5 A1 (concat H n1 m1 n5 al (concat H m1 n3 n5 Whg qp)))
             (concat_assoc H n0 n1 m1 n5 A1 al (concat H m1 n3 n5 Whg qp))
      = concat H n0 m1 n5 (concat H n0 o1 m1 E (concat H o1 o2 m1 A3 A4g)) (concat H m1 n3 n5 Whg qp)
        by refl ((r ↦ concat H n0 m1 n5 r (concat H m1 n3 n5 Whg qp)) : Id H n0 m1 → Id H n0 n5)
             (inverse (Id H n0 m1) (concat H n0 o1 m1 E (concat H o1 o2 m1 A3 A4g)) (concat H n0 n1 m1 A1 al) pent)
      = concat H n0 o1 n5 E (concat H o1 m1 n5 (concat H o1 o2 m1 A3 A4g) (concat H m1 n3 n5 Whg qp))
        by concat_assoc H n0 o1 m1 n5 E (concat H o1 o2 m1 A3 A4g) (concat H m1 n3 n5 Whg qp)
      = concat H n0 o1 n5 E (concat H o1 o2 n5 A3 (concat H o2 m1 n5 A4g (concat H m1 n3 n5 Whg qp)))
        by refl (concat H n0 o1 n5 E) (concat_assoc H o1 o2 m1 n5 A3 A4g (concat H m1 n3 n5 Whg qp))
      = concat H n0 o1 n5 E (concat H o1 o2 n5 A3 (concat H o2 m1 n5 A4g (concat H m1 n4 n5 (concat H m1 n3 n4 Whg Wq) p)))
        by refl (concat H n0 o1 n5 E) (refl (concat H o1 o2 n5 A3) (refl (concat H o2 m1 n5 A4g)
             (inverse (Id H m1 n5) (concat H m1 n4 n5 (concat H m1 n3 n4 Whg Wq) p) (concat H m1 n3 n5 Whg qp)
               (concat_assoc H m1 n3 n4 n5 Whg Wq p))))
      = concat H n0 o1 n5 E (concat H o1 o2 n5 A3 (concat H o2 n4 n5 (concat H o2 m1 n4 A4g (concat H m1 n3 n4 Whg Wq)) p))
        by refl (concat H n0 o1 n5 E) (refl (concat H o1 o2 n5 A3)
             (inverse (Id H o2 n5) (concat H o2 n4 n5 (concat H o2 m1 n4 A4g (concat H m1 n3 n4 Whg Wq)) p)
               (concat H o2 m1 n5 A4g (concat H m1 n4 n5 (concat H m1 n3 n4 Whg Wq) p))
               (concat_assoc H o2 m1 n4 n5 A4g (concat H m1 n3 n4 Whg Wq) p)))
      = concat H n0 o1 n5 E (concat H o1 o2 n5 A3 (concat H o2 n4 n5 Rq p))
        by refl (concat H n0 o1 n5 E) (refl (concat H o1 o2 n5 A3)
             (refl ((r ↦ concat H o2 n4 n5 r p) : Id H o2 n4 → Id H o2 n5)
               (inverse (Id H o2 n4) Rq (concat H o2 m1 n4 A4g (concat H m1 n3 n4 Whg Wq)) mpc))) ∎

{` def:slice-cat, the wild case: from the three coherences, the slice of a
   wild precategory is a wild precategory with the same objects, arrows,
   identities and composition as above. `}
def coherent_wild_slice (C : WildPrecat) (tl : WildTriangleCoherence C) (tr : WildRightTriangleFiller C)
  (pent : WildPentagon C) (c : C .ob) : WildPrecat
  ≔ (ob ≔ SliceOb C c,
     hom ≔ SliceHom C c,
     idn ≔ slice_idn C c,
     comp ≔ slice_comp C c,
     lu ≔ x y f ↦
       let a ≔ x .fst in let b ≔ y .fst in
       wild_slice_sigma_path (C .hom a b) (C .hom a c) (t ↦ C .comp a b c (y .snd) t) (x .snd)
         (C .comp a b b (C .idn b) (f .fst)) (f .fst) (C .lu a b (f .fst))
         (slice_comp C c x y y (slice_idn C c y) f .snd) (f .snd)
         (wild_slice_lu_algebra (C .hom a c) (C .comp a b c (y .snd) (C .comp a b b (C .idn b) (f .fst)))
           (C .comp a b c (C .comp b b c (y .snd) (C .idn b)) (f .fst)) (C .comp a b c (y .snd) (f .fst)) (x .snd)
           (C .assoc a b b c (f .fst) (C .idn b) (y .snd))
           (cat_whisker_right C a b c (C .comp b b c (y .snd) (C .idn b)) (y .snd) (f .fst) (C .ru b c (y .snd)))
           (cat_whisker_left C a b c (y .snd) (C .comp a b b (C .idn b) (f .fst)) (f .fst) (C .lu a b (f .fst)))
           (f .snd) (tl a b c (f .fst) (y .snd))),
     ru ≔ x y f ↦
       let a ≔ x .fst in let b ≔ y .fst in
       wild_slice_sigma_path (C .hom a b) (C .hom a c) (t ↦ C .comp a b c (y .snd) t) (x .snd)
         (C .comp a a b (f .fst) (C .idn a)) (f .fst) (C .ru a b (f .fst))
         (slice_comp C c x x y f (slice_idn C c x) .snd) (f .snd)
         (wild_slice_ru_algebra (C .hom a c) (C .comp a b c (y .snd) (C .comp a a b (f .fst) (C .idn a)))
           (C .comp a a c (C .comp a b c (y .snd) (f .fst)) (C .idn a)) (C .comp a a c (x .snd) (C .idn a)) (x .snd)
           (C .comp a b c (y .snd) (f .fst))
           (C .assoc a a b c (C .idn a) (f .fst) (y .snd))
           (cat_whisker_right C a a c (C .comp a b c (y .snd) (f .fst)) (x .snd) (C .idn a) (f .snd))
           (C .ru a c (x .snd)) (C .ru a c (C .comp a b c (y .snd) (f .fst))) (f .snd)
           (cat_whisker_left C a b c (y .snd) (C .comp a a b (f .fst) (C .idn a)) (f .fst) (C .ru a b (f .fst)))
           (naturality (C .hom a c) (C .hom a c) (m ↦ C .comp a a c m (C .idn a)) (m ↦ m) (m ↦ C .ru a c m)
             (C .comp a b c (y .snd) (f .fst)) (x .snd) (f .snd))
           (tr a b c (f .fst) (y .snd))),
     assoc ≔ x0 x1 x2 x3 g h k ↦
       let A0 ≔ x0 .fst in let A1 ≔ x1 .fst in let A2 ≔ x2 .fst in let A3 ≔ x3 .fst in
       let f1 ≔ x1 .snd in let f2 ≔ x2 .snd in let f3 ≔ x3 .snd in
       let gg ≔ g .fst in let hh ≔ h .fst in let kk ≔ k .fst in
       let H ≔ C .hom A0 c in
       let hg ≔ C .comp A0 A1 A2 hh gg in
       let kh ≔ C .comp A1 A2 A3 kk hh in
       let f3k ≔ C .comp A2 A3 c f3 kk in
       wild_slice_sigma_path (C .hom A0 A3) H (t ↦ C .comp A0 A3 c f3 t) (x0 .snd)
         (C .comp A0 A2 A3 kk hg) (C .comp A0 A1 A3 kh gg) (C .assoc A0 A1 A2 A3 gg hh kk)
         (slice_comp C c x0 x2 x3 k (slice_comp C c x0 x1 x2 h g) .snd)
         (slice_comp C c x0 x1 x3 (slice_comp C c x1 x2 x3 k h) g .snd)
         (wild_slice_assoc_algebra H
           (C .comp A0 A3 c f3 (C .comp A0 A2 A3 kk hg))
           (C .comp A0 A2 c f3k hg)
           (C .comp A0 A2 c f2 hg)
           (C .comp A0 A1 c (C .comp A1 A2 c f2 hh) gg)
           (C .comp A0 A1 c f1 gg)
           (x0 .snd)
           (C .comp A0 A1 c (C .comp A1 A2 c f3k hh) gg)
           (C .comp A0 A3 c f3 (C .comp A0 A1 A3 kh gg))
           (C .comp A0 A1 c (C .comp A1 A3 c f3 kh) gg)
           (C .assoc A0 A2 A3 c hg kk f3)
           (cat_whisker_right C A0 A2 c f3k f2 hg (k .snd))
           (C .assoc A0 A1 A2 c gg hh f2)
           (cat_whisker_right C A0 A1 c (C .comp A1 A2 c f2 hh) f1 gg (h .snd))
           (g .snd)
           (C .assoc A0 A1 A2 c gg hh f3k)
           (cat_whisker_right C A0 A1 c (C .comp A1 A2 c f3k hh) (C .comp A1 A2 c f2 hh) gg
             (cat_whisker_right C A1 A2 c f3k f2 hh (k .snd)))
           (cat_whisker_left C A0 A3 c f3 (C .comp A0 A2 A3 kk hg) (C .comp A0 A1 A3 kh gg)
             (C .assoc A0 A1 A2 A3 gg hh kk))
           (C .assoc A0 A1 A3 c gg kh f3)
           (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) (C .comp A1 A2 c f3k hh) gg
             (C .assoc A1 A2 A3 c hh kk f3))
           (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) f1 gg (slice_comp C c x1 x2 x3 k h .snd))
           (naturality (C .hom A2 c) H (m ↦ C .comp A0 A2 c m hg) (m ↦ C .comp A0 A1 c (C .comp A1 A2 c m hh) gg)
             (m ↦ C .assoc A0 A1 A2 c gg hh m) f3k f2 (k .snd))
           (pent A0 A1 A2 A3 c gg hh kk f3)
           (concat (Id H (C .comp A0 A1 c (C .comp A1 A3 c f3 kh) gg) (C .comp A0 A1 c f1 gg))
             (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) f1 gg (slice_comp C c x1 x2 x3 k h .snd))
             (concat H (C .comp A0 A1 c (C .comp A1 A3 c f3 kh) gg) (C .comp A0 A1 c (C .comp A1 A2 c f3k hh) gg)
               (C .comp A0 A1 c f1 gg)
               (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) (C .comp A1 A2 c f3k hh) gg
                 (C .assoc A1 A2 A3 c hh kk f3))
               (cat_whisker_right C A0 A1 c (C .comp A1 A2 c f3k hh) f1 gg
                 (concat (C .hom A1 c) (C .comp A1 A2 c f3k hh) (C .comp A1 A2 c f2 hh) f1
                   (cat_whisker_right C A1 A2 c f3k f2 hh (k .snd)) (h .snd))))
             (concat H (C .comp A0 A1 c (C .comp A1 A3 c f3 kh) gg) (C .comp A0 A1 c (C .comp A1 A2 c f3k hh) gg)
               (C .comp A0 A1 c f1 gg)
               (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) (C .comp A1 A2 c f3k hh) gg
                 (C .assoc A1 A2 A3 c hh kk f3))
               (concat H (C .comp A0 A1 c (C .comp A1 A2 c f3k hh) gg) (C .comp A0 A1 c (C .comp A1 A2 c f2 hh) gg)
                 (C .comp A0 A1 c f1 gg)
                 (cat_whisker_right C A0 A1 c (C .comp A1 A2 c f3k hh) (C .comp A1 A2 c f2 hh) gg
                   (cat_whisker_right C A1 A2 c f3k f2 hh (k .snd)))
                 (cat_whisker_right C A0 A1 c (C .comp A1 A2 c f2 hh) f1 gg (h .snd))))
             (map_path_concat (C .hom A1 c) H (m ↦ C .comp A0 A1 c m gg)
               (C .comp A1 A3 c f3 kh) (C .comp A1 A2 c f3k hh) f1
               (C .assoc A1 A2 A3 c hh kk f3)
               (concat (C .hom A1 c) (C .comp A1 A2 c f3k hh) (C .comp A1 A2 c f2 hh) f1
                 (cat_whisker_right C A1 A2 c f3k f2 hh (k .snd)) (h .snd)))
             (refl (concat H (C .comp A0 A1 c (C .comp A1 A3 c f3 kh) gg) (C .comp A0 A1 c (C .comp A1 A2 c f3k hh) gg)
                 (C .comp A0 A1 c f1 gg)
                 (cat_whisker_right C A0 A1 c (C .comp A1 A3 c f3 kh) (C .comp A1 A2 c f3k hh) gg
                   (C .assoc A1 A2 A3 c hh kk f3)))
               (map_path_concat (C .hom A1 c) H (m ↦ C .comp A0 A1 c m gg)
                 (C .comp A1 A2 c f3k hh) (C .comp A1 A2 c f2 hh) f1
                 (cat_whisker_right C A1 A2 c f3k f2 hh (k .snd)) (h .snd))))))

{` The projection fst : C/c → C also exists for the wild slice. `}
def coherent_wild_slice_projection (C : WildPrecat) (tl : WildTriangleCoherence C)
  (tr : WildRightTriangleFiller C) (pent : WildPentagon C) (c : C .ob)
  : WildFunctor (coherent_wild_slice C tl tr pent c) C
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y g ↦ g .fst,
     map_id ≔ x ↦ refl (C .idn (x .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) (g .fst) (f .fst)))

{` The wild category of types has all three coherences (its λ, ρ and α
   are reflexivities; the other two are type_wild_triangle and
   type_wild_pentagon of module 604), so its slices are wild
   precategories. `}
def type_wild_right_triangle : WildRightTriangleFiller TypeWild
  ≔ a b c g f ↦ concat_p1 (a → c) (x ↦ f (g x)) (x ↦ f (g x)) (refl (x ↦ f (g x)))

{` xca:univ-slice-cat: the slice of the universe U/B. Objects (A, f : A → B),
   arrows (g, f' ∘ g = f) with identifications of functions, identities
   (id, refl), composite (h ∘ g, ap(- ∘ g)(q) · p); λ, ρ, α from the unit and
   associativity laws of path composition. `}
def UniverseSliceOb (B : Type) : Type ≔ Σ Type (A ↦ A → B)

def UniverseSliceHom (B : Type) (x y : UniverseSliceOb B) : Type
  ≔ Σ (x .fst → y .fst) (g ↦ Id (x .fst → B) (z ↦ y .snd (g z)) (x .snd))

def universe_slice_comp (B : Type) (x y z : UniverseSliceOb B) (k : UniverseSliceHom B y z)
  (h : UniverseSliceHom B x y) : UniverseSliceHom B x z
  ≔ (w ↦ k .fst (h .fst w),
     concat (x .fst → B) (w ↦ z .snd (k .fst (h .fst w))) (w ↦ y .snd (h .fst w)) (x .snd)
       (refl ((m ↦ (w ↦ m (h .fst w))) : (y .fst → B) → (x .fst → B)) (k .snd)) (h .snd))

def universe_slice_assoc_path (B : Type) (x y z u : UniverseSliceOb B) (f : UniverseSliceHom B x y)
  (g : UniverseSliceHom B y z) (h : UniverseSliceHom B z u)
  : Id (Id (x .fst → B) (w ↦ u .snd (h .fst (g .fst (f .fst w)))) (x .snd))
      (universe_slice_comp B x z u h (universe_slice_comp B x y z g f) .snd)
      (universe_slice_comp B x y u (universe_slice_comp B y z u h g) f .snd)
  ≔ let X ≔ x .fst → B in
    let F : (y .fst → B) → X ≔ m ↦ w ↦ m (f .fst w) in
    let G : (z .fst → B) → (y .fst → B) ≔ m ↦ w ↦ m (g .fst w) in
    let e1 : X ≔ w ↦ u .snd (h .fst (g .fst (f .fst w))) in
    let e2 : X ≔ w ↦ z .snd (g .fst (f .fst w)) in
    let e3 : X ≔ w ↦ y .snd (f .fst w) in
    calc
      concat X e1 e2 (x .snd) (refl F (refl G (h .snd))) (concat X e2 e3 (x .snd) (refl F (g .snd)) (f .snd))
      = concat X e1 e3 (x .snd) (concat X e1 e2 e3 (refl F (refl G (h .snd))) (refl F (g .snd))) (f .snd)
        by inverse (Id X e1 (x .snd))
             (concat X e1 e3 (x .snd) (concat X e1 e2 e3 (refl F (refl G (h .snd))) (refl F (g .snd))) (f .snd))
             (concat X e1 e2 (x .snd) (refl F (refl G (h .snd))) (concat X e2 e3 (x .snd) (refl F (g .snd)) (f .snd)))
             (concat_assoc X e1 e2 e3 (x .snd) (refl F (refl G (h .snd))) (refl F (g .snd)) (f .snd))
      = concat X e1 e3 (x .snd)
          (refl F (concat (y .fst → B) (w ↦ u .snd (h .fst (g .fst w))) (w ↦ z .snd (g .fst w)) (y .snd)
            (refl G (h .snd)) (g .snd)))
          (f .snd)
        by refl ((r ↦ concat X e1 e3 (x .snd) r (f .snd)) : Id X e1 e3 → Id X e1 (x .snd))
             (inverse (Id X e1 e3)
               (refl F (concat (y .fst → B) (w ↦ u .snd (h .fst (g .fst w))) (w ↦ z .snd (g .fst w)) (y .snd)
                 (refl G (h .snd)) (g .snd)))
               (concat X e1 e2 e3 (refl F (refl G (h .snd))) (refl F (g .snd)))
               (map_path_concat (y .fst → B) X F (w ↦ u .snd (h .fst (g .fst w))) (w ↦ z .snd (g .fst w)) (y .snd)
                 (refl G (h .snd)) (g .snd))) ∎

def universe_slice_wild (B : Type) : WildPrecat
  ≔ (ob ≔ UniverseSliceOb B,
     hom ≔ UniverseSliceHom B,
     idn ≔ x ↦ (w ↦ w, refl (x .snd)),
     comp ≔ universe_slice_comp B,
     lu ≔ x y f ↦ refl ((t ↦ (f .fst, t)) : Id (x .fst → B) (w ↦ y .snd (f .fst w)) (x .snd) → UniverseSliceHom B x y)
       (concat_1p (x .fst → B) (w ↦ y .snd (f .fst w)) (x .snd) (f .snd)),
     ru ≔ x y f ↦ refl ((t ↦ (f .fst, t)) : Id (x .fst → B) (w ↦ y .snd (f .fst w)) (x .snd) → UniverseSliceHom B x y)
       (concat_p1 (x .fst → B) (w ↦ y .snd (f .fst w)) (x .snd) (f .snd)),
     assoc ≔ x y z u f g h ↦
       refl ((t ↦ (w ↦ h .fst (g .fst (f .fst w)), t))
           : Id (x .fst → B) (w ↦ u .snd (h .fst (g .fst (f .fst w)))) (x .snd) → UniverseSliceHom B x u)
         (universe_slice_assoc_path B x y z u f g h))

{` The projection U/B → U, and univalence of U/B ("for particular wild
   categories, it may very well happen that C/c is again a wild category"):
   an arrow (h, q) of U/B is an isomorphism exactly when h is an
   equivalence (by equivalence induction and path induction on q), and the
   type of objects with an isomorphism from (A, f) is a retract of a
   contractible type. `}
def universe_slice_projection (B : Type) : WildFunctor (universe_slice_wild B) TypeWild
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y g ↦ g .fst,
     map_id ≔ x ↦ refl ((w ↦ w) : x .fst → x .fst),
     map_comp ≔ x y z f g ↦ refl ((w ↦ g .fst (f .fst w)) : x .fst → z .fst))

def universe_slice_identity_iso (B : Type) (A : Type) (f f' : A → B) (q : Id (A → B) f' f)
  : CatIsIso (universe_slice_wild B) (A, f) (A, f') (w ↦ w, q)
  ≔ J (A → B) f' (f q ↦ CatIsIso (universe_slice_wild B) (A, f) (A, f') (w ↦ w, q))
      (cat_identity_is_iso (universe_slice_wild B) (A, f')) f q

def universe_slice_iso_from_equiv (B : Type) (x y : UniverseSliceOb B) (h : UniverseSliceHom B x y)
  (he : isEquiv (x .fst) (y .fst) (h .fst)) : CatIsIso (universe_slice_wild B) x y h
  ≔ equivalence_induction (x .fst)
      (A' e ↦ (f' : A' → B) (q : Id (x .fst → B) (z ↦ f' (e .map z)) (x .snd))
        → CatIsIso (universe_slice_wild B) x (A', f') (e .map, q))
      (f' q ↦ universe_slice_identity_iso B (x .fst) (x .snd) f' q)
      (y .fst) (h .fst, he) (y .snd) (h .snd)

def universe_slice_univalent (B : Type) : IsUnivalentCat (universe_slice_wild B)
  ≔ cat_univalent_from_contractible (universe_slice_wild B) (x ↦
      let S ≔ universe_slice_wild B in
      let AE ≔ Σ Type (A' ↦ CatIso TypeWild (x .fst) A') in
      let Fb : AE → Type ≔ ae ↦ Fiber (ae .fst → B) (x .fst → B) (k ↦ (z ↦ k (ae .snd .fst z))) (x .snd) in
      let T ≔ Σ (UniverseSliceOb B) (y ↦ CatIso S x y) in
      contractible_retract (Σ AE Fb) T
        (sigma_contractible AE Fb (cat_univalent_iso_total_contractible TypeWild type_wild_univalent (x .fst))
          (ae ↦ cat_precompose_equiv TypeWild (x .fst) (ae .fst) (ae .snd .fst) (ae .snd .snd) B .equiv (x .snd)))
        (t ↦ ((t .fst .fst, t .snd .fst),
              ((t .fst .snd .fst, t .snd .snd),
               universe_slice_iso_from_equiv B x (t .fst .fst, t .snd .fst) (t .fst .snd .fst, t .snd .snd)
                 (type_is_iso_to_equiv (x .fst) (t .fst .fst) (t .fst .snd .fst) (t .fst .snd .snd)))))
        (s ↦ ((s .fst .fst,
               (s .snd .fst .fst,
                functor_preserves_iso S TypeWild (universe_slice_projection B) x (s .fst) (s .snd .fst) (s .snd .snd))),
              (s .fst .snd, s .snd .fst .snd)))
        (s ↦ refl ((w ↦ (s .fst, w)) : CatIso S x (s .fst) → T)
          (cat_iso_path S x (s .fst)
            (s .snd .fst,
             universe_slice_iso_from_equiv B x (s .fst) (s .snd .fst)
               (type_is_iso_to_equiv (x .fst) (s .fst .fst) (s .snd .fst .fst)
                 (functor_preserves_iso S TypeWild (universe_slice_projection B) x (s .fst) (s .snd .fst) (s .snd .snd))))
            (s .snd) (refl (s .snd .fst)))))

def UniverseSliceCategory (B : Type) : WildCategory ≔ (universe_slice_wild B, universe_slice_univalent B)

{` Litmus: in U/Bool, the arrow (Unit, const true) → (Bool, id) given by
   const true, and its composite with not : (Bool, id) → (Bool, not). `}
def universe_slice_litmus_point : UniverseSliceOb Bool ≔ (Unit, _ ↦ true.)
def universe_slice_litmus_id : UniverseSliceOb Bool ≔ (Bool, x ↦ x)
def universe_slice_litmus_not : UniverseSliceOb Bool ≔ (Bool, bool_not)

def universe_slice_litmus_arrow : UniverseSliceHom Bool universe_slice_litmus_point universe_slice_litmus_id
  ≔ (_ ↦ true., refl ((_ ↦ true.) : Unit → Bool))

def universe_slice_litmus_not_arrow : UniverseSliceHom Bool universe_slice_litmus_id universe_slice_litmus_not
  ≔ (bool_not, funext Bool (_ ↦ Bool) (x ↦ bool_not (bool_not x)) (x ↦ x) bool_not_involutive)

def universe_slice_litmus_composite
  : Id Bool (universe_slice_wild Bool .comp universe_slice_litmus_point universe_slice_litmus_id
      universe_slice_litmus_not universe_slice_litmus_not_arrow universe_slice_litmus_arrow .fst star.) false.
  ≔ refl (false. : Bool)

{` The general wild slice of the wild category of types has the same
   objects and arrows as U/B. `}
def universe_slice_coherent_ob (B : Type)
  : Id Type (coherent_wild_slice TypeWild type_wild_triangle type_wild_right_triangle type_wild_pentagon B .ob)
      (universe_slice_wild B .ob)
  ≔ refl (UniverseSliceOb B)

def universe_slice_coherent_hom (B : Type) (x y : UniverseSliceOb B)
  : Id Type (coherent_wild_slice TypeWild type_wild_triangle type_wild_right_triangle type_wild_pentagon B .hom x y)
      (universe_slice_wild B .hom x y)
  ≔ refl (UniverseSliceHom B x y)
