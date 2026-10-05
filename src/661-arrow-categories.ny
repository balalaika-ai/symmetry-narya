export "660-slice-categories"

{` Chapter 6 (cats.tex), ex:arrow-cat: the arrow precategory C^→ of a
   precategory, the functors dom and cod, and univalence of C^→ for a
   category C.

   Objects are triples (A, B, f : A → B). An arrow (A, B, f) → (A', B', f')
   is a pair (g : A → A', h : B → B') with a filler of the square
   f' ∘ g = h ∘ f. `}

def ArrowCatOb (C : WildPrecat) : Type ≔ Σ (C .ob) (a ↦ Σ (C .ob) (b ↦ C .hom a b))

def ArrowCatSquare (C : WildPrecat) (x y : ArrowCatOb C) (g : C .hom (x .fst) (y .fst))
  (h : C .hom (x .snd .fst) (y .snd .fst)) : Type
  ≔ Id (C .hom (x .fst) (y .snd .fst))
      (C .comp (x .fst) (y .fst) (y .snd .fst) (y .snd .snd) g)
      (C .comp (x .fst) (x .snd .fst) (y .snd .fst) h (x .snd .snd))

def ArrowCatHomPair (C : WildPrecat) (x y : ArrowCatOb C) : Type
  ≔ Product (C .hom (x .fst) (y .fst)) (C .hom (x .snd .fst) (y .snd .fst))

def ArrowCatHom (C : WildPrecat) (x y : ArrowCatOb C) : Type
  ≔ Σ (ArrowCatHomPair C x y) (gh ↦ ArrowCatSquare C x y (gh .fst) (gh .snd))

def arrow_cat_idn (C : WildPrecat) (x : ArrowCatOb C) : ArrowCatHom C x x
  ≔ let a ≔ x .fst in let b ≔ x .snd .fst in let f ≔ x .snd .snd in
    ((C .idn a, C .idn b),
     concat (C .hom a b) (C .comp a a b f (C .idn a)) f (C .comp a b b (C .idn b) f)
       (C .ru a b f) (inverse (C .hom a b) (C .comp a b b (C .idn b) f) f (C .lu a b f)))

def arrow_cat_comp_square (C : WildPrecat) (x y z : ArrowCatOb C) (k : ArrowCatHom C y z) (h : ArrowCatHom C x y)
  : ArrowCatSquare C x z (C .comp (x .fst) (y .fst) (z .fst) (k .fst .fst) (h .fst .fst))
      (C .comp (x .snd .fst) (y .snd .fst) (z .snd .fst) (k .fst .snd) (h .fst .snd))
  ≔ let a ≔ x .fst in let b ≔ x .snd .fst in let f ≔ x .snd .snd in
    let a' ≔ y .fst in let b' ≔ y .snd .fst in let f' ≔ y .snd .snd in
    let a'' ≔ z .fst in let b'' ≔ z .snd .fst in let f'' ≔ z .snd .snd in
    let g ≔ h .fst .fst in let hh ≔ h .fst .snd in
    let g' ≔ k .fst .fst in let hh' ≔ k .fst .snd in
    calc
      C .comp a a'' b'' f'' (C .comp a a' a'' g' g)
      = C .comp a a' b'' (C .comp a' a'' b'' f'' g') g by C .assoc a a' a'' b'' g g' f''
      = C .comp a a' b'' (C .comp a' b' b'' hh' f') g
        by cat_whisker_right C a a' b'' (C .comp a' a'' b'' f'' g') (C .comp a' b' b'' hh' f') g (k .snd)
      = C .comp a b' b'' hh' (C .comp a a' b' f' g)
        by inverse (C .hom a b'') (C .comp a b' b'' hh' (C .comp a a' b' f' g))
             (C .comp a a' b'' (C .comp a' b' b'' hh' f') g) (C .assoc a a' b' b'' g f' hh')
      = C .comp a b' b'' hh' (C .comp a b b' hh f)
        by cat_whisker_left C a b' b'' hh' (C .comp a a' b' f' g) (C .comp a b b' hh f) (h .snd)
      = C .comp a b b'' (C .comp b b' b'' hh' hh) f by C .assoc a b b' b'' f hh hh' ∎

def arrow_cat_comp (C : WildPrecat) (x y z : ArrowCatOb C) (k : ArrowCatHom C y z) (h : ArrowCatHom C x y) : ArrowCatHom C x z
  ≔ ((C .comp (x .fst) (y .fst) (z .fst) (k .fst .fst) (h .fst .fst),
      C .comp (x .snd .fst) (y .snd .fst) (z .snd .fst) (k .fst .snd) (h .fst .snd)),
     arrow_cat_comp_square C x y z k h)

{` In a precategory the square fillers form a proposition, so arrows of
   C^→ are determined by their pairs of arrows. `}
def arrow_cat_square_prop (C : WildPrecat) (hs : HasHomSets C) (x y : ArrowCatOb C) (gh : ArrowCatHomPair C x y)
  : isProp (ArrowCatSquare C x y (gh .fst) (gh .snd))
  ≔ hs (x .fst) (y .snd .fst) (C .comp (x .fst) (y .fst) (y .snd .fst) (y .snd .snd) (gh .fst))
      (C .comp (x .fst) (x .snd .fst) (y .snd .fst) (gh .snd) (x .snd .snd))

def arrow_cat_hom_path (C : WildPrecat) (hs : HasHomSets C) (x y : ArrowCatOb C) (u v : ArrowCatHom C x y)
  (p : Id (ArrowCatHomPair C x y) (u .fst) (v .fst)) : Id (ArrowCatHom C x y) u v
  ≔ (p, pathover_of_eq (ArrowCatHomPair C x y) (gh ↦ ArrowCatSquare C x y (gh .fst) (gh .snd)) (u .fst) (v .fst) p
        (u .snd) (v .snd)
        (arrow_cat_square_prop C hs x y (v .fst)
          (transport (ArrowCatHomPair C x y) (gh ↦ ArrowCatSquare C x y (gh .fst) (gh .snd)) (u .fst) (v .fst) p (u .snd))
          (v .snd)))

def arrow_precat_wild (C : WildPrecat) (hs : HasHomSets C) : WildPrecat
  ≔ (ob ≔ ArrowCatOb C,
     hom ≔ ArrowCatHom C,
     idn ≔ arrow_cat_idn C,
     comp ≔ arrow_cat_comp C,
     lu ≔ x y f ↦ arrow_cat_hom_path C hs x y (arrow_cat_comp C x y y (arrow_cat_idn C y) f) f
       (C .lu (x .fst) (y .fst) (f .fst .fst), C .lu (x .snd .fst) (y .snd .fst) (f .fst .snd)),
     ru ≔ x y f ↦ arrow_cat_hom_path C hs x y (arrow_cat_comp C x x y f (arrow_cat_idn C x)) f
       (C .ru (x .fst) (y .fst) (f .fst .fst), C .ru (x .snd .fst) (y .snd .fst) (f .fst .snd)),
     assoc ≔ x y z w f g h ↦ arrow_cat_hom_path C hs x w
       (arrow_cat_comp C x z w h (arrow_cat_comp C x y z g f)) (arrow_cat_comp C x y w (arrow_cat_comp C y z w h g) f)
       (C .assoc (x .fst) (y .fst) (z .fst) (w .fst) (f .fst .fst) (g .fst .fst) (h .fst .fst),
        C .assoc (x .snd .fst) (y .snd .fst) (z .snd .fst) (w .snd .fst) (f .fst .snd) (g .fst .snd) (h .fst .snd)))

def arrow_cat_homset (C : WildPrecat) (hs : HasHomSets C) : HasHomSets (arrow_precat_wild C hs)
  ≔ x y ↦ sigma_set (ArrowCatHomPair C x y) (gh ↦ ArrowCatSquare C x y (gh .fst) (gh .snd))
      (product_set (C .hom (x .fst) (y .fst)) (C .hom (x .snd .fst) (y .snd .fst))
        (hs (x .fst) (y .fst)) (hs (x .snd .fst) (y .snd .fst)))
      (gh ↦ prop_is_set (ArrowCatSquare C x y (gh .fst) (gh .snd)) (arrow_cat_square_prop C hs x y gh))

def ArrowPrecat (C : Precat) : Precat
  ≔ (arrow_precat_wild (C .wild) (C .homset), arrow_cat_homset (C .wild) (C .homset))

{` ex:arrow-cat: the functors dom, cod : C^→ → C. `}
def arrow_cat_dom (C : WildPrecat) (hs : HasHomSets C) : WildFunctor (arrow_precat_wild C hs) C
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y u ↦ u .fst .fst,
     map_id ≔ x ↦ refl (C .idn (x .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) (g .fst .fst) (f .fst .fst)))

def arrow_cat_cod (C : WildPrecat) (hs : HasHomSets C) : WildFunctor (arrow_precat_wild C hs) C
  ≔ (obj ≔ x ↦ x .snd .fst,
     mor ≔ x y u ↦ u .fst .snd,
     map_id ≔ x ↦ refl (C .idn (x .snd .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .snd .fst) (y .snd .fst) (z .snd .fst) (g .fst .snd) (f .fst .snd)))

{` Isomorphisms of C^→ are the arrows whose two components are
   isomorphisms of C. `}
def arrow_cat_iso_to_dom (C : WildPrecat) (hs : HasHomSets C) (x y : ArrowCatOb C) (u : ArrowCatHom C x y)
  (i : CatIsIso (arrow_precat_wild C hs) x y u) : CatIsIso C (x .fst) (y .fst) (u .fst .fst)
  ≔ ((i .fst .fst .fst .fst, i .fst .snd .fst .fst), (i .snd .fst .fst .fst, i .snd .snd .fst .fst))

def arrow_cat_iso_to_cod (C : WildPrecat) (hs : HasHomSets C) (x y : ArrowCatOb C) (u : ArrowCatHom C x y)
  (i : CatIsIso (arrow_precat_wild C hs) x y u) : CatIsIso C (x .snd .fst) (y .snd .fst) (u .fst .snd)
  ≔ ((i .fst .fst .fst .snd, i .fst .snd .fst .snd), (i .snd .fst .fst .snd, i .snd .snd .fst .snd))

def arrow_cat_inverse_square (C : WildPrecat) (x y : ArrowCatOb C) (u : ArrowCatHom C x y)
  (gm : C .hom (y .fst) (x .fst))
  (gg : Id (C .hom (y .fst) (y .fst)) (C .comp (y .fst) (x .fst) (y .fst) (u .fst .fst) gm) (C .idn (y .fst)))
  (hm : C .hom (y .snd .fst) (x .snd .fst))
  (hl : Id (C .hom (x .snd .fst) (x .snd .fst)) (C .comp (x .snd .fst) (y .snd .fst) (x .snd .fst) hm (u .fst .snd))
          (C .idn (x .snd .fst)))
  : ArrowCatSquare C y x gm hm
  ≔ let a ≔ x .fst in let b ≔ x .snd .fst in let f ≔ x .snd .snd in
    let a' ≔ y .fst in let b' ≔ y .snd .fst in let f' ≔ y .snd .snd in
    let g ≔ u .fst .fst in let h ≔ u .fst .snd in
    calc
      C .comp a' a b f gm
      = C .comp a' b b (C .idn b) (C .comp a' a b f gm)
        by inverse (C .hom a' b) (C .comp a' b b (C .idn b) (C .comp a' a b f gm)) (C .comp a' a b f gm)
             (C .lu a' b (C .comp a' a b f gm))
      = C .comp a' b b (C .comp b b' b hm h) (C .comp a' a b f gm)
        by cat_whisker_right C a' b b (C .idn b) (C .comp b b' b hm h) (C .comp a' a b f gm)
             (inverse (C .hom b b) (C .comp b b' b hm h) (C .idn b) hl)
      = C .comp a' b' b hm (C .comp a' b b' h (C .comp a' a b f gm))
        by inverse (C .hom a' b) (C .comp a' b' b hm (C .comp a' b b' h (C .comp a' a b f gm)))
             (C .comp a' b b (C .comp b b' b hm h) (C .comp a' a b f gm))
             (C .assoc a' b b' b (C .comp a' a b f gm) h hm)
      = C .comp a' b' b hm (C .comp a' a b' (C .comp a b b' h f) gm)
        by cat_whisker_left C a' b' b hm (C .comp a' b b' h (C .comp a' a b f gm)) (C .comp a' a b' (C .comp a b b' h f) gm)
             (C .assoc a' a b b' gm f h)
      = C .comp a' b' b hm (C .comp a' a b' (C .comp a a' b' f' g) gm)
        by cat_whisker_left C a' b' b hm (C .comp a' a b' (C .comp a b b' h f) gm) (C .comp a' a b' (C .comp a a' b' f' g) gm)
             (cat_whisker_right C a' a b' (C .comp a b b' h f) (C .comp a a' b' f' g) gm
               (inverse (C .hom a b') (C .comp a a' b' f' g) (C .comp a b b' h f) (u .snd)))
      = C .comp a' b' b hm (C .comp a' a' b' f' (C .comp a' a a' g gm))
        by cat_whisker_left C a' b' b hm (C .comp a' a b' (C .comp a a' b' f' g) gm) (C .comp a' a' b' f' (C .comp a' a a' g gm))
             (inverse (C .hom a' b') (C .comp a' a' b' f' (C .comp a' a a' g gm)) (C .comp a' a b' (C .comp a a' b' f' g) gm)
               (C .assoc a' a a' b' gm g f'))
      = C .comp a' b' b hm (C .comp a' a' b' f' (C .idn a'))
        by cat_whisker_left C a' b' b hm (C .comp a' a' b' f' (C .comp a' a a' g gm)) (C .comp a' a' b' f' (C .idn a'))
             (cat_whisker_left C a' a' b' f' (C .comp a' a a' g gm) (C .idn a') gg)
      = C .comp a' b' b hm f'
        by cat_whisker_left C a' b' b hm (C .comp a' a' b' f' (C .idn a')) f' (C .ru a' b' f') ∎

def arrow_cat_iso_from_components (C : WildPrecat) (hs : HasHomSets C) (x y : ArrowCatOb C) (u : ArrowCatHom C x y)
  (gi : CatIsIso C (x .fst) (y .fst) (u .fst .fst)) (hi : CatIsIso C (x .snd .fst) (y .snd .fst) (u .fst .snd))
  : CatIsIso (arrow_precat_wild C hs) x y u
  ≔ let gm ≔ gi .fst .fst in
    let hm ≔ hi .fst .fst in
    let gl : Id (C .hom (x .fst) (x .fst)) (C .comp (x .fst) (y .fst) (x .fst) gm (u .fst .fst)) (C .idn (x .fst))
      ≔ cat_iso_inverse C (x .fst) (y .fst) (u .fst .fst, gi) .snd .fst .snd in
    let hl : Id (C .hom (x .snd .fst) (x .snd .fst))
               (C .comp (x .snd .fst) (y .snd .fst) (x .snd .fst) hm (u .fst .snd)) (C .idn (x .snd .fst))
      ≔ cat_iso_inverse C (x .snd .fst) (y .snd .fst) (u .fst .snd, hi) .snd .fst .snd in
    let v : ArrowCatHom C y x ≔ ((gm, hm), arrow_cat_inverse_square C x y u gm (gi .fst .snd) hm hl) in
    ((v, arrow_cat_hom_path C hs y y (arrow_cat_comp C y x y u v) (arrow_cat_idn C y) (gi .fst .snd, hi .fst .snd)),
     (v, arrow_cat_hom_path C hs x x (arrow_cat_comp C x y x v u) (arrow_cat_idn C x) (gl, hl)))

{` ex:arrow-cat: "C^→ is a category if C is". For a fixed (a, b, f), the
   type of pairs of an object and an isomorphism from (a, b, f) is a
   retract of a type of pairs of isomorphisms a ≅ a', b ≅ b' and an element
   of a fiber of precomposition with the first, which is contractible. `}
def arrow_cat_univalent (C : WildPrecat) (hs : HasHomSets C) (un : IsUnivalentCat C)
  : IsUnivalentCat (arrow_precat_wild C hs)
  ≔ cat_univalent_from_contractible (arrow_precat_wild C hs) (x ↦
      let Ar ≔ arrow_precat_wild C hs in
      let a ≔ x .fst in let b ≔ x .snd .fst in let f ≔ x .snd .snd in
      let AE ≔ Σ (C .ob) (a' ↦ CatIso C a a') in
      let BE ≔ Σ (C .ob) (b' ↦ CatIso C b b') in
      let Fb : AE → BE → Type
        ≔ ae be ↦ Fiber (C .hom (ae .fst) (be .fst)) (C .hom a (be .fst))
            (k ↦ C .comp a (ae .fst) (be .fst) k (ae .snd .fst)) (C .comp a b (be .fst) (be .snd .fst) f) in
      let T ≔ Σ (ArrowCatOb C) (y ↦ CatIso Ar x y) in
      contractible_retract (Σ AE (ae ↦ Σ BE (be ↦ Fb ae be))) T
        (sigma_contractible AE (ae ↦ Σ BE (be ↦ Fb ae be)) (cat_univalent_iso_total_contractible C un a)
          (ae ↦ sigma_contractible BE (be ↦ Fb ae be) (cat_univalent_iso_total_contractible C un b)
            (be ↦ cat_precompose_equiv C a (ae .fst) (ae .snd .fst) (ae .snd .snd) (be .fst) .equiv
                    (C .comp a b (be .fst) (be .snd .fst) f))))
        (t ↦
          let y : ArrowCatOb C ≔ (t .fst .fst, (t .snd .fst .fst, t .snd .snd .fst)) in
          let uu : ArrowCatHom C x y ≔ ((t .fst .snd .fst, t .snd .fst .snd .fst), t .snd .snd .snd) in
          (y, (uu, arrow_cat_iso_from_components C hs x y uu (t .fst .snd .snd) (t .snd .fst .snd .snd))))
        (s ↦ ((s .fst .fst, (s .snd .fst .fst .fst, arrow_cat_iso_to_dom C hs x (s .fst) (s .snd .fst) (s .snd .snd))),
              ((s .fst .snd .fst, (s .snd .fst .fst .snd, arrow_cat_iso_to_cod C hs x (s .fst) (s .snd .fst) (s .snd .snd))),
               (s .fst .snd .snd, s .snd .fst .snd))))
        (s ↦ refl ((w ↦ (s .fst, w)) : CatIso Ar x (s .fst) → T)
          (cat_iso_path Ar x (s .fst)
            (s .snd .fst,
             arrow_cat_iso_from_components C hs x (s .fst) (s .snd .fst)
               (arrow_cat_iso_to_dom C hs x (s .fst) (s .snd .fst) (s .snd .snd))
               (arrow_cat_iso_to_cod C hs x (s .fst) (s .snd .fst) (s .snd .snd)))
            (s .snd) (refl (s .snd .fst)))))

def ArrowCategory (C : Category) : Category
  ≔ (arrow_precat_wild (C .wild) (C .homset), arrow_cat_homset (C .wild) (C .homset),
     arrow_cat_univalent (C .wild) (C .homset) (C .univalent))

{` Litmus checks in the arrow category of sets: objects (Unit, Bool,
   const true) and (Unit, Bool, const false). The pair (id, not) is an arrow
   (false = not true by refl), the pair (id, id) is not. `}
def arrow_cat_litmus_true : ArrowCatOb (SetCat .wild) ≔ ((Unit, unit_set), ((Bool, bool_set), _ ↦ true.))
def arrow_cat_litmus_false : ArrowCatOb (SetCat .wild) ≔ ((Unit, unit_set), ((Bool, bool_set), _ ↦ false.))

def arrow_cat_litmus_arrow : ArrowCatHom (SetCat .wild) arrow_cat_litmus_true arrow_cat_litmus_false
  ≔ ((x ↦ x, bool_not), refl ((_ ↦ false.) : Unit → Bool))

def arrow_cat_litmus_no_identity_arrow
  (s : ArrowCatSquare (SetCat .wild) arrow_cat_litmus_true arrow_cat_litmus_false (x ↦ x) (x ↦ x)) : Empty
  ≔ bool_encode false. true. (s (refl (star. : Unit)))

def arrow_cat_litmus_dom_cod
  : Product
      (Id (Unit → Unit) (arrow_cat_dom (SetCat .wild) (SetCat .homset) .mor arrow_cat_litmus_true arrow_cat_litmus_false
         arrow_cat_litmus_arrow) (x ↦ x))
      (Id Bool (arrow_cat_cod (SetCat .wild) (SetCat .homset) .mor arrow_cat_litmus_true arrow_cat_litmus_false
         arrow_cat_litmus_arrow true.) false.)
  ≔ (refl ((x ↦ x) : Unit → Unit), refl (false. : Bool))
