export "603-adjunctions-and-equivalences"
export "162-pointed-maps"

{` Chapter 6 (cats.tex), rem:wild and the list of examples after
   def:category: the wild category of pointed types (with the unit and
   associativity laws "left as an exercise"), the wild category of
   families over a type, the univalence of both, and the coherence
   conditions that a wild precategory does not require: the identification
   of λ and ρ at an identity, the triangle of the footnote to rem:wild and
   the pentagon eq:pentagon. `}

{` rem:wild: the unit laws and the associativity law for pointed maps with
   the composition (g_÷ f_÷, g_÷(f_pt) g_pt) of def:pointedtypes
   (book_pointed_compose) and the pointed identity (id, refl) of
   def:pointedidentity. The underlying maps agree judgmentally; the
   pointing paths are identified by the path-groupoid laws. `}
def pointed_wild_lu (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) (book_pointed_compose A B B f (book_pointed_identity B)) f
  ≔ (refl (f .fst), concat_1p (B .carrier) (B .point) (f .fst (A .point)) (f .snd))

def pointed_wild_ru (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) (book_pointed_compose A A B (book_pointed_identity A) f) f
  ≔ (refl (f .fst), concat_p1 (B .carrier) (B .point) (f .fst (A .point)) (f .snd))

def pointed_wild_assoc (A B C D : Pointed) (f : BookPointedMap A B) (g : BookPointedMap B C)
  (h : BookPointedMap C D)
  : Id (BookPointedMap A D)
      (book_pointed_compose A C D (book_pointed_compose A B C f g) h)
      (book_pointed_compose A B D f (book_pointed_compose B C D g h))
  ≔ let C0 ≔ C .carrier in
    let D0 ≔ D .carrier in
    let pa ≔ A .point in
    let pb ≔ B .point in
    let pc ≔ C .point in
    let pd ≔ D .point in
    let hp ≔ refl (h .fst) (g .snd) in
    let hgp ≔ refl (h .fst) (refl (g .fst) (f .snd)) in
    (refl (x ↦ h .fst (g .fst (f .fst x))),
     concat (Id D0 pd (h .fst (g .fst (f .fst pa))))
       (concat D0 pd (h .fst pc) (h .fst (g .fst (f .fst pa))) (h .snd)
         (refl (h .fst) (concat C0 pc (g .fst pb) (g .fst (f .fst pa)) (g .snd) (refl (g .fst) (f .snd)))))
       (concat D0 pd (h .fst pc) (h .fst (g .fst (f .fst pa))) (h .snd)
         (concat D0 (h .fst pc) (h .fst (g .fst pb)) (h .fst (g .fst (f .fst pa))) hp hgp))
       (concat D0 pd (h .fst (g .fst pb)) (h .fst (g .fst (f .fst pa)))
         (concat D0 pd (h .fst pc) (h .fst (g .fst pb)) (h .snd) hp) hgp)
       (refl (concat D0 pd (h .fst pc) (h .fst (g .fst (f .fst pa))) (h .snd))
         (map_path_concat C0 D0 (h .fst) pc (g .fst pb) (g .fst (f .fst pa)) (g .snd) (refl (g .fst) (f .snd))))
       (inverse (Id D0 pd (h .fst (g .fst (f .fst pa))))
         (concat D0 pd (h .fst (g .fst pb)) (h .fst (g .fst (f .fst pa)))
           (concat D0 pd (h .fst pc) (h .fst (g .fst pb)) (h .snd) hp) hgp)
         (concat D0 pd (h .fst pc) (h .fst (g .fst (f .fst pa))) (h .snd)
           (concat D0 (h .fst pc) (h .fst (g .fst pb)) (h .fst (g .fst (f .fst pa))) hp hgp))
         (concat_assoc D0 pd (h .fst pc) (h .fst (g .fst pb)) (h .fst (g .fst (f .fst pa))) (h .snd) hp hgp)))

{` rem:wild and the second example after def:category: the wild
   precategory of pointed types, objects Pointed (= U_*) and arrows the
   pointed maps X →* Y of def:pointedtypes. `}
def PointedWild : WildPrecat
  ≔ (ob ≔ Pointed,
     hom ≔ A B ↦ BookPointedMap A B,
     idn ≔ A ↦ book_pointed_identity A,
     comp ≔ A B C g f ↦ book_pointed_compose A B C f g,
     lu ≔ A B f ↦ pointed_wild_lu A B f,
     ru ≔ A B f ↦ pointed_wild_ru A B f,
     assoc ≔ A B C D f g h ↦ pointed_wild_assoc A B C D f g h)

{` "The wild category of pointed types": it is univalent. An isomorphism of
   pointed types has an underlying biinvertible map; conversely every
   pointed map whose underlying map is an equivalence is an isomorphism,
   by induction on the contractible type of pointed equivalences out of X
   (module 162). `}
def pointed_iso_underlying_equiv (X Y : Pointed) (f : BookPointedMap X Y) (i : CatIsIso PointedWild X Y f)
  : Equiv (X .carrier) (Y .carrier)
  ≔ biinvertible_equiv (X .carrier) (Y .carrier) (f .fst)
      (i .fst .fst .fst) (y ↦ i .fst .snd .fst (refl y))
      (i .snd .fst .fst) (x ↦ i .snd .snd .fst (refl x))

def pointed_identity_equivalence (X : Pointed) : BookPointedEquiv X X
  ≔ (book_pointed_identity X, book_equivalence (X .carrier) (X .carrier) (identity_equiv (X .carrier)) .equiv)

def pointed_equivalence_is_iso (X : Pointed) (u : Σ Pointed (Y ↦ BookPointedEquiv X Y))
  : CatIsIso PointedWild X (u .fst) (u .snd .fst)
  ≔ let T ≔ Σ Pointed (Y ↦ BookPointedEquiv X Y) in
    let c ≔ pointed_equivalences_total_contractible X in
    let t0 : T ≔ (X, pointed_identity_equivalence X) in
    transport T (v ↦ CatIsIso PointedWild X (v .fst) (v .snd .fst)) t0 u
      (concat T t0 (c .center) u (inverse T (c .center) t0 (c .contract t0)) (c .contract u))
      (cat_identity_is_iso PointedWild X)

def pointed_iso_book_equiv (X Y : Pointed) (f : BookPointedMap X Y)
  : Equiv (CatIsIso PointedWild X Y f) (BookIsEquiv (X .carrier) (Y .carrier) (f .fst))
  ≔ iff_equiv (CatIsIso PointedWild X Y f) (BookIsEquiv (X .carrier) (Y .carrier) (f .fst))
      (cat_is_iso_prop PointedWild X Y f) (book_isequiv_isprop (X .carrier) (Y .carrier) (f .fst))
      (i ↦ book_equivalence (X .carrier) (Y .carrier) (pointed_iso_underlying_equiv X Y f i) .equiv)
      (e ↦ pointed_equivalence_is_iso X (Y, (f, e)))

def pointed_iso_total_equiv (X : Pointed)
  : Equiv (Σ Pointed (Y ↦ CatIso PointedWild X Y)) (Σ Pointed (Y ↦ BookPointedEquiv X Y))
  ≔ family_equiv Pointed (Y ↦ CatIso PointedWild X Y) (Y ↦ BookPointedEquiv X Y)
      (Y ↦ family_equiv (BookPointedMap X Y) (f ↦ CatIsIso PointedWild X Y f)
        (f ↦ BookIsEquiv (X .carrier) (Y .carrier) (f .fst)) (f ↦ pointed_iso_book_equiv X Y f))

def pointed_wild_univalent : IsUnivalentCat PointedWild
  ≔ cat_univalent_from_contractible PointedWild (X ↦
      hlevel_equiv zero. (Σ Pointed (Y ↦ BookPointedEquiv X Y)) (Σ Pointed (Y ↦ CatIso PointedWild X Y))
        (canonical_inverse_equiv (Σ Pointed (Y ↦ CatIso PointedWild X Y)) (Σ Pointed (Y ↦ BookPointedEquiv X Y))
          (pointed_iso_total_equiv X))
        (native_contraction (Σ Pointed (Y ↦ BookPointedEquiv X Y)) (pointed_equivalences_total_contractible X)))

def PointedWildCategory : WildCategory ≔ (PointedWild, pointed_wild_univalent)

{` Third example after def:category: the wild category of families over a
   type X, objects X → U and arrows the fiberwise maps ∏_{x:X} A(x) → B(x)
   (def:fiberwise); identities, composition and laws are pointwise and
   judgmental. `}
def FamilyWild (X : Type) : WildPrecat
  ≔ (ob ≔ X → Type,
     hom ≔ A B ↦ (x : X) → A x → B x,
     idn ≔ A ↦ x a ↦ a,
     comp ≔ A B C g f ↦ x a ↦ g x (f x a),
     lu ≔ A B f ↦ refl f,
     ru ≔ A B f ↦ refl f,
     assoc ≔ A B C D f g h ↦ refl ((x a ↦ h x (g x (f x a))) : (x : X) → A x → D x))

{` Isomorphisms of families are the fiberwise equivalences. `}
def family_iso_fiberwise_equiv (X : Type) (A B : X → Type) (f : (x : X) → A x → B x)
  (i : CatIsIso (FamilyWild X) A B f) (x : X) : isEquiv (A x) (B x) (f x)
  ≔ biinvertible_equiv (A x) (B x) (f x)
      (i .fst .fst x) (b ↦ i .fst .snd (refl x) (refl b))
      (i .snd .fst x) (a ↦ i .snd .snd (refl x) (refl a)) .equiv

def family_fiberwise_equiv_iso (X : Type) (A B : X → Type) (f : (x : X) → A x → B x)
  (e : (x : X) → isEquiv (A x) (B x) (f x)) : CatIsIso (FamilyWild X) A B f
  ≔ let g : (x : X) → B x → A x ≔ x ↦ equiv_inverse_map (A x) (B x) (f x, e x) in
    ((g, funext X (x ↦ B x → B x) (x b ↦ f x (g x b)) (x b ↦ b)
           (x ↦ funext (B x) (_ ↦ B x) (b ↦ f x (g x b)) (b ↦ b) (equiv_counit (A x) (B x) (f x, e x)))),
     (g, funext X (x ↦ A x → A x) (x a ↦ g x (f x a)) (x a ↦ a)
           (x ↦ funext (A x) (_ ↦ A x) (a ↦ g x (f x a)) (a ↦ a) (equiv_retraction (A x) (B x) (f x, e x)))))

def family_iso_path_equiv (X : Type) (A B : X → Type)
  : Equiv (Id (X → Type) A B) (CatIso (FamilyWild X) A B)
  ≔ let Fib ≔ (x : X) → Σ (A x → B x) (isEquiv (A x) (B x)) in
    let Tot ≔ Σ ((x : X) → A x → B x) (f ↦ (x : X) → isEquiv (A x) (B x) (f x)) in
    compose_equiv (Id (X → Type) A B) (Homotopy X (_ ↦ Type) A B) (CatIso (FamilyWild X) A B)
      (function_extensionality X (_ ↦ Type) A B)
      (compose_equiv (Homotopy X (_ ↦ Type) A B) ((x : X) → Equiv (A x) (B x)) (CatIso (FamilyWild X) A B)
        (pi_family_equiv X (x ↦ Id Type (A x) (B x)) (x ↦ Equiv (A x) (B x)) (x ↦ univalence_equiv (A x) (B x)))
        (compose_equiv ((x : X) → Equiv (A x) (B x)) Fib (CatIso (FamilyWild X) A B)
          (pi_family_equiv X (x ↦ Equiv (A x) (B x)) (x ↦ Σ (A x → B x) (isEquiv (A x) (B x)))
            (x ↦ equiv_sigma_equiv (A x) (B x)))
          (compose_equiv Fib Tot (CatIso (FamilyWild X) A B)
            (choice_equiv X (x ↦ A x → B x) (x f ↦ isEquiv (A x) (B x) f))
            (family_equiv ((x : X) → A x → B x) (f ↦ (x : X) → isEquiv (A x) (B x) (f x))
              (f ↦ CatIsIso (FamilyWild X) A B f)
              (f ↦ iff_equiv ((x : X) → isEquiv (A x) (B x) (f x)) (CatIsIso (FamilyWild X) A B f)
                (pi_prop X (x ↦ isEquiv (A x) (B x) (f x)) (x ↦ isequiv_isprop (A x) (B x) (f x)))
                (cat_is_iso_prop (FamilyWild X) A B f)
                (family_fiberwise_equiv_iso X A B f)
                (i ↦ family_iso_fiberwise_equiv X A B f i))))))

def family_wild_univalent (X : Type) : IsUnivalentCat (FamilyWild X)
  ≔ cat_univalent_from_equivalences (FamilyWild X) (family_iso_path_equiv X)

def FamilyWildCategory (X : Type) : WildCategory ≔ (FamilyWild X, family_wild_univalent X)

{` rem:wild, the coherences that are NOT part of a wild precategory.
   (1) An identification of λ and ρ at an identity, both of type
   id_A ∘ id_A = id_A. `}
def WildUnitCoherence (C : WildPrecat) : Type
  ≔ (a : C .ob) → Id (Id (C .hom a a) (C .comp a a a (C .idn a) (C .idn a)) (C .idn a))
      (C .lu a a (C .idn a)) (C .ru a a (C .idn a))

{` (2) The triangle in the footnote to rem:wild: for g : A → B and
   f : B → C, the composite of α : f ∘ (id ∘ g) = (f ∘ id) ∘ g with
   ap_{- ∘ g}(ρ) agrees with ap_{f ∘ -}(λ). `}
def WildTriangleCoherence (C : WildPrecat) : Type
  ≔ (a b c : C .ob) (g : C .hom a b) (f : C .hom b c)
    → Id (Id (C .hom a c) (C .comp a b c f (C .comp a b b (C .idn b) g)) (C .comp a b c f g))
        (concat (C .hom a c) (C .comp a b c f (C .comp a b b (C .idn b) g))
          (C .comp a b c (C .comp b b c f (C .idn b)) g) (C .comp a b c f g)
          (C .assoc a b b c g (C .idn b) f)
          (cat_whisker_right C a b c (C .comp b b c f (C .idn b)) f g (C .ru b c f)))
        (cat_whisker_left C a b c f (C .comp a b b (C .idn b) g) g (C .lu a b g))

{` (3) eq:pentagon. For f : A → B, g : B → C, h : C → D, k : D → E the
   vertices are P0 = k∘(h∘(g∘f)), P1 = k∘((h∘g)∘f), P2 = (k∘(h∘g))∘f,
   P3 = ((k∘h)∘g)∘f and P4 = (k∘h)∘(g∘f); a filler identifies the path
   P0 → P1 → P2 → P3 (ap_{k∘-}(α), α, ap_{-∘f}(α)) with P0 → P4 → P3
   (α, α). `}
def wild_pentagon_left (C : WildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c)
  (h : C .hom c d) (k : C .hom d e)
  : Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
      (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
  ≔ let P0 ≔ C .comp a d e k (C .comp a c d h (C .comp a b c g f)) in
    let P1 ≔ C .comp a d e k (C .comp a b d (C .comp b c d h g) f) in
    let P2 ≔ C .comp a b e (C .comp b d e k (C .comp b c d h g)) f in
    let P3 ≔ C .comp a b e (C .comp b c e (C .comp c d e k h) g) f in
    concat (C .hom a e) P0 P1 P3
      (cat_whisker_left C a d e k (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f)
        (C .assoc a b c d f g h))
      (concat (C .hom a e) P1 P2 P3
        (C .assoc a b d e f (C .comp b c d h g) k)
        (cat_whisker_right C a b e (C .comp b d e k (C .comp b c d h g)) (C .comp b c e (C .comp c d e k h) g) f
          (C .assoc b c d e g h k)))

def wild_pentagon_right (C : WildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c)
  (h : C .hom c d) (k : C .hom d e)
  : Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
      (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
  ≔ concat (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
      (C .comp a c e (C .comp c d e k h) (C .comp a b c g f))
      (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f)
      (C .assoc a c d e (C .comp a b c g f) h k)
      (C .assoc a b c e f g (C .comp c d e k h))

{` The type of fillers of eq:pentagon for one quadruple of composable
   arrows, and the type of pentagon structures (fillers for all
   quadruples). `}
def WildPentagonFiller (C : WildPrecat) (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d)
  (k : C .hom d e) : Type
  ≔ Id (Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
        (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f))
      (wild_pentagon_left C a b c d e f g h k) (wild_pentagon_right C a b c d e f g h k)

def WildPentagon (C : WildPrecat) : Type
  ≔ (a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) (k : C .hom d e)
    → Id (Id (C .hom a e) (C .comp a d e k (C .comp a c d h (C .comp a b c g f)))
          (C .comp a b e (C .comp b c e (C .comp c d e k h) g) f))
        (wild_pentagon_left C a b c d e f g h k) (wild_pentagon_right C a b c d e f g h k)

def wild_pentagon_fillers (C : WildPrecat)
  : Id Type (WildPentagon C)
      ((a b c d e : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) (k : C .hom d e)
        → WildPentagonFiller C a b c d e f g h k)
  ≔ refl (WildPentagon C)

{` In the wild category of types (λ, ρ, α reflexivities) all three
   coherences hold. `}
def type_wild_unit_coherence : WildUnitCoherence TypeWild
  ≔ A ↦ refl (refl ((x ↦ x) : A → A))

def type_wild_triangle : WildTriangleCoherence TypeWild
  ≔ A B C g f ↦ concat_p1 (A → C) (x ↦ f (g x)) (x ↦ f (g x)) (refl ((x ↦ f (g x)) : A → C))

def type_wild_pentagon : WildPentagon TypeWild
  ≔ A B C D E f g h k ↦
      let P : A → E ≔ x ↦ k (h (g (f x))) in
      refl (concat (A → E) P P P (refl P)) (concat_1p (A → E) P P (refl P))

{` "When the types of morphisms hom(A,B) are sets, then the types of λ, ρ
   and α are propositions, so any coherence conditions are automatically
   fulfilled." `}
def precat_left_unit_prop (C : WildPrecat) (hs : HasHomSets C)
  : isProp ((a b : C .ob) (f : C .hom a b) → Id (C .hom a b) (C .comp a b b (C .idn b) f) f)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b) → Id (C .hom a b) (C .comp a b b (C .idn b) f) f)
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b) → Id (C .hom a b) (C .comp a b b (C .idn b) f) f)
        (b ↦ pi_prop (C .hom a b) (f ↦ Id (C .hom a b) (C .comp a b b (C .idn b) f) f)
          (f ↦ hs a b (C .comp a b b (C .idn b) f) f)))

def precat_right_unit_prop (C : WildPrecat) (hs : HasHomSets C)
  : isProp ((a b : C .ob) (f : C .hom a b) → Id (C .hom a b) (C .comp a a b f (C .idn a)) f)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b) → Id (C .hom a b) (C .comp a a b f (C .idn a)) f)
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b) → Id (C .hom a b) (C .comp a a b f (C .idn a)) f)
        (b ↦ pi_prop (C .hom a b) (f ↦ Id (C .hom a b) (C .comp a a b f (C .idn a)) f)
          (f ↦ hs a b (C .comp a a b f (C .idn a)) f)))

def precat_assoc_prop (C : WildPrecat) (hs : HasHomSets C) (a b c d : C .ob)
  (f : C .hom a b) (g : C .hom b c) (h : C .hom c d)
  : isProp (Id (C .hom a d) (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f))
  ≔ hs a d (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f)

def precat_unit_coherence (C : Precat) : WildUnitCoherence (C .wild)
  ≔ a ↦ C .homset a a (C .wild .comp a a a (C .wild .idn a) (C .wild .idn a)) (C .wild .idn a)
      (C .wild .lu a a (C .wild .idn a)) (C .wild .ru a a (C .wild .idn a))

def precat_triangle_coherence (C : Precat) : WildTriangleCoherence (C .wild)
  ≔ a b c g f ↦
      let W ≔ C .wild in
      C .homset a c (W .comp a b c f (W .comp a b b (W .idn b) g)) (W .comp a b c f g)
        (concat (W .hom a c) (W .comp a b c f (W .comp a b b (W .idn b) g))
          (W .comp a b c (W .comp b b c f (W .idn b)) g) (W .comp a b c f g)
          (W .assoc a b b c g (W .idn b) f)
          (cat_whisker_right W a b c (W .comp b b c f (W .idn b)) f g (W .ru b c f)))
        (cat_whisker_left W a b c f (W .comp a b b (W .idn b) g) g (W .lu a b g))

def precat_pentagon (C : Precat) : WildPentagon (C .wild)
  ≔ a b c d e f g h k ↦
      let W ≔ C .wild in
      C .homset a e (W .comp a d e k (W .comp a c d h (W .comp a b c g f)))
        (W .comp a b e (W .comp b c e (W .comp c d e k h) g) f)
        (wild_pentagon_left W a b c d e f g h k) (wild_pentagon_right W a b c d e f g h k)

{` Litmus checks. Pointed composition computes the book's pointing path
   g_÷(f_pt)·g_pt, here for the negation (Bool, true) →* (Bool, false). `}
def pointed_bool_true : Pointed ≔ (Bool, true.)
def pointed_bool_false : Pointed ≔ (Bool, false.)

def pointed_bool_negation (X Y : Bool) : BookPointedMap (Bool, X) (Bool, bool_not X)
  ≔ (bool_not, refl (bool_not X))

def pointed_wild_composite_point (X Y Z : Pointed) (f : BookPointedMap X Y) (g : BookPointedMap Y Z)
  : Id (Id (Z .carrier) (Z .point) (g .fst (f .fst (X .point))))
      (PointedWild .comp X Y Z g f .snd)
      (concat (Z .carrier) (Z .point) (g .fst (Y .point)) (g .fst (f .fst (X .point))) (g .snd)
        (refl (g .fst) (f .snd)))
  ≔ refl (PointedWild .comp X Y Z g f .snd)

def pointed_wild_negation_twice
  : Id Bool (PointedWild .comp pointed_bool_true pointed_bool_false pointed_bool_true
      (pointed_bool_negation false. true.) (pointed_bool_negation true. true.) .fst true.) true.
  ≔ refl (true. : Bool)

def pointed_bool_negation_iso : CatIso PointedWild pointed_bool_true pointed_bool_false
  ≔ (pointed_bool_negation true. true.,
     pointed_equivalence_is_iso pointed_bool_true
       (pointed_bool_false, (pointed_bool_negation true. true.,
         book_equivalence Bool Bool bool_not_equiv .equiv)))

{` Univalence turns this isomorphism into an identification of pointed
   types, although Bool pointed at true and at false are different pairs. `}
def pointed_bool_true_false_path : Id Pointed pointed_bool_true pointed_bool_false
  ≔ cat_isotoid PointedWild pointed_wild_univalent pointed_bool_true pointed_bool_false pointed_bool_negation_iso

{` Families: composition is pointwise. `}
def family_wild_composite_check (f g : (b : Bool) → BoolFamily Unit Bool b → BoolFamily Unit Bool b)
  : Id (BoolFamily Unit Bool true.)
      (FamilyWild Bool .comp (BoolFamily Unit Bool) (BoolFamily Unit Bool) (BoolFamily Unit Bool) g f true. true.)
      (g true. (f true. true.))
  ≔ refl (g true. (f true. true.))
