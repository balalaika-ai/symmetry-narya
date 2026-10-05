export "472-bicycle-normality"

{` group.tex 2134–2204: the subsets H_x of words fixing x, the exercises
   at group.tex 2142 (normal iff all H_x agree) and 2178 (words identified
   by ⟦-⟧(x₀) iff same meaning), and rem:bicycle-list-concat. `}

{` Two words with the same value at x give a word fixing x, and conversely. `}
def bicycle_words_same_point (X : Type) (a b : Equiv X X) (x : X) (l1 l2 : List (Sum Int Int))
  (p : Id X (bicycle_meaning_map X a b l1 x) (bicycle_meaning_map X a b l2 x))
  : Id X (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse l2) l1) x) x
  ≔ calc
      bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse l2) l1) x
      = bicycle_meaning_map X a b (bicycle_word_inverse l2) (bicycle_meaning_map X a b l1 x)
        by bicycle_meaning_append X a b (bicycle_word_inverse l2) l1 x
      = bicycle_meaning_map X a b (bicycle_word_inverse l2) (bicycle_meaning_map X a b l2 x)
        by refl (bicycle_meaning_map X a b (bicycle_word_inverse l2)) p
      = bicycle_meaning_inverse_map X a b l2 (bicycle_meaning_map X a b l2 x)
        by bicycle_meaning_word_inverse X a b l2 (bicycle_meaning_map X a b l2 x)
      = x by bicycle_meaning_retraction X a b l2 x ∎

def bicycle_words_from_fixed (X : Type) (a b : Equiv X X) (y : X) (l1 l2 : List (Sum Int Int))
  (q : Id X (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse l2) l1) y) y)
  : Id X (bicycle_meaning_map X a b l1 y) (bicycle_meaning_map X a b l2 y)
  ≔ calc
      bicycle_meaning_map X a b l1 y
      = bicycle_meaning_map X a b l2 (bicycle_meaning_inverse_map X a b l2 (bicycle_meaning_map X a b l1 y))
        by inverse X (bicycle_meaning_map X a b l2 (bicycle_meaning_inverse_map X a b l2 (bicycle_meaning_map X a b l1 y)))
          (bicycle_meaning_map X a b l1 y) (bicycle_meaning_section X a b l2 (bicycle_meaning_map X a b l1 y))
      = bicycle_meaning_map X a b l2 (bicycle_meaning_map X a b (bicycle_word_inverse l2) (bicycle_meaning_map X a b l1 y))
        by refl (bicycle_meaning_map X a b l2)
          (inverse X (bicycle_meaning_map X a b (bicycle_word_inverse l2) (bicycle_meaning_map X a b l1 y))
            (bicycle_meaning_inverse_map X a b l2 (bicycle_meaning_map X a b l1 y))
            (bicycle_meaning_word_inverse X a b l2 (bicycle_meaning_map X a b l1 y)))
      = bicycle_meaning_map X a b l2 (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse l2) l1) y)
        by refl (bicycle_meaning_map X a b l2)
          (inverse X (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse l2) l1) y)
            (bicycle_meaning_map X a b (bicycle_word_inverse l2) (bicycle_meaning_map X a b l1 y))
            (bicycle_meaning_append X a b (bicycle_word_inverse l2) l1 y))
      = bicycle_meaning_map X a b l2 y by refl (bicycle_meaning_map X a b l2) q ∎

{` H_x ≔ {ℓ : (Z ⊔ Z)* | ⟦ℓ⟧(x) = x} as an element of Sub((Z ⊔ Z)*). `}
def bicycle_stabilizer (B : Bicycles) (x : bicycle_carrier B) : Subtypes (List (Sum Int Int))
  ≔ l ↦ (Id (bicycle_carrier B) (bicycle_word_map B l x) x, bicycle_carrier_set B (bicycle_word_map B l x) x)

def subtypes_path_inclusion (T : Type) (P Q : Subtypes T) (e : Id (Subtypes T) P Q) : Inclusion T P Q
  ≔ t p ↦ transport PropTypes (R ↦ R .fst) (P t) (Q t) (refl ((R ↦ R t) : Subtypes T → PropTypes) e) p

{` A map of bicycles determined by a point: if H_x ⊆ H'_y, then
   f(⟦ℓ⟧x) ≔ ⟦ℓ⟧'y is well defined (unique choice over the proposition
   BicyclePointImage) and commutes with a, b. `}
def BicyclePointImage (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B') (z : bicycle_carrier B) : Type
  ≔ Σ (bicycle_carrier B') (w ↦ Mere (Σ (List (Sum Int Int)) (l ↦
      Product (Id (bicycle_carrier B) z (bicycle_word_map B l x)) (Id (bicycle_carrier B') w (bicycle_word_map B' l y)))))

def bicycle_point_image_prop (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y)) (z : bicycle_carrier B)
  : isProp (BicyclePointImage B B' x y z)
  ≔ let X ≔ bicycle_carrier B in let Y ≔ bicycle_carrier B' in
    u v ↦ subtype_equal Y
      (w ↦ Mere (Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x)) (Id Y w (bicycle_word_map B' l y)))))
      (w ↦ mere_isprop (Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x)) (Id Y w (bicycle_word_map B' l y)))))
      u v
      (mere_rec (Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x)) (Id Y (u .fst) (bicycle_word_map B' l y))))
        (Id Y (u .fst) (v .fst)) (bicycle_carrier_set B' (u .fst) (v .fst))
        (s ↦ mere_rec (Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x)) (Id Y (v .fst) (bicycle_word_map B' l y))))
          (Id Y (u .fst) (v .fst)) (bicycle_carrier_set B' (u .fst) (v .fst))
          (t ↦ calc
            u .fst = bicycle_word_map B' (s .fst) y by s .snd .snd
            = bicycle_word_map B' (t .fst) y
              by bicycle_words_from_fixed Y (bicycle_a B') (bicycle_b B') y (s .fst) (t .fst)
                (hsub (append (Sum Int Int) (bicycle_word_inverse (t .fst)) (s .fst))
                  (bicycle_words_same_point X (bicycle_a B) (bicycle_b B) x (s .fst) (t .fst)
                    (calc bicycle_word_map B (s .fst) x
                      = z by inverse X z (bicycle_word_map B (s .fst) x) (s .snd .fst)
                      = bicycle_word_map B (t .fst) x by t .snd .fst ∎)))
            = v .fst by inverse Y (v .fst) (bicycle_word_map B' (t .fst) y) (t .snd .snd) ∎)
          (v .snd))
        (u .snd))

def bicycle_point_image_element (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y)) (z : bicycle_carrier B)
  : BicyclePointImage B B' x y z
  ≔ let X ≔ bicycle_carrier B in let Y ≔ bicycle_carrier B' in
    mere_rec (BicycleWordFrom X (bicycle_a B) (bicycle_b B) x z) (BicyclePointImage B B' x y z)
      (bicycle_point_image_prop B B' x y hsub z)
      (w ↦ (bicycle_word_map B' (w .fst) y,
        mere (Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x))
            (Id Y (bicycle_word_map B' (w .fst) y) (bicycle_word_map B' l y))))
          (w .fst, (w .snd, refl (bicycle_word_map B' (w .fst) y)))))
      (bicycle_connectivity B .snd x z)

def bicycle_point_map (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  : bicycle_carrier B → bicycle_carrier B'
  ≔ z ↦ bicycle_point_image_element B B' x y hsub z .fst

def bicycle_point_map_point (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  : Id (bicycle_carrier B') (bicycle_point_map B B' x y hsub x) y
  ≔ refl ((t ↦ t .fst) : BicyclePointImage B B' x y x → bicycle_carrier B')
      (bicycle_point_image_prop B B' x y hsub x (bicycle_point_image_element B B' x y hsub x)
        (y, mere (Σ (List (Sum Int Int)) (l ↦ Product (Id (bicycle_carrier B) x (bicycle_word_map B l x))
            (Id (bicycle_carrier B') y (bicycle_word_map B' l y))))
          (nil., (refl x, refl y))))

{` The image of a letter step: if z ↦ w via ℓ, then s(z) ↦ s'(w) via (letter s) ℓ. `}
def bicycle_point_map_step (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  (letter : Sum Int Int) (z : bicycle_carrier B)
  : Id (bicycle_carrier B') (bicycle_point_map B B' x y hsub (bicycle_word_map B (cons. letter nil.) z))
      (bicycle_word_map B' (cons. letter nil.) (bicycle_point_map B B' x y hsub z))
  ≔ let X ≔ bicycle_carrier B in let Y ≔ bicycle_carrier B' in
    let f ≔ bicycle_point_map B B' x y hsub in
    let z' ≔ bicycle_word_map B (cons. letter nil.) z in
    let P ≔ (w ↦ Σ (List (Sum Int Int)) (l ↦ Product (Id X z (bicycle_word_map B l x)) (Id Y w (bicycle_word_map B' l y))))
      : Y → Type in
    mere_rec (P (f z)) (Id Y (f z') (bicycle_word_map B' (cons. letter nil.) (f z)))
      (bicycle_carrier_set B' (f z') (bicycle_word_map B' (cons. letter nil.) (f z)))
      (s ↦ refl ((t ↦ t .fst) : BicyclePointImage B B' x y z' → Y)
        (bicycle_point_image_prop B B' x y hsub z' (bicycle_point_image_element B B' x y hsub z')
          (bicycle_word_map B' (cons. letter nil.) (f z),
            mere (Σ (List (Sum Int Int)) (l ↦ Product (Id X z' (bicycle_word_map B l x))
                (Id Y (bicycle_word_map B' (cons. letter nil.) (f z)) (bicycle_word_map B' l y))))
              (cons. letter (s .fst),
                (calc z' = bicycle_word_map B (cons. letter nil.) (bicycle_word_map B (s .fst) x)
                     by refl (bicycle_word_map B (cons. letter nil.)) (s .snd .fst)
                   = bicycle_word_map B (cons. letter (s .fst)) x
                     by inverse X (bicycle_word_map B (append (Sum Int Int) (cons. letter nil.) (s .fst)) x)
                       (bicycle_word_map B (cons. letter nil.) (bicycle_word_map B (s .fst) x))
                       (bicycle_meaning_append X (bicycle_a B) (bicycle_b B) (cons. letter nil.) (s .fst) x) ∎,
                 calc bicycle_word_map B' (cons. letter nil.) (f z)
                     = bicycle_word_map B' (cons. letter nil.) (bicycle_word_map B' (s .fst) y)
                       by refl (bicycle_word_map B' (cons. letter nil.)) (s .snd .snd)
                   = bicycle_word_map B' (cons. letter (s .fst)) y
                     by inverse Y (bicycle_word_map B' (append (Sum Int Int) (cons. letter nil.) (s .fst)) y)
                       (bicycle_word_map B' (cons. letter nil.) (bicycle_word_map B' (s .fst) y))
                       (bicycle_meaning_append Y (bicycle_a B') (bicycle_b B') (cons. letter nil.) (s .fst) y) ∎)))))
      (bicycle_point_image_element B B' x y hsub z .snd)

def bicycle_point_map_commutes_a (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  : Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (bicycle_point_map B B' x y hsub)
  ≔ bicycle_point_map_step B B' x y hsub (inl. (pos. (suc. zero.)))

def bicycle_point_map_commutes_b (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (hsub : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  : Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (bicycle_point_map B B' x y hsub)
  ≔ bicycle_point_map_step B B' x y hsub (inr. (pos. (suc. zero.)))

{` If H_x = H'_y (both inclusions), there is an isomorphism of bicycles
   sending x to y. This is the bicycle analogue of lem:IdCycle. `}
def bicycle_iso_from_point (B B' : Bicycles) (x : bicycle_carrier B) (y : bicycle_carrier B')
  (h1 : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' y))
  (h2 : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B' y) (bicycle_stabilizer B x))
  : Σ (BicycleIsomorphisms B B') (e ↦ Id (bicycle_carrier B') (e .fst .map x) y)
  ≔ let X ≔ bicycle_carrier B in let Y ≔ bicycle_carrier B' in
    let f ≔ bicycle_point_map B B' x y h1 in
    let g ≔ bicycle_point_map B' B y x h2 in
    let gf : (z : X) → Id X (g (f z)) z
      ≔ bicycle_commuting_maps_agree X X (bicycle_carrier_set B) (bicycle_a B) (bicycle_b B) (bicycle_a B) (bicycle_b B)
          (bicycle_connectivity B) (z ↦ g (f z)) (z ↦ z)
          (z ↦ concat X (g (f (bicycle_a B .map z))) (g (bicycle_a B' .map (f z))) (bicycle_a B .map (g (f z)))
            (refl g (bicycle_point_map_commutes_a B B' x y h1 z)) (bicycle_point_map_commutes_a B' B y x h2 (f z)))
          (z ↦ concat X (g (f (bicycle_b B .map z))) (g (bicycle_b B' .map (f z))) (bicycle_b B .map (g (f z)))
            (refl g (bicycle_point_map_commutes_b B B' x y h1 z)) (bicycle_point_map_commutes_b B' B y x h2 (f z)))
          (z ↦ refl (bicycle_a B .map z)) (z ↦ refl (bicycle_b B .map z))
          x (concat X (g (f x)) (g y) x (refl g (bicycle_point_map_point B B' x y h1)) (bicycle_point_map_point B' B y x h2)) in
    let fg : (w : Y) → Id Y (f (g w)) w
      ≔ bicycle_commuting_maps_agree Y Y (bicycle_carrier_set B') (bicycle_a B') (bicycle_b B') (bicycle_a B') (bicycle_b B')
          (bicycle_connectivity B') (w ↦ f (g w)) (w ↦ w)
          (w ↦ concat Y (f (g (bicycle_a B' .map w))) (f (bicycle_a B .map (g w))) (bicycle_a B' .map (f (g w)))
            (refl f (bicycle_point_map_commutes_a B' B y x h2 w)) (bicycle_point_map_commutes_a B B' x y h1 (g w)))
          (w ↦ concat Y (f (g (bicycle_b B' .map w))) (f (bicycle_b B .map (g w))) (bicycle_b B' .map (f (g w)))
            (refl f (bicycle_point_map_commutes_b B' B y x h2 w)) (bicycle_point_map_commutes_b B B' x y h1 (g w)))
          (w ↦ refl (bicycle_a B' .map w)) (w ↦ refl (bicycle_b B' .map w))
          y (concat Y (f (g y)) (f x) y (refl f (bicycle_point_map_point B' B y x h2)) (bicycle_point_map_point B B' x y h1)) in
    ((quasi_inverse_equiv X Y f g gf fg,
      (bicycle_point_map_commutes_a B B' x y h1, bicycle_point_map_commutes_b B B' x y h1)),
     bicycle_point_map_point B B' x y h1)

{` A symmetry (indeed any path of bicycles) commutes with every ⟦ℓ⟧. `}
def bicycle_path_evaluate_meaning (B B' : Bicycles) (p : Id Bicycles B B') (l : List (Sum Int Int))
  (x : bicycle_carrier B)
  : Id (bicycle_carrier B') (bicycle_path_evaluate B B' p (bicycle_word_map B l x))
      (bicycle_word_map B' l (bicycle_path_evaluate B B' p x))
  ≔ let e ≔ bicycle_paths_equiv B B' .map p in
    bicycle_meaning_intertwine (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_b B)
      (bicycle_a B') (bicycle_b B') (e .fst .map) (e .snd .fst) (e .snd .snd) l x

{` Paths of bicycles preserve the stabilizers: H_x ⊆ H'_{p(x)}. `}
def bicycle_path_stabilizer_inclusion (B B' : Bicycles) (p : Id Bicycles B B') (x : bicycle_carrier B)
  : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B' (bicycle_path_evaluate B B' p x))
  ≔ l q ↦ calc
      bicycle_word_map B' l (bicycle_path_evaluate B B' p x)
      = bicycle_path_evaluate B B' p (bicycle_word_map B l x)
        by inverse (bicycle_carrier B') (bicycle_path_evaluate B B' p (bicycle_word_map B l x))
          (bicycle_word_map B' l (bicycle_path_evaluate B B' p x)) (bicycle_path_evaluate_meaning B B' p l x)
      = bicycle_path_evaluate B B' p x by refl (bicycle_path_evaluate B B' p) q ∎

{` Exercise at group.tex 2142: (X,a,b) is normal iff H_x = H_y for all x, y. `}
def normal_bicycle_stabilizers_equal (B : Bicycles) (h : IsNormalBicycle B) (x y : bicycle_carrier B)
  : Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y)
  ≔ let incl : (u v : bicycle_carrier B) → Inclusion (List (Sum Int Int)) (bicycle_stabilizer B u) (bicycle_stabilizer B v)
      ≔ u v l q ↦ transport (bicycle_carrier B) (w ↦ bicycle_stabilizer B w l .fst)
          (bicycle_path_evaluate B B (bicycle_cbid B h u v) u) v
          (inverse (bicycle_carrier B) v (bicycle_path_evaluate B B (bicycle_cbid B h u v) u) (bicycle_cbid_sends B h u v))
          (bicycle_path_stabilizer_inclusion B B (bicycle_cbid B h u v) u l q) in
    inclusion_antisym (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B y) (incl x y) (incl y x)

def bicycle_normal_from_stabilizers (B : Bicycles)
  (h : (x y : bicycle_carrier B) → Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y))
  : IsNormalBicycle B
  ≔ x ↦ embedding_surjection_equiv native_truncation (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x)
      (bicycle_evaluation_injective B B x)
      (z ↦ native_truncation .include (BookFiber (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x) z)
        (let s ≔ bicycle_iso_from_point B B x z
            (subtypes_path_inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B z) (h x z))
            (subtypes_path_inclusion (List (Sum Int Int)) (bicycle_stabilizer B z) (bicycle_stabilizer B x) (h z x)) in
         (bicycle_path_from_iso B B (s .fst),
          inverse (bicycle_carrier B) (s .fst .fst .map x) z (s .snd)))) .equiv

def bicycle_normal_stabilizers_equiv (B : Bicycles)
  : Equiv (IsNormalBicycle B)
      ((x y : bicycle_carrier B) → Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y))
  ≔ iff_equiv (IsNormalBicycle B)
      ((x y : bicycle_carrier B) → Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y))
      (is_normal_bicycle_prop B)
      (pi_prop (bicycle_carrier B)
        (x ↦ (y : bicycle_carrier B) → Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y))
        (x ↦ pi_prop (bicycle_carrier B)
          (y ↦ Id (Subtypes (List (Sum Int Int))) (bicycle_stabilizer B x) (bicycle_stabilizer B y))
          (y ↦ subtypes_set (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B y))))
      (normal_bicycle_stabilizers_equal B) (bicycle_normal_from_stabilizers B)

{` group.tex 2174–2176: for x₀, the map ⟦-⟧(x₀) : (Z ⊔ Z)* → X is surjective. `}
def bicycle_words_at_point_surjective (B : Bicycles) (x0 : bicycle_carrier B)
  : Surjective (List (Sum Int Int)) (bicycle_carrier B) (l ↦ bicycle_word_map B l x0)
  ≔ z ↦ bicycle_connectivity B .snd x0 z

{` The equivalence relation it induces on words. `}
def bicycle_word_relation (B : Bicycles) (x0 : bicycle_carrier B) : EquivalenceRelation (List (Sum Int Int))
  ≔ let X ≔ bicycle_carrier B in
    ((l l' ↦ (Id X (bicycle_word_map B l x0) (bicycle_word_map B l' x0),
        bicycle_carrier_set B (bicycle_word_map B l x0) (bicycle_word_map B l' x0))),
     l ↦ refl (bicycle_word_map B l x0),
     l l' p ↦ inverse X (bicycle_word_map B l x0) (bicycle_word_map B l' x0) p,
     l l' l'' p q ↦ concat X (bicycle_word_map B l x0) (bicycle_word_map B l' x0) (bicycle_word_map B l'' x0) p q)

{` Exercise at group.tex 2178: for a normal bicycle and x₀ : X, two words are
   related (⟦ℓ⟧(x₀) = ⟦ℓ'⟧(x₀)) iff ⟦ℓ⟧ = ⟦ℓ'⟧ as equivalences X ≃ X. `}
def normal_bicycle_words_same_meaning (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int)) (p : Id (bicycle_carrier B) (bicycle_word_map B l x0) (bicycle_word_map B l' x0))
  (z : bicycle_carrier B) : Id (bicycle_carrier B) (bicycle_word_map B l z) (bicycle_word_map B l' z)
  ≔ let X ≔ bicycle_carrier B in
    let s ≔ bicycle_cbid B h x0 z in
    let ev ≔ bicycle_path_evaluate B B s in
    calc
      bicycle_word_map B l z = bicycle_word_map B l (ev x0) by refl (bicycle_word_map B l) (bicycle_cbid_sends B h x0 z)
      = ev (bicycle_word_map B l x0)
        by inverse X (ev (bicycle_word_map B l x0)) (bicycle_word_map B l (ev x0)) (bicycle_path_evaluate_meaning B B s l x0)
      = ev (bicycle_word_map B l' x0) by refl ev p
      = bicycle_word_map B l' (ev x0) by bicycle_path_evaluate_meaning B B s l' x0
      = bicycle_word_map B l' z
        by inverse X (bicycle_word_map B l' z) (bicycle_word_map B l' (ev x0))
          (refl (bicycle_word_map B l') (bicycle_cbid_sends B h x0 z)) ∎

def normal_bicycle_word_relation_meaning (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int))
  : Equiv (Id (bicycle_carrier B) (bicycle_word_map B l x0) (bicycle_word_map B l' x0))
      (Id (Equiv (bicycle_carrier B) (bicycle_carrier B))
        (bicycle_meaning (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l)
        (bicycle_meaning (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l'))
  ≔ let X ≔ bicycle_carrier B in
    let M ≔ (k ↦ bicycle_meaning X (bicycle_a B) (bicycle_b B) k) : List (Sum Int Int) → Equiv X X in
    iff_equiv (Id X (bicycle_word_map B l x0) (bicycle_word_map B l' x0)) (Id (Equiv X X) (M l) (M l'))
      (bicycle_carrier_set B (bicycle_word_map B l x0) (bicycle_word_map B l' x0))
      (equivalences_set X X (bicycle_carrier_set B) (M l) (M l'))
      (p ↦ equiv_homotopy X X (M l) (M l') (normal_bicycle_words_same_meaning B h x0 l l' p))
      (q ↦ refl ((e ↦ e .map x0) : Equiv X X → X) q)

{` rem:bicycle-list-concat. If a symmetry maps x to x', it maps ⟦ℓ⟧x to
   ⟦ℓ⟧x' (bicycle_path_evaluate_meaning); hence cbid x x' = cbid ⟦ℓ⟧x ⟦ℓ⟧x'. `}
def bicycle_cbid_meaning (B : Bicycles) (h : IsNormalBicycle B) (l : List (Sum Int Int)) (x x' : bicycle_carrier B)
  : Id (Id Bicycles B B) (bicycle_cbid B h x x') (bicycle_cbid B h (bicycle_word_map B l x) (bicycle_word_map B l x'))
  ≔ bicycle_cbid_unique B h (bicycle_word_map B l x) (bicycle_word_map B l x') (bicycle_cbid B h x x')
      (concat (bicycle_carrier B)
        (bicycle_path_evaluate B B (bicycle_cbid B h x x') (bicycle_word_map B l x))
        (bicycle_word_map B l (bicycle_path_evaluate B B (bicycle_cbid B h x x') x))
        (bicycle_word_map B l x')
        (bicycle_path_evaluate_meaning B B (bicycle_cbid B h x x') l x)
        (refl (bicycle_word_map B l)
          (inverse (bicycle_carrier B) x' (bicycle_path_evaluate B B (bicycle_cbid B h x x') x) (bicycle_cbid_sends B h x x'))))

def bicycle_cbid_at (B : Bicycles) (h : IsNormalBicycle B) : bicycle_carrier B → bicycle_carrier B → Id Bicycles B B
  ≔ x x' ↦ bicycle_cbid B h x x'

{` First display of rem:bicycle-list-concat (g ∘ f is concat f g):
   cbid_{x₀}^{⟦ℓ⟧x₀} ∘ cbid_{x₀}^{⟦ℓ'⟧x₀}
     = cbid_{⟦ℓ'⟧x₀}^{⟦ℓ'ℓ⟧x₀} ∘ cbid_{x₀}^{⟦ℓ'⟧x₀} = cbid_{x₀}^{⟦ℓ'ℓ⟧x₀}. `}
def bicycle_list_concat_forward_step (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int))
  : Id (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0)) (bicycle_cbid B h x0 (bicycle_word_map B l x0)))
      (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0))
        (bicycle_cbid B h (bicycle_word_map B l' x0) (bicycle_word_map B (append (Sum Int Int) l' l) x0)))
  ≔ refl (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0)))
      (concat (Id Bicycles B B) (bicycle_cbid B h x0 (bicycle_word_map B l x0))
        (bicycle_cbid B h (bicycle_word_map B l' x0) (bicycle_word_map B l' (bicycle_word_map B l x0)))
        (bicycle_cbid B h (bicycle_word_map B l' x0) (bicycle_word_map B (append (Sum Int Int) l' l) x0))
        (bicycle_cbid_meaning B h l' x0 (bicycle_word_map B l x0))
        (refl (bicycle_cbid_at B h (bicycle_word_map B l' x0))
          (inverse (bicycle_carrier B) (bicycle_word_map B (append (Sum Int Int) l' l) x0)
            (bicycle_word_map B l' (bicycle_word_map B l x0))
            (bicycle_meaning_append (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l' l x0))))

def bicycle_list_concat_forward (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int))
  : Id (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0)) (bicycle_cbid B h x0 (bicycle_word_map B l x0)))
      (bicycle_cbid B h x0 (bicycle_word_map B (append (Sum Int Int) l' l) x0))
  ≔ concat (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0)) (bicycle_cbid B h x0 (bicycle_word_map B l x0)))
      (concat Bicycles B B B (bicycle_cbid B h x0 (bicycle_word_map B l' x0))
        (bicycle_cbid B h (bicycle_word_map B l' x0) (bicycle_word_map B (append (Sum Int Int) l' l) x0)))
      (bicycle_cbid B h x0 (bicycle_word_map B (append (Sum Int Int) l' l) x0))
      (bicycle_list_concat_forward_step B h x0 l l')
      (bicycle_cbid_compose B h x0 (bicycle_word_map B l' x0) (bicycle_word_map B (append (Sum Int Int) l' l) x0))

{` Second display: cbid_{⟦ℓ⟧x₀}^{x₀} ∘ cbid_{⟦ℓ'⟧x₀}^{x₀}
     = cbid_{⟦ℓ⟧x₀}^{x₀} ∘ cbid_{⟦ℓℓ'⟧x₀}^{⟦ℓ⟧x₀} = cbid_{⟦ℓℓ'⟧x₀}^{x₀}:
   the map ℓ ↦ cbid_{⟦ℓ⟧x₀}^{x₀} turns concatenation into composition. `}
def bicycle_list_concat_backward_step (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int))
  : Id (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h (bicycle_word_map B l' x0) x0) (bicycle_cbid B h (bicycle_word_map B l x0) x0))
      (concat Bicycles B B B
        (bicycle_cbid B h (bicycle_word_map B (append (Sum Int Int) l l') x0) (bicycle_word_map B l x0))
        (bicycle_cbid B h (bicycle_word_map B l x0) x0))
  ≔ refl ((s ↦ concat Bicycles B B B s (bicycle_cbid B h (bicycle_word_map B l x0) x0)) : Id Bicycles B B → Id Bicycles B B)
      (concat (Id Bicycles B B) (bicycle_cbid B h (bicycle_word_map B l' x0) x0)
        (bicycle_cbid B h (bicycle_word_map B l (bicycle_word_map B l' x0)) (bicycle_word_map B l x0))
        (bicycle_cbid B h (bicycle_word_map B (append (Sum Int Int) l l') x0) (bicycle_word_map B l x0))
        (bicycle_cbid_meaning B h l (bicycle_word_map B l' x0) x0)
        (refl ((w ↦ bicycle_cbid B h w (bicycle_word_map B l x0)) : bicycle_carrier B → Id Bicycles B B)
          (inverse (bicycle_carrier B) (bicycle_word_map B (append (Sum Int Int) l l') x0)
            (bicycle_word_map B l (bicycle_word_map B l' x0))
            (bicycle_meaning_append (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l l' x0))))

def bicycle_list_concat_backward (B : Bicycles) (h : IsNormalBicycle B) (x0 : bicycle_carrier B)
  (l l' : List (Sum Int Int))
  : Id (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h (bicycle_word_map B l' x0) x0) (bicycle_cbid B h (bicycle_word_map B l x0) x0))
      (bicycle_cbid B h (bicycle_word_map B (append (Sum Int Int) l l') x0) x0)
  ≔ concat (Id Bicycles B B)
      (concat Bicycles B B B (bicycle_cbid B h (bicycle_word_map B l' x0) x0) (bicycle_cbid B h (bicycle_word_map B l x0) x0))
      (concat Bicycles B B B
        (bicycle_cbid B h (bicycle_word_map B (append (Sum Int Int) l l') x0) (bicycle_word_map B l x0))
        (bicycle_cbid B h (bicycle_word_map B l x0) x0))
      (bicycle_cbid B h (bicycle_word_map B (append (Sum Int Int) l l') x0) x0)
      (bicycle_list_concat_backward_step B h x0 l l')
      (bicycle_cbid_compose B h (bicycle_word_map B (append (Sum Int Int) l l') x0) (bicycle_word_map B l x0) x0)
