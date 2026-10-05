export "1704-sets-cover"

{` Reduced words for thm:Blass-2 (choicefin.tex:170), without the pushout C.
   Data: a map p : Y → X between sets with decidable equality on Y. The book
   identifies c =_C f(x) with reduced words over Y ⊔ Y; here such words are
   built directly. A letter is a pair (a, b) of distinct elements of one
   fiber, read as k(a)·k(b)⁻¹ (a step from c to f(p a) = f(p b) and back).
   Words are lists with the most recent letter at the head; a word is
   reduced when consecutive letters (a', b') (older) and (a, b) (newer)
   satisfy b' ≠ a. Loops are reduced words; a path to x is a reduced word
   followed by a final k(y) with p(y) = x and y different from the last b. `}
def bword_Setup : Type ≔ sig (
  dom : Type,
  cod : Type,
  dom_set : isSet dom,
  dom_dec : DecidableEquality dom,
  cod_set : isSet cod,
  map : dom → cod)

def bword_PairProp (W : bword_Setup) (w : Product (W .dom) (W .dom)) : Type
  ≔ Product (Id (W .cod) (W .map (w .fst)) (W .map (w .snd))) (Not (Id (W .dom) (w .fst) (w .snd)))

def bword_pair_prop (W : bword_Setup) (w : Product (W .dom) (W .dom)) : isProp (bword_PairProp W w)
  ≔ product_prop (Id (W .cod) (W .map (w .fst)) (W .map (w .snd))) (Not (Id (W .dom) (w .fst) (w .snd)))
      (W .cod_set (W .map (w .fst)) (W .map (w .snd))) (negation_prop (Id (W .dom) (w .fst) (w .snd)))

def bword_Pair (W : bword_Setup) : Type ≔ Σ (Product (W .dom) (W .dom)) (bword_PairProp W)

def bword_pair_set (W : bword_Setup) : isSet (bword_Pair W)
  ≔ sigma_set (Product (W .dom) (W .dom)) (bword_PairProp W)
      (product_set (W .dom) (W .dom) (W .dom_set) (W .dom_set))
      (w ↦ prop_is_set (bword_PairProp W w) (bword_pair_prop W w))

def bword_pair_eq (W : bword_Setup) (d e : bword_Pair W)
  (pa : Id (W .dom) (d .fst .fst) (e .fst .fst)) (pb : Id (W .dom) (d .fst .snd) (e .fst .snd))
  : Id (bword_Pair W) d e
  ≔ subtype_equal (Product (W .dom) (W .dom)) (bword_PairProp W) (bword_pair_prop W) d e (pa, pb)

{` The newest letter (a, b) of a nonempty word does not end with y: b ≠ y. `}
def bword_NotEndsWith (W : bword_Setup) (y : W .dom) (l : List (bword_Pair W)) : Type
  ≔ match l [ nil. ↦ Unit | cons. d _ ↦ Not (Id (W .dom) (d .fst .snd) y) ]

def bword_not_ends_prop (W : bword_Setup) (y : W .dom) (l : List (bword_Pair W))
  : isProp (bword_NotEndsWith W y l)
  ≔ match l [ nil. ↦ unit_prop | cons. d _ ↦ negation_prop (Id (W .dom) (d .fst .snd) y) ]

def bword_Reduced (W : bword_Setup) (l : List (bword_Pair W)) : Type
  ≔ match l [
  | nil. ↦ Unit
  | cons. d l' ↦ Product (bword_NotEndsWith W (d .fst .fst) l') (bword_Reduced W l') ]

def bword_reduced_prop (W : bword_Setup) (l : List (bword_Pair W)) : isProp (bword_Reduced W l)
  ≔ match l [
  | nil. ↦ unit_prop
  | cons. d l' ↦ product_prop (bword_NotEndsWith W (d .fst .fst) l') (bword_Reduced W l')
      (bword_not_ends_prop W (d .fst .fst) l') (bword_reduced_prop W l') ]

{` S: the set of reduced loop words at c. `}
def bword_Loops (W : bword_Setup) : Type ≔ Σ (List (bword_Pair W)) (bword_Reduced W)

def bword_loops_set (W : bword_Setup) : isSet (bword_Loops W)
  ≔ sigma_set (List (bword_Pair W)) (bword_Reduced W) (list_set (bword_Pair W) (bword_pair_set W))
      (l ↦ prop_is_set (bword_Reduced W l) (bword_reduced_prop W l))

def bword_loops_eq (W : bword_Setup) (s t : bword_Loops W) (q : Id (List (bword_Pair W)) (s .fst) (t .fst))
  : Id (bword_Loops W) s t
  ≔ subtype_equal (List (bword_Pair W)) (bword_Reduced W) (bword_reduced_prop W) s t q

def bword_empty_loop (W : bword_Setup) : bword_Loops W ≔ (nil., star.)

{` T_x: the set of reduced paths from c to f(x). `}
def bword_PathProp (W : bword_Setup) (x : W .cod) (w : Product (W .dom) (List (bword_Pair W))) : Type
  ≔ Product (Id (W .cod) (W .map (w .fst)) x)
      (Product (bword_Reduced W (w .snd)) (bword_NotEndsWith W (w .fst) (w .snd)))

def bword_path_prop (W : bword_Setup) (x : W .cod) (w : Product (W .dom) (List (bword_Pair W)))
  : isProp (bword_PathProp W x w)
  ≔ product_prop (Id (W .cod) (W .map (w .fst)) x)
      (Product (bword_Reduced W (w .snd)) (bword_NotEndsWith W (w .fst) (w .snd)))
      (W .cod_set (W .map (w .fst)) x)
      (product_prop (bword_Reduced W (w .snd)) (bword_NotEndsWith W (w .fst) (w .snd))
        (bword_reduced_prop W (w .snd)) (bword_not_ends_prop W (w .fst) (w .snd)))

def bword_Paths (W : bword_Setup) (x : W .cod) : Type
  ≔ Σ (Product (W .dom) (List (bword_Pair W))) (bword_PathProp W x)

def bword_paths_set (W : bword_Setup) (x : W .cod) : isSet (bword_Paths W x)
  ≔ sigma_set (Product (W .dom) (List (bword_Pair W))) (bword_PathProp W x)
      (product_set (W .dom) (List (bword_Pair W)) (W .dom_set) (list_set (bword_Pair W) (bword_pair_set W)))
      (w ↦ prop_is_set (bword_PathProp W x w) (bword_path_prop W x w))

def bword_paths_eq (W : bword_Setup) (x : W .cod) (s t : bword_Paths W x)
  (py : Id (W .dom) (s .fst .fst) (t .fst .fst)) (pl : Id (List (bword_Pair W)) (s .fst .snd) (t .fst .snd))
  : Id (bword_Paths W x) s t
  ≔ subtype_equal (Product (W .dom) (List (bword_Pair W))) (bword_PathProp W x) (bword_path_prop W x) s t (py, pl)

{` The last letter of a path to x is its endpoint y; this is the map
   T_x → p⁻¹(x) used at the end of the book's proof. `}
def bword_endpoint (W : bword_Setup) (x : W .cod) (t : bword_Paths W x) : BookFiber (W .dom) (W .cod) (W .map) x
  ≔ (t .fst .fst, inverse (W .cod) (W .map (t .fst .fst)) x (t .snd .fst))

{` Given y₀ with p(y₀) = x, a bijection T_x ≃ S: a path ending in y ≠ y₀
   becomes the loop with the new letter (y, y₀) appended; a path ending in
   y₀ is the loop itself. The inverse strips a final letter (a, y₀). `}
def bword_new_pair (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (n : Not (Id (W .dom) y y0)) : bword_Pair W
  ≔ ((y, y0), (concat (W .cod) (W .map y) x (W .map y0) e (inverse (W .cod) (W .map y0) x e0), n))

def bword_extend (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (l : List (bword_Pair W)) (g : bword_Reduced W l)
  (ne : bword_NotEndsWith W y l) (dec : Decidable (Id (W .dom) y y0)) : bword_Loops W
  ≔ match dec [
  | inl. _ ↦ (l, g)
  | inr. n ↦ (cons. (bword_new_pair W x y0 e0 y e n) l, (ne, g)) ]

def bword_to_loops (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (t : bword_Paths W x) : bword_Loops W
  ≔ bword_extend W x y0 e0 (t .fst .fst) (t .snd .fst) (t .fst .snd) (t .snd .snd .fst) (t .snd .snd .snd)
      (W .dom_dec (t .fst .fst) y0)

def bword_base_path (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  : bword_Paths W x
  ≔ ((y0, nil.), (e0, (star., star.)))

def bword_strip_pair (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (d : bword_Pair W) (q : Id (W .dom) (d .fst .snd) y0) : Id (W .cod) (W .map (d .fst .fst)) x
  ≔ concat (W .cod) (W .map (d .fst .fst)) (W .map y0) x
      (concat (W .cod) (W .map (d .fst .fst)) (W .map (d .fst .snd)) (W .map y0) (d .snd .fst)
        (map_path (W .dom) (W .cod) (W .map) (d .fst .snd) y0 q)) e0

def bword_strip (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (d : bword_Pair W) (l : List (bword_Pair W)) (ne : bword_NotEndsWith W (d .fst .fst) l)
  (g : bword_Reduced W l) (dec : Decidable (Id (W .dom) (d .fst .snd) y0)) : bword_Paths W x
  ≔ match dec [
  | inl. q ↦ ((d .fst .fst, l), (bword_strip_pair W x y0 e0 d q, (g, ne)))
  | inr. n ↦ ((y0, cons. d l), (e0, ((ne, g), n))) ]

def bword_from_list (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (l : List (bword_Pair W)) (g : bword_Reduced W l) : bword_Paths W x
  ≔ match l [
  | nil. ↦ bword_base_path W x y0 e0
  | cons. d l' ↦ bword_strip W x y0 e0 d l' (g .fst) (g .snd) (W .dom_dec (d .fst .snd) y0) ]

def bword_from_loops (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (s : bword_Loops W) : bword_Paths W x
  ≔ bword_from_list W x y0 e0 (s .fst) (s .snd)

{` First round trip: from_loops (to_loops t) = t. `}
def bword_strip_other (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (q : Id (W .dom) y y0)
  (d : bword_Pair W) (l : List (bword_Pair W)) (g : bword_Reduced W (cons. d l))
  (ne : bword_NotEndsWith W y (cons. d l)) (dec : Decidable (Id (W .dom) (d .fst .snd) y0))
  : Id (bword_Paths W x) (bword_strip W x y0 e0 d l (g .fst) (g .snd) dec) ((y, cons. d l), (e, (g, ne)))
  ≔ match dec [
  | inl. q2 ↦ absurd (Id (bword_Paths W x) (bword_strip W x y0 e0 d l (g .fst) (g .snd) (inl. q2))
        ((y, cons. d l), (e, (g, ne))))
      (ne (concat (W .dom) (d .fst .snd) y0 y q2 (inverse (W .dom) y y0 q)))
  | inr. n2 ↦ bword_paths_eq W x ((y0, cons. d l), (e0, ((g .fst, g .snd), n2))) ((y, cons. d l), (e, (g, ne)))
      (inverse (W .dom) y y0 q) (refl (cons. d l)) ]

def bword_from_kept (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (q : Id (W .dom) y y0)
  (l : List (bword_Pair W)) (g : bword_Reduced W l) (ne : bword_NotEndsWith W y l)
  : Id (bword_Paths W x) (bword_from_list W x y0 e0 l g) ((y, l), (e, (g, ne)))
  ≔ match l [
  | nil. ↦ bword_paths_eq W x (bword_base_path W x y0 e0) ((y, nil.), (e, (g, ne)))
      (inverse (W .dom) y y0 q) (refl (nil. : List (bword_Pair W)))
  | cons. d l' ↦ bword_strip_other W x y0 e0 y e q d l' g ne (W .dom_dec (d .fst .snd) y0) ]

def bword_from_new (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (n : Not (Id (W .dom) y y0))
  (l : List (bword_Pair W)) (g : bword_Reduced W l) (ne : bword_NotEndsWith W y l)
  (dec : Decidable (Id (W .dom) y0 y0))
  : Id (bword_Paths W x) (bword_strip W x y0 e0 (bword_new_pair W x y0 e0 y e n) l ne g dec) ((y, l), (e, (g, ne)))
  ≔ match dec [
  | inl. q2 ↦ bword_paths_eq W x
      ((y, l), (bword_strip_pair W x y0 e0 (bword_new_pair W x y0 e0 y e n) q2, (g, ne))) ((y, l), (e, (g, ne)))
      (refl y) (refl l)
  | inr. n2 ↦ absurd (Id (bword_Paths W x) (bword_strip W x y0 e0 (bword_new_pair W x y0 e0 y e n) l ne g (inr. n2))
        ((y, l), (e, (g, ne)))) (n2 (refl y0)) ]

def bword_from_to_dec (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (y : W .dom) (e : Id (W .cod) (W .map y) x) (l : List (bword_Pair W)) (g : bword_Reduced W l)
  (ne : bword_NotEndsWith W y l) (dec : Decidable (Id (W .dom) y y0))
  : Id (bword_Paths W x) (bword_from_loops W x y0 e0 (bword_extend W x y0 e0 y e l g ne dec)) ((y, l), (e, (g, ne)))
  ≔ match dec [
  | inl. q ↦ bword_from_kept W x y0 e0 y e q l g ne
  | inr. n ↦ bword_from_new W x y0 e0 y e n l g ne (W .dom_dec y0 y0) ]

def bword_from_to (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (t : bword_Paths W x) : Id (bword_Paths W x) (bword_from_loops W x y0 e0 (bword_to_loops W x y0 e0 t)) t
  ≔ bword_from_to_dec W x y0 e0 (t .fst .fst) (t .snd .fst) (t .fst .snd) (t .snd .snd .fst) (t .snd .snd .snd)
      (W .dom_dec (t .fst .fst) y0)

{` Second round trip: to_loops (from_loops s) = s. `}
def bword_to_base (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (g : bword_Reduced W nil.) (dec : Decidable (Id (W .dom) y0 y0))
  : Id (bword_Loops W) (bword_extend W x y0 e0 y0 e0 nil. star. star. dec) (nil., g)
  ≔ match dec [
  | inl. _ ↦ bword_loops_eq W (nil., star.) (nil., g) (refl (nil. : List (bword_Pair W)))
  | inr. n ↦ absurd (Id (bword_Loops W) (bword_extend W x y0 e0 y0 e0 nil. star. star. (inr. n)) (nil., g))
      (n (refl y0)) ]

def bword_to_stripped (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (d : bword_Pair W) (l : List (bword_Pair W)) (g : bword_Reduced W (cons. d l))
  (q : Id (W .dom) (d .fst .snd) y0) (dec : Decidable (Id (W .dom) (d .fst .fst) y0))
  : Id (bword_Loops W)
      (bword_extend W x y0 e0 (d .fst .fst) (bword_strip_pair W x y0 e0 d q) l (g .snd) (g .fst) dec)
      (cons. d l, g)
  ≔ match dec [
  | inl. q2 ↦ absurd (Id (bword_Loops W)
        (bword_extend W x y0 e0 (d .fst .fst) (bword_strip_pair W x y0 e0 d q) l (g .snd) (g .fst) (inl. q2))
        (cons. d l, g))
      (d .snd .snd (concat (W .dom) (d .fst .fst) y0 (d .fst .snd) q2 (inverse (W .dom) (d .fst .snd) y0 q)))
  | inr. n2 ↦ bword_loops_eq W
      (cons. (bword_new_pair W x y0 e0 (d .fst .fst) (bword_strip_pair W x y0 e0 d q) n2) l, (g .fst, g .snd))
      (cons. d l, g)
      (cons. (bword_pair_eq W (bword_new_pair W x y0 e0 (d .fst .fst) (bword_strip_pair W x y0 e0 d q) n2) d
          (refl (d .fst .fst)) (inverse (W .dom) (d .fst .snd) y0 q))
        (refl l)) ]

def bword_to_unstripped (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (d : bword_Pair W) (l : List (bword_Pair W)) (g : bword_Reduced W (cons. d l))
  (n : Not (Id (W .dom) (d .fst .snd) y0)) (dec : Decidable (Id (W .dom) y0 y0))
  : Id (bword_Loops W) (bword_extend W x y0 e0 y0 e0 (cons. d l) (g .fst, g .snd) n dec) (cons. d l, g)
  ≔ match dec [
  | inl. _ ↦ bword_loops_eq W (cons. d l, (g .fst, g .snd)) (cons. d l, g) (refl (cons. d l))
  | inr. n2 ↦ absurd (Id (bword_Loops W) (bword_extend W x y0 e0 y0 e0 (cons. d l) (g .fst, g .snd) n (inr. n2))
        (cons. d l, g)) (n2 (refl y0)) ]

def bword_to_strip_dec (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (d : bword_Pair W) (l : List (bword_Pair W)) (g : bword_Reduced W (cons. d l))
  (dec : Decidable (Id (W .dom) (d .fst .snd) y0))
  : Id (bword_Loops W) (bword_to_loops W x y0 e0 (bword_strip W x y0 e0 d l (g .fst) (g .snd) dec)) (cons. d l, g)
  ≔ match dec [
  | inl. q ↦ bword_to_stripped W x y0 e0 d l g q (W .dom_dec (d .fst .fst) y0)
  | inr. n ↦ bword_to_unstripped W x y0 e0 d l g n (W .dom_dec y0 y0) ]

def bword_to_from_list (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  (l : List (bword_Pair W)) (g : bword_Reduced W l)
  : Id (bword_Loops W) (bword_to_loops W x y0 e0 (bword_from_list W x y0 e0 l g)) (l, g)
  ≔ match l [
  | nil. ↦ bword_to_base W x y0 e0 g (W .dom_dec y0 y0)
  | cons. d l' ↦ bword_to_strip_dec W x y0 e0 d l' g (W .dom_dec (d .fst .snd) y0) ]

{` T_x ≃ S, given any y₀ in the fiber over x. `}
def bword_paths_loops_equiv (W : bword_Setup) (x : W .cod) (y0 : W .dom) (e0 : Id (W .cod) (W .map y0) x)
  : Equiv (bword_Paths W x) (bword_Loops W)
  ≔ quasi_inverse_equiv (bword_Paths W x) (bword_Loops W)
      (bword_to_loops W x y0 e0) (bword_from_loops W x y0 e0)
      (bword_from_to W x y0 e0) (s ↦ bword_to_from_list W x y0 e0 (s .fst) (s .snd))
