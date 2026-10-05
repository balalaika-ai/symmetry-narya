export "404-group-examples"

{` Chapter 4, section "Bicycles" (group.tex 1785–2340): lists of letters in
   Z ⊔ Z, their meaning ⟦ℓ⟧ : X ≃ X for two self-equivalences a, b of a type
   X (group.tex 1867–1877), and the type of bicycles (def:bicycle).
   A letter inl n stands for aⁿ and inr n for bⁿ; powers are the integer
   powers permutation_power of module 57 (int_iterate of e and its inverse).
   Integers are Int of module 03: pos. n = n and neg. n = −(n+1). `}

def BicycleWord : Type ≔ List (Sum Int Int)

{` The meaning ⟦ℓ⟧, defined by list induction exactly as printed:
   ⟦ε⟧ = id, ⟦inl n ℓ⟧ = aⁿ ∘ ⟦ℓ⟧, ⟦inr n ℓ⟧ = bⁿ ∘ ⟦ℓ⟧ (underlying map). `}
def bicycle_meaning_map (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X) : X
  ≔ match l [
  | nil. ↦ x
  | cons. (inl. n) k ↦ permutation_power X a n (bicycle_meaning_map X a b k x)
  | cons. (inr. n) k ↦ permutation_power X b n (bicycle_meaning_map X a b k x) ]

{` The inverse of ⟦ℓ⟧: ⟦ℓ⟧⁻¹ ∘ a⁻ⁿ, etc. `}
def bicycle_meaning_inverse_map (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X) : X
  ≔ match l [
  | nil. ↦ x
  | cons. (inl. n) k ↦ bicycle_meaning_inverse_map X a b k (permutation_power X a (int_neg n) x)
  | cons. (inr. n) k ↦ bicycle_meaning_inverse_map X a b k (permutation_power X b (int_neg n) x) ]

def bicycle_meaning_retraction (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_inverse_map X a b l (bicycle_meaning_map X a b l x)) x
  ≔ match l [
  | nil. ↦ refl x
  | cons. (inl. n) k ↦ concat X
      (bicycle_meaning_inverse_map X a b k
        (permutation_power X a (int_neg n) (permutation_power X a n (bicycle_meaning_map X a b k x))))
      (bicycle_meaning_inverse_map X a b k (bicycle_meaning_map X a b k x)) x
      (refl (bicycle_meaning_inverse_map X a b k)
        (permutation_power_inverse X a n (bicycle_meaning_map X a b k x)))
      (bicycle_meaning_retraction X a b k x)
  | cons. (inr. n) k ↦ concat X
      (bicycle_meaning_inverse_map X a b k
        (permutation_power X b (int_neg n) (permutation_power X b n (bicycle_meaning_map X a b k x))))
      (bicycle_meaning_inverse_map X a b k (bicycle_meaning_map X a b k x)) x
      (refl (bicycle_meaning_inverse_map X a b k)
        (permutation_power_inverse X b n (bicycle_meaning_map X a b k x)))
      (bicycle_meaning_retraction X a b k x) ]

def bicycle_meaning_section (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b l (bicycle_meaning_inverse_map X a b l x)) x
  ≔ match l [
  | nil. ↦ refl x
  | cons. (inl. n) k ↦ concat X
      (permutation_power X a n
        (bicycle_meaning_map X a b k (bicycle_meaning_inverse_map X a b k (permutation_power X a (int_neg n) x))))
      (permutation_power X a n (permutation_power X a (int_neg n) x)) x
      (refl (permutation_power X a n) (bicycle_meaning_section X a b k (permutation_power X a (int_neg n) x)))
      (permutation_power_inverse_other X a n x)
  | cons. (inr. n) k ↦ concat X
      (permutation_power X b n
        (bicycle_meaning_map X a b k (bicycle_meaning_inverse_map X a b k (permutation_power X b (int_neg n) x))))
      (permutation_power X b n (permutation_power X b (int_neg n) x)) x
      (refl (permutation_power X b n) (bicycle_meaning_section X a b k (permutation_power X b (int_neg n) x)))
      (permutation_power_inverse_other X b n x) ]

{` ⟦ℓ⟧ : X ≃ X as an equivalence; its underlying map is bicycle_meaning_map
   by definition. `}
def bicycle_meaning (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) : Equiv X X
  ≔ quasi_inverse_equiv X X (bicycle_meaning_map X a b l) (bicycle_meaning_inverse_map X a b l)
      (bicycle_meaning_retraction X a b l) (bicycle_meaning_section X a b l)

{` The three defining clauses as identifications of equivalences (the
   underlying maps agree by definition). `}
def bicycle_meaning_nil (X : Type) (a b : Equiv X X)
  : Id (Equiv X X) (bicycle_meaning X a b nil.) (identity_equiv X)
  ≔ equiv_path X X (bicycle_meaning X a b nil.) (identity_equiv X) (refl (identity X))

def bicycle_meaning_cons_left (X : Type) (a b : Equiv X X) (n : Int) (l : List (Sum Int Int))
  : Id (Equiv X X) (bicycle_meaning X a b (cons. (inl. n) l))
      (compose_equiv X X X (bicycle_meaning X a b l) (permutation_power_equiv X a n))
  ≔ equiv_path X X (bicycle_meaning X a b (cons. (inl. n) l))
      (compose_equiv X X X (bicycle_meaning X a b l) (permutation_power_equiv X a n))
      (refl (bicycle_meaning_map X a b (cons. (inl. n) l)))

def bicycle_meaning_cons_right (X : Type) (a b : Equiv X X) (n : Int) (l : List (Sum Int Int))
  : Id (Equiv X X) (bicycle_meaning X a b (cons. (inr. n) l))
      (compose_equiv X X X (bicycle_meaning X a b l) (permutation_power_equiv X b n))
  ≔ equiv_path X X (bicycle_meaning X a b (cons. (inr. n) l))
      (compose_equiv X X X (bicycle_meaning X a b l) (permutation_power_equiv X b n))
      (refl (bicycle_meaning_map X a b (cons. (inr. n) l)))

{` The example of group.tex 1876: ⟦inl 3 inr −2 inl −1 inr 1⟧ = a³b⁻²a⁻¹b.
   Here −2 = neg. 1 and −1 = neg. 0. The right-hand side is written out with
   a, b and their inverses, so the identification is a litmus check of the
   order of composition and of the integer powers (it holds by refl). `}
def bicycle_example_word : List (Sum Int Int)
  ≔ cons. (inl. (pos. (suc. (suc. (suc. zero.)))))
      (cons. (inr. (neg. (suc. zero.)))
        (cons. (inl. (neg. zero.))
          (cons. (inr. (pos. (suc. zero.))) nil.)))

def bicycle_example_meaning (X : Type) (a b : Equiv X X)
  : Id (X → X) (bicycle_meaning X a b bicycle_example_word .map)
      (x ↦ a .map (a .map (a .map
        (equiv_inverse_map X X b (equiv_inverse_map X X b
          (equiv_inverse_map X X a (b .map x)))))))
  ≔ refl (bicycle_meaning X a b bicycle_example_word .map)

{` The same example as composite of the integer powers a³, b⁻², a⁻¹, b¹. `}
def bicycle_example_meaning_powers (X : Type) (a b : Equiv X X)
  : Id (Equiv X X) (bicycle_meaning X a b bicycle_example_word)
      (compose_equiv X X X
        (compose_equiv X X X
          (compose_equiv X X X (permutation_power_equiv X b (pos. (suc. zero.)))
            (permutation_power_equiv X a (neg. zero.)))
          (permutation_power_equiv X b (neg. (suc. zero.))))
        (permutation_power_equiv X a (pos. (suc. (suc. (suc. zero.))))))
  ≔ equiv_path X X (bicycle_meaning X a b bicycle_example_word)
      (compose_equiv X X X
        (compose_equiv X X X
          (compose_equiv X X X (permutation_power_equiv X b (pos. (suc. zero.)))
            (permutation_power_equiv X a (neg. zero.)))
          (permutation_power_equiv X b (neg. (suc. zero.))))
        (permutation_power_equiv X a (pos. (suc. (suc. (suc. zero.))))))
      (refl (bicycle_meaning X a b bicycle_example_word .map))

{` ⟦ℓ'⟧ ∘ ⟦ℓ⟧ = ⟦ℓ'ℓ⟧ (used in rem:bicycle-list-concat), with ℓ'ℓ = append ℓ' ℓ. `}
def bicycle_meaning_append (X : Type) (a b : Equiv X X) (l' l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b (append (Sum Int Int) l' l) x)
      (bicycle_meaning_map X a b l' (bicycle_meaning_map X a b l x))
  ≔ match l' [
  | nil. ↦ refl (bicycle_meaning_map X a b l x)
  | cons. (inl. n) k ↦ refl (permutation_power X a n) (bicycle_meaning_append X a b k l x)
  | cons. (inr. n) k ↦ refl (permutation_power X b n) (bicycle_meaning_append X a b k l x) ]

{` The inverse word: reverse the list and negate every exponent;
   ⟦ℓ⁻¹⟧ = ⟦ℓ⟧⁻¹. `}
def bicycle_letter_inverse : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inl. (int_neg n) | inr. n ↦ inr. (int_neg n) ]

def bicycle_word_inverse (l : List (Sum Int Int)) : List (Sum Int Int)
  ≔ match l [
  | nil. ↦ nil.
  | cons. s k ↦ append (Sum Int Int) (bicycle_word_inverse k) (cons. (bicycle_letter_inverse s) nil.) ]

def bicycle_meaning_word_inverse (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b (bicycle_word_inverse l) x) (bicycle_meaning_inverse_map X a b l x)
  ≔ match l [
  | nil. ↦ refl x
  | cons. (inl. n) k ↦ concat X
      (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse k) (cons. (inl. (int_neg n)) nil.)) x)
      (bicycle_meaning_map X a b (bicycle_word_inverse k) (permutation_power X a (int_neg n) x))
      (bicycle_meaning_inverse_map X a b k (permutation_power X a (int_neg n) x))
      (bicycle_meaning_append X a b (bicycle_word_inverse k) (cons. (inl. (int_neg n)) nil.) x)
      (bicycle_meaning_word_inverse X a b k (permutation_power X a (int_neg n) x))
  | cons. (inr. n) k ↦ concat X
      (bicycle_meaning_map X a b (append (Sum Int Int) (bicycle_word_inverse k) (cons. (inr. (int_neg n)) nil.)) x)
      (bicycle_meaning_map X a b (bicycle_word_inverse k) (permutation_power X b (int_neg n) x))
      (bicycle_meaning_inverse_map X a b k (permutation_power X b (int_neg n) x))
      (bicycle_meaning_append X a b (bicycle_word_inverse k) (cons. (inr. (int_neg n)) nil.) x)
      (bicycle_meaning_word_inverse X a b k (permutation_power X b (int_neg n) x)) ]

{` If h intertwines a with a' and b with b' (ha = a'h, hb = b'h pointwise),
   then h⟦ℓ⟧ = ⟦ℓ⟧'h (the list induction in the proof of lem:evisinj-bicycle). `}
def bicycle_meaning_intertwine (X Y : Type) (a b : Equiv X X) (a' b' : Equiv Y Y) (h : X → Y)
  (ha : Commutes X Y a a' h) (hb : Commutes X Y b b' h) (l : List (Sum Int Int)) (x : X)
  : Id Y (h (bicycle_meaning_map X a b l x)) (bicycle_meaning_map Y a' b' l (h x))
  ≔ match l [
  | nil. ↦ refl (h x)
  | cons. (inl. n) k ↦ concat Y
      (h (permutation_power X a n (bicycle_meaning_map X a b k x)))
      (permutation_power Y a' n (h (bicycle_meaning_map X a b k x)))
      (permutation_power Y a' n (bicycle_meaning_map Y a' b' k (h x)))
      (permutation_power_intertwine X Y a a' h ha n (bicycle_meaning_map X a b k x))
      (refl (permutation_power Y a' n) (bicycle_meaning_intertwine X Y a b a' b' h ha hb k x))
  | cons. (inr. n) k ↦ concat Y
      (h (permutation_power X b n (bicycle_meaning_map X a b k x)))
      (permutation_power Y b' n (h (bicycle_meaning_map X a b k x)))
      (permutation_power Y b' n (bicycle_meaning_map Y a' b' k (h x)))
      (permutation_power_intertwine X Y b b' h hb n (bicycle_meaning_map X a b k x))
      (refl (permutation_power Y b' n) (bicycle_meaning_intertwine X Y a b a' b' h ha hb k x)) ]

{` "x and x' are connected by a and b": ∃ ℓ, x' = ⟦ℓ⟧(x), and the full
   condition ‖X‖ × Π_{x,x'} ∃_ℓ (x' = ⟦ℓ⟧(x)) of def:bicycle. `}
def BicycleWordFrom (X : Type) (a b : Equiv X X) (x x' : X) : Type
  ≔ Σ (List (Sum Int Int)) (l ↦ Id X x' (bicycle_meaning X a b l .map x))

def BicycleConnected (X : Type) (a b : Equiv X X) : Type
  ≔ Product (Mere X) ((x x' : X) → Mere (Σ (List (Sum Int Int)) (l ↦ Id X x' (bicycle_meaning X a b l .map x))))

def bicycle_connected_prop (X : Type) (a b : Equiv X X) : isProp (BicycleConnected X a b)
  ≔ product_prop (Mere X) ((x x' : X) → Mere (BicycleWordFrom X a b x x')) (mere_isprop X)
      (pi_prop X (x ↦ (x' : X) → Mere (BicycleWordFrom X a b x x'))
        (x ↦ pi_prop X (x' ↦ Mere (BicycleWordFrom X a b x x')) (x' ↦ mere_isprop (BicycleWordFrom X a b x x'))))

{` def:bicycle, the displayed formula with the printed nesting:
   Bicyc ≔ Σ_{X:Set} Σ_{a:X≃X} Σ_{b:X≃X} (‖X‖ × Π_{x,x'} ∃_ℓ (x' = ⟦ℓ⟧(x))). `}
def Bicycles : Type
  ≔ Σ SetTypes (X ↦ Σ (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦
      BicycleConnected (X .fst) a b)))

def mkbicycle (X : SetTypes) (a b : Equiv (X .fst) (X .fst)) (h : BicycleConnected (X .fst) a b) : Bicycles
  ≔ (X, (a, (b, h)))

def bicycle_set (B : Bicycles) : SetTypes ≔ B .fst
def bicycle_carrier (B : Bicycles) : Type ≔ B .fst .fst
def bicycle_carrier_set (B : Bicycles) : isSet (bicycle_carrier B) ≔ B .fst .snd
def bicycle_a (B : Bicycles) : Equiv (bicycle_carrier B) (bicycle_carrier B) ≔ B .snd .fst
def bicycle_b (B : Bicycles) : Equiv (bicycle_carrier B) (bicycle_carrier B) ≔ B .snd .snd .fst
def bicycle_connectivity (B : Bicycles) : BicycleConnected (bicycle_carrier B) (bicycle_a B) (bicycle_b B)
  ≔ B .snd .snd .snd

{` ⟦ℓ⟧ for a bicycle. `}
def bicycle_word_map (B : Bicycles) (l : List (Sum Int Int)) (x : bicycle_carrier B) : bicycle_carrier B
  ≔ bicycle_meaning_map (bicycle_carrier B) (bicycle_a B) (bicycle_b B) l x

{` Connectivity from a single point: if every y is (merely) ⟦ℓ⟧(x₀) for some
   ℓ, then any x, x' are connected (via the inverse word). `}
def bicycle_word_compose_back (X : Type) (a b : Equiv X X) (x0 x x' : X)
  (w : BicycleWordFrom X a b x0 x) (w' : BicycleWordFrom X a b x0 x') : BicycleWordFrom X a b x x'
  ≔ (append (Sum Int Int) (w' .fst) (bicycle_word_inverse (w .fst)), calc
      x' = bicycle_meaning_map X a b (w' .fst) x0 by w' .snd
      = bicycle_meaning_map X a b (w' .fst)
          (bicycle_meaning_inverse_map X a b (w .fst) (bicycle_meaning_map X a b (w .fst) x0))
        by refl (bicycle_meaning_map X a b (w' .fst))
          (inverse X (bicycle_meaning_inverse_map X a b (w .fst) (bicycle_meaning_map X a b (w .fst) x0)) x0
            (bicycle_meaning_retraction X a b (w .fst) x0))
      = bicycle_meaning_map X a b (w' .fst) (bicycle_meaning_inverse_map X a b (w .fst) x)
        by refl ((y ↦ bicycle_meaning_map X a b (w' .fst) (bicycle_meaning_inverse_map X a b (w .fst) y)) : X → X)
          (inverse X x (bicycle_meaning_map X a b (w .fst) x0) (w .snd))
      = bicycle_meaning_map X a b (w' .fst) (bicycle_meaning_map X a b (bicycle_word_inverse (w .fst)) x)
        by refl (bicycle_meaning_map X a b (w' .fst))
          (inverse X (bicycle_meaning_map X a b (bicycle_word_inverse (w .fst)) x)
            (bicycle_meaning_inverse_map X a b (w .fst) x) (bicycle_meaning_word_inverse X a b (w .fst) x))
      = bicycle_meaning_map X a b (append (Sum Int Int) (w' .fst) (bicycle_word_inverse (w .fst))) x
        by inverse X (bicycle_meaning_map X a b (append (Sum Int Int) (w' .fst) (bicycle_word_inverse (w .fst))) x)
          (bicycle_meaning_map X a b (w' .fst) (bicycle_meaning_map X a b (bicycle_word_inverse (w .fst)) x))
          (bicycle_meaning_append X a b (w' .fst) (bicycle_word_inverse (w .fst)) x) ∎)

def bicycle_connected_from_point (X : Type) (a b : Equiv X X) (x0 : X)
  (h : (y : X) → Mere (BicycleWordFrom X a b x0 y)) : BicycleConnected X a b
  ≔ (mere X x0, x x' ↦
      mere_rec (BicycleWordFrom X a b x0 x) (Mere (BicycleWordFrom X a b x x')) (mere_isprop (BicycleWordFrom X a b x x'))
        (w ↦ mere_rec (BicycleWordFrom X a b x0 x') (Mere (BicycleWordFrom X a b x x'))
          (mere_isprop (BicycleWordFrom X a b x x'))
          (w' ↦ mere (BicycleWordFrom X a b x x') (bicycle_word_compose_back X a b x0 x x' w w')) (h x')) (h x))

{` The connectivity of a bicycle transported along an equivalence that
   intertwines the structure maps. `}
def bicycle_connected_transfer (X Y : Type) (a b : Equiv X X) (a' b' : Equiv Y Y) (e : Equiv X Y)
  (ha : Commutes X Y a a' (e .map)) (hb : Commutes X Y b b' (e .map)) (c : BicycleConnected X a b)
  : BicycleConnected Y a' b'
  ≔ (mere_rec X (Mere Y) (mere_isprop Y) (x ↦ mere Y (e .map x)) (c .fst),
      y y' ↦ mere_rec (BicycleWordFrom X a b (equiv_inverse_map X Y e y) (equiv_inverse_map X Y e y'))
        (Mere (BicycleWordFrom Y a' b' y y')) (mere_isprop (BicycleWordFrom Y a' b' y y'))
        (w ↦ mere (BicycleWordFrom Y a' b' y y') (w .fst, calc
          y' = e .map (equiv_inverse_map X Y e y') by inverse Y (e .map (equiv_inverse_map X Y e y')) y' (equiv_counit X Y e y')
          = e .map (bicycle_meaning_map X a b (w .fst) (equiv_inverse_map X Y e y)) by refl (e .map) (w .snd)
          = bicycle_meaning_map Y a' b' (w .fst) (e .map (equiv_inverse_map X Y e y))
            by bicycle_meaning_intertwine X Y a b a' b' (e .map) ha hb (w .fst) (equiv_inverse_map X Y e y)
          = bicycle_meaning_map Y a' b' (w .fst) y
            by refl (bicycle_meaning_map Y a' b' (w .fst)) (equiv_counit X Y e y) ∎))
        (c .snd (equiv_inverse_map X Y e y) (equiv_inverse_map X Y e y')))
