export "477-abnormal-bicycles"

{` Exercise at group.tex 2146, first part, and the map Cyc × Cyc → Bicyc.
   A bicycle is commuting if ab = ba (stated pointwise, a(b x) = b(a x),
   which for a set is equivalent to the equality of the maps). Commuting
   bicycles are normal. The map ((X,t),(Y,u)) ↦ (X × Y, t × id, id × u)
   lands in the commuting bicycles, but it is NOT onto them: the commuting
   bicycle (Bool, not, not) is not in its image (refutation of the printed
   claim; the corrected statement, an equivalence onto the "split"
   commuting bicycles, is in module 479). `}

def IsCommutingBicycle (B : Bicycles) : Type
  ≔ (x : bicycle_carrier B) → Id (bicycle_carrier B) (bicycle_a B .map (bicycle_b B .map x)) (bicycle_b B .map (bicycle_a B .map x))

def is_commuting_bicycle_prop (B : Bicycles) : isProp (IsCommutingBicycle B)
  ≔ pi_prop (bicycle_carrier B)
      (x ↦ Id (bicycle_carrier B) (bicycle_a B .map (bicycle_b B .map x)) (bicycle_b B .map (bicycle_a B .map x)))
      (x ↦ bicycle_carrier_set B (bicycle_a B .map (bicycle_b B .map x)) (bicycle_b B .map (bicycle_a B .map x)))

def CommutingBicycles : Type ≔ Σ Bicycles IsCommutingBicycle

{` Powers of a self-equivalence commute with every map commuting with it. `}
def bicycle_power_commutes (X : Type) (e : Equiv X X) (f : X → X)
  (h : (x : X) → Id X (f (e .map x)) (e .map (f x))) (n : Int) (x : X)
  : Id X (permutation_power X e n (f x)) (f (permutation_power X e n x))
  ≔ inverse X (f (permutation_power X e n x)) (permutation_power X e n (f x))
      (permutation_power_intertwine X X e e f h n x)

{` If ab = ba, every ⟦ℓ⟧ commutes with a and b, hence any two meanings commute. `}
def commuting_meaning_commutes_a (X : Type) (a b : Equiv X X)
  (hab : (x : X) → Id X (a .map (b .map x)) (b .map (a .map x))) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b l (a .map x)) (a .map (bicycle_meaning_map X a b l x))
  ≔ match l [
  | nil. ↦ refl (a .map x)
  | cons. (inl. n) k ↦ concat X
      (permutation_power X a n (bicycle_meaning_map X a b k (a .map x)))
      (permutation_power X a n (a .map (bicycle_meaning_map X a b k x)))
      (a .map (permutation_power X a n (bicycle_meaning_map X a b k x)))
      (refl (permutation_power X a n) (commuting_meaning_commutes_a X a b hab k x))
      (bicycle_power_commutes X a (a .map) (w ↦ refl (a .map (a .map w))) n (bicycle_meaning_map X a b k x))
  | cons. (inr. n) k ↦ concat X
      (permutation_power X b n (bicycle_meaning_map X a b k (a .map x)))
      (permutation_power X b n (a .map (bicycle_meaning_map X a b k x)))
      (a .map (permutation_power X b n (bicycle_meaning_map X a b k x)))
      (refl (permutation_power X b n) (commuting_meaning_commutes_a X a b hab k x))
      (bicycle_power_commutes X b (a .map) hab n (bicycle_meaning_map X a b k x)) ]

def commuting_meaning_commutes_b (X : Type) (a b : Equiv X X)
  (hab : (x : X) → Id X (a .map (b .map x)) (b .map (a .map x))) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b l (b .map x)) (b .map (bicycle_meaning_map X a b l x))
  ≔ match l [
  | nil. ↦ refl (b .map x)
  | cons. (inl. n) k ↦ concat X
      (permutation_power X a n (bicycle_meaning_map X a b k (b .map x)))
      (permutation_power X a n (b .map (bicycle_meaning_map X a b k x)))
      (b .map (permutation_power X a n (bicycle_meaning_map X a b k x)))
      (refl (permutation_power X a n) (commuting_meaning_commutes_b X a b hab k x))
      (bicycle_power_commutes X a (b .map) (w ↦ inverse X (a .map (b .map w)) (b .map (a .map w)) (hab w)) n
        (bicycle_meaning_map X a b k x))
  | cons. (inr. n) k ↦ concat X
      (permutation_power X b n (bicycle_meaning_map X a b k (b .map x)))
      (permutation_power X b n (b .map (bicycle_meaning_map X a b k x)))
      (b .map (permutation_power X b n (bicycle_meaning_map X a b k x)))
      (refl (permutation_power X b n) (commuting_meaning_commutes_b X a b hab k x))
      (bicycle_power_commutes X b (b .map) (w ↦ refl (b .map (b .map w))) n (bicycle_meaning_map X a b k x)) ]

def commuting_meanings_commute (X : Type) (a b : Equiv X X)
  (hab : (x : X) → Id X (a .map (b .map x)) (b .map (a .map x))) (l m : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X a b l (bicycle_meaning_map X a b m x)) (bicycle_meaning_map X a b m (bicycle_meaning_map X a b l x))
  ≔ bicycle_meaning_intertwine X X a b a b (bicycle_meaning_map X a b l)
      (commuting_meaning_commutes_a X a b hab l) (commuting_meaning_commutes_b X a b hab l) m x

{` Exercise at group.tex 2146: every commuting bicycle is normal (all H_x agree). `}
def commuting_bicycle_stabilizer_inclusion (B : Bicycles) (hc : IsCommutingBicycle B) (x y : bicycle_carrier B)
  : Inclusion (List (Sum Int Int)) (bicycle_stabilizer B x) (bicycle_stabilizer B y)
  ≔ l q ↦ let X ≔ bicycle_carrier B in
      mere_rec (BicycleWordFrom X (bicycle_a B) (bicycle_b B) x y) (Id X (bicycle_word_map B l y) y)
        (bicycle_carrier_set B (bicycle_word_map B l y) y)
        (w ↦ calc
          bicycle_word_map B l y = bicycle_word_map B l (bicycle_word_map B (w .fst) x) by refl (bicycle_word_map B l) (w .snd)
          = bicycle_word_map B (w .fst) (bicycle_word_map B l x)
            by commuting_meanings_commute X (bicycle_a B) (bicycle_b B) hc l (w .fst) x
          = bicycle_word_map B (w .fst) x by refl (bicycle_word_map B (w .fst)) q
          = y by inverse X y (bicycle_word_map B (w .fst) x) (w .snd) ∎)
        (bicycle_connectivity B .snd x y)

def commuting_bicycle_normal (B : Bicycles) (hc : IsCommutingBicycle B) : IsNormalBicycle B
  ≔ bicycle_normal_from_stabilizers B (x y ↦ inclusion_antisym (List (Sum Int Int))
      (bicycle_stabilizer B x) (bicycle_stabilizer B y)
      (commuting_bicycle_stabilizer_inclusion B hc x y) (commuting_bicycle_stabilizer_inclusion B hc y x))

{` Cycles (def:Cyc, module 58): carrier, set, permutation, cyclicity. `}
def cycle_carrier_type (c : Cycles) : Type ≔ c .fst .fst .fst
def cycle_carrier_is_set (c : Cycles) : isSet (cycle_carrier_type c) ≔ c .fst .fst .snd
def cycle_generator (c : Cycles) : Equiv (cycle_carrier_type c) (cycle_carrier_type c) ≔ c .fst .snd

{` Powers of t × id and id × u. `}
def product_left_power (X Y : Type) (t : Equiv X X) (n : Int) (x : X) (y : Y)
  : Id (Product X Y) (permutation_power (Product X Y) (product_equiv X Y X Y t (identity_equiv Y)) n (x, y))
      (permutation_power X t n x, y)
  ≔ inverse (Product X Y) (permutation_power X t n x, y)
      (permutation_power (Product X Y) (product_equiv X Y X Y t (identity_equiv Y)) n (x, y))
      (permutation_power_intertwine X (Product X Y) t (product_equiv X Y X Y t (identity_equiv Y)) (w ↦ (w, y))
        (w ↦ refl ((t .map w, y) : Product X Y)) n x)

def product_right_power (X Y : Type) (u : Equiv Y Y) (n : Int) (x : X) (y : Y)
  : Id (Product X Y) (permutation_power (Product X Y) (product_equiv X Y X Y (identity_equiv X) u) n (x, y))
      (x, permutation_power Y u n y)
  ≔ inverse (Product X Y) (x, permutation_power Y u n y)
      (permutation_power (Product X Y) (product_equiv X Y X Y (identity_equiv X) u) n (x, y))
      (permutation_power_intertwine Y (Product X Y) u (product_equiv X Y X Y (identity_equiv X) u) (w ↦ (x, w))
        (w ↦ refl ((x, u .map w) : Product X Y)) n y)

def product_bicycle_set (c d : Cycles) : SetTypes
  ≔ (Product (cycle_carrier_type c) (cycle_carrier_type d),
      sigma_set (cycle_carrier_type c) (_ ↦ cycle_carrier_type d) (cycle_carrier_is_set c) (_ ↦ cycle_carrier_is_set d))

def product_bicycle_a (c d : Cycles)
  : Equiv (Product (cycle_carrier_type c) (cycle_carrier_type d)) (Product (cycle_carrier_type c) (cycle_carrier_type d))
  ≔ product_equiv (cycle_carrier_type c) (cycle_carrier_type d) (cycle_carrier_type c) (cycle_carrier_type d)
      (cycle_generator c) (identity_equiv (cycle_carrier_type d))

def product_bicycle_b (c d : Cycles)
  : Equiv (Product (cycle_carrier_type c) (cycle_carrier_type d)) (Product (cycle_carrier_type c) (cycle_carrier_type d))
  ≔ product_equiv (cycle_carrier_type c) (cycle_carrier_type d) (cycle_carrier_type c) (cycle_carrier_type d)
      (identity_equiv (cycle_carrier_type c)) (cycle_generator d)

{` (x', y') = (t×id)ⁿ (id×u)ᵐ (x, y) when x' = tⁿ x and y' = uᵐ y. `}
def product_bicycle_connected (c d : Cycles)
  : BicycleConnected (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_a c d) (product_bicycle_b c d)
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in
    let t ≔ cycle_generator c in let u ≔ cycle_generator d in
    let P ≔ Product X Y in
    let W : P → P → Type ≔ p q ↦ BicycleWordFrom P (product_bicycle_a c d) (product_bicycle_b c d) p q in
    (mere_rec X (Mere P) (mere_isprop P)
       (x ↦ mere_rec Y (Mere P) (mere_isprop P) (y ↦ mere P (x, y)) (d .snd .fst)) (c .snd .fst),
     p q ↦ mere_rec (OrbitWitness X t (p .fst) (q .fst)) (Mere (W p q)) (mere_isprop (W p q))
       (v ↦ mere_rec (OrbitWitness Y u (p .snd) (q .snd)) (Mere (W p q)) (mere_isprop (W p q))
         (w ↦ mere (W p q) (cons. (inl. (v .fst)) (cons. (inr. (w .fst)) nil.), calc
           q = (permutation_power X t (v .fst) (p .fst), permutation_power Y u (w .fst) (p .snd))
             by (v .snd, w .snd)
           = permutation_power P (product_bicycle_a c d) (v .fst) (p .fst, permutation_power Y u (w .fst) (p .snd))
             by inverse P (permutation_power P (product_bicycle_a c d) (v .fst) (p .fst, permutation_power Y u (w .fst) (p .snd)))
               (permutation_power X t (v .fst) (p .fst), permutation_power Y u (w .fst) (p .snd))
               (product_left_power X Y t (v .fst) (p .fst) (permutation_power Y u (w .fst) (p .snd)))
           = permutation_power P (product_bicycle_a c d) (v .fst)
               (permutation_power P (product_bicycle_b c d) (w .fst) (p .fst, p .snd))
             by refl (permutation_power P (product_bicycle_a c d) (v .fst))
               (inverse P (permutation_power P (product_bicycle_b c d) (w .fst) (p .fst, p .snd))
                 (p .fst, permutation_power Y u (w .fst) (p .snd))
                 (product_right_power X Y u (w .fst) (p .fst) (p .snd))) ∎))
         (d .snd .snd (p .snd) (q .snd)))
       (c .snd .snd (p .fst) (q .fst)))

{` The map Cyc × Cyc → Bicyc of the exercise. `}
def cycle_product_bicycle (c d : Cycles) : Bicycles
  ≔ mkbicycle (product_bicycle_set c d) (product_bicycle_a c d) (product_bicycle_b c d) (product_bicycle_connected c d)

def cycle_product_bicycle_commuting (c d : Cycles) : IsCommutingBicycle (cycle_product_bicycle c d)
  ≔ p ↦ refl ((cycle_generator c .map (p .fst), cycle_generator d .map (p .snd))
      : Product (cycle_carrier_type c) (cycle_carrier_type d))

{` Counterexample: (Bool, not, not) is a commuting bicycle. `}
def bool_double_bicycle : Bicycles
  ≔ mkbicycle (Bool, bool_set) bool_not_equiv bool_not_equiv
      (bicycle_connected_from_point Bool bool_not_equiv bool_not_equiv false.
        (y ↦ mere (BicycleWordFrom Bool bool_not_equiv bool_not_equiv false. y)
          (match y [
           | false. ↦ (nil., refl (false. : Bool))
           | true. ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (true. : Bool)) ])))

def bool_double_bicycle_commuting : IsCommutingBicycle bool_double_bicycle
  ≔ x ↦ refl (bool_not (bool_not x))

{` No identification (X × Y, t × id, id × u) = (Bool, not, not): with
   p = e⁻¹(false), e((t×id)p) = not(e p) = e((id×u)p), so t(p₁) = p₁, hence
   (t×id)p = p and e p = not(e p), impossible. `}
def bool_double_not_cycle_product (c d : Cycles) (e : BicycleIsomorphisms (cycle_product_bicycle c d) bool_double_bicycle)
  : Empty
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in
    let P ≔ Product X Y in
    let t ≔ cycle_generator c in let u ≔ cycle_generator d in
    let f ≔ e .fst .map in
    let p ≔ equiv_inverse_map P Bool (e .fst) false. in
    let same : Id P (t .map (p .fst), p .snd) (p .fst, u .map (p .snd))
      ≔ equiv_inverse_map (Id P (t .map (p .fst), p .snd) (p .fst, u .map (p .snd)))
          (Id Bool (f (t .map (p .fst), p .snd)) (f (p .fst, u .map (p .snd))))
          (equivalence_on_paths P Bool (e .fst) (t .map (p .fst), p .snd) (p .fst, u .map (p .snd)))
          (concat Bool (f (t .map (p .fst), p .snd)) (bool_not (f p)) (f (p .fst, u .map (p .snd)))
            (e .snd .fst p) (inverse Bool (f (p .fst, u .map (p .snd))) (bool_not (f p)) (e .snd .snd p))) in
    let fixed : Id P (t .map (p .fst), p .snd) p
      ≔ (same .fst, refl (p .snd)) in
    bool_not_no_fixed_point (f p)
      (calc bool_not (f p) = f (t .map (p .fst), p .snd)
          by inverse Bool (f (t .map (p .fst), p .snd)) (bool_not (f p)) (e .snd .fst p)
        = f p by refl f fixed ∎)

def bool_double_not_in_image (c d : Cycles) (q : Id Bicycles (cycle_product_bicycle c d) bool_double_bicycle) : Empty
  ≔ bool_double_not_cycle_product c d (bicycle_paths_equiv (cycle_product_bicycle c d) bool_double_bicycle .map q)

{` Refutation of the printed claim: the map is not onto the commuting bicycles. `}
def cycle_product_not_onto_commuting
  (h : (B : CommutingBicycles) → Mere (Σ Cycles (c ↦ Σ Cycles (d ↦ Id Bicycles (cycle_product_bicycle c d) (B .fst)))))
  : Empty
  ≔ mere_rec (Σ Cycles (c ↦ Σ Cycles (d ↦ Id Bicycles (cycle_product_bicycle c d) bool_double_bicycle))) Empty empty_prop
      (w ↦ bool_double_not_in_image (w .fst) (w .snd .fst) (w .snd .snd))
      (h (bool_double_bicycle, bool_double_bicycle_commuting))
