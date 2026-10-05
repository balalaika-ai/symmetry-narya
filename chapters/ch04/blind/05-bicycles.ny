export "04-sign"

{` Blind statements, chapter 4, section "Bicycles". Lists of Z ⊔ Z are
   List (Sum Int Int); their meaning [l] is defined on underlying maps:
   [ε] = id, [inl n :: l] = a^n ∘ [l], [inr n :: l] = b^n ∘ [l]. `}
def BlindZZList : Type ≔ List (Sum Int Int)

def blind_sem (X : Type) (a b : Equiv X X) (l : BlindZZList) : X → X
  ≔ match l [
  | nil. ↦ identity X
  | cons. h t ↦ match h [
    | inl. n ↦ x ↦ permutation_power X a n (blind_sem X a b t x)
    | inr. n ↦ x ↦ permutation_power X b n (blind_sem X a b t x) ] ]

{` def:bicycle. `}
def BlindBicycleStr (X : SetTypes) (a b : Equiv (X .fst) (X .fst)) : Type
  ≔ Product (Mere (X .fst)) ((x x' : X .fst) → Mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))

def BlindBicycles : Type
  ≔ Σ SetTypes (X ↦ Σ (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦ BlindBicycleStr X a b)))

def blind_bicycle_str_prop (X : SetTypes) (a b : Equiv (X .fst) (X .fst)) : isProp (BlindBicycleStr X a b)
  ≔ product_prop (Mere (X .fst)) ((x x' : X .fst) → Mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))
      (mere_isprop (X .fst))
      (pi_prop (X .fst) (x ↦ (x' : X .fst) → Mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))
        (x ↦ pi_prop (X .fst) (x' ↦ Mere (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))
          (x' ↦ mere_isprop (Σ BlindZZList (l ↦ Id (X .fst) x' (blind_sem (X .fst) a b l x))))))

def blind_bicycles_groupoid : isGroupoid BlindBicycles
  ≔ blind_groupoid_sigma SetTypes
      (X ↦ Σ (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦ BlindBicycleStr X a b)))
      sets_groupoid
      (X ↦ blind_set_groupoid (Σ (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦ BlindBicycleStr X a b)))
        (sigma_set (Equiv (X .fst) (X .fst)) (a ↦ Σ (Equiv (X .fst) (X .fst)) (b ↦ BlindBicycleStr X a b))
          (equivalences_set (X .fst) (X .fst) (X .snd))
          (a ↦ sigma_set (Equiv (X .fst) (X .fst)) (b ↦ BlindBicycleStr X a b)
            (equivalences_set (X .fst) (X .fst) (X .snd))
            (b ↦ prop_is_set (BlindBicycleStr X a b) (blind_bicycle_str_prop X a b)))))

{` Raw data (X, a, b) with the bicycle property (equivalences plus
   connectedness) as a separate witness type. `}
def BlindBicycleOn (X : SetTypes) (a b : X .fst → X .fst) : Type
  ≔ Σ (isEquiv (X .fst) (X .fst) a) (ha ↦ Σ (isEquiv (X .fst) (X .fst) b) (hb ↦ BlindBicycleStr X (a, ha) (b, hb)))

def blind_bicycle_of (X : SetTypes) (a b : X .fst → X .fst) (w : BlindBicycleOn X a b) : BlindBicycles
  ≔ (X, ((a, w .fst), ((b, w .snd .fst), w .snd .snd)))

def blind_bicycle_aut (B : BlindBicycles) : BlindGroup ≔ blind_Aut BlindBicycles blind_bicycles_groupoid B

{` def:Dinfty-Q. The bicycle property of the two standard bicycles is
   the claim implicit in the definition; the groups are parametrized by it. `}
def blind_zz_set : SetTypes ≔ (Sum Int Int, sum_set Int Int int_set int_set)
def blind_dihedral_a : Sum Int Int → Sum Int Int ≔ [ inl. n ↦ inl. (int_succ n) | inr. n ↦ inr. (int_pred n) ]
def blind_dihedral_b : Sum Int Int → Sum Int Int ≔ [ inl. n ↦ inr. n | inr. n ↦ inl. n ]

def blind_dihedral_is_bicycle : Type ≔ BlindBicycleOn blind_zz_set blind_dihedral_a blind_dihedral_b
def blind_dihedral_bicycle (w : blind_dihedral_is_bicycle) : BlindBicycles
  ≔ blind_bicycle_of blind_zz_set blind_dihedral_a blind_dihedral_b w
def blind_Dinfty (w : blind_dihedral_is_bicycle) : BlindGroup ≔ blind_bicycle_aut (blind_dihedral_bicycle w)

{` Elements of Fin (k+1) by value: zero, successor modulo k+1, and the
   residue of a natural number (consistent with blind_fin_val). `}
def blind_fin_zero (k : Nat) : Fin (suc. k) ≔ match k [ zero. ↦ inr. star. | suc. j ↦ inl. (blind_fin_zero j) ]
def blind_fin_next (k : Nat) (y : Fin k) : Fin (suc. k)
  ≔ match k [
  | zero. ↦ match y [ ]
  | suc. j ↦ match y [ inl. z ↦ inl. (blind_fin_next j z) | inr. _ ↦ inr. star. ] ]
def blind_fin_succ_mod (k : Nat) (x : Fin (suc. k)) : Fin (suc. k)
  ≔ match x [ inl. y ↦ blind_fin_next k y | inr. _ ↦ blind_fin_zero k ]
def blind_fin_of_nat (k n : Nat) : Fin (suc. k)
  ≔ match n [ zero. ↦ blind_fin_zero k | suc. m ↦ blind_fin_succ_mod k (blind_fin_of_nat k m) ]

def blind_bool_if (A : Type) (c : Bool) (t f : A) : A ≔ match c [ true. ↦ t | false. ↦ f ]

def blind_seven : Nat ≔ suc. (suc. (suc. blind_four))
def blind_five : Nat ≔ suc. blind_four
def blind_eight : Nat ≔ suc. blind_seven
def blind_six : Nat ≔ suc. blind_five

{` Quaternion bicycle on bn 8: a(k) = k+1 (k even), k+3 (k odd);
   b(k) = k-1 (k even), k-3 (k odd), modulo 8. `}
def blind_quaternion_a (x : Fin blind_eight) : Fin blind_eight
  ≔ let v ≔ blind_fin_val blind_eight x in
    blind_fin_of_nat blind_seven (add v (blind_bool_if Nat (blind_nat_even v) (suc. zero.) blind_three))
def blind_quaternion_b (x : Fin blind_eight) : Fin blind_eight
  ≔ let v ≔ blind_fin_val blind_eight x in
    blind_fin_of_nat blind_seven (add v (blind_bool_if Nat (blind_nat_even v) blind_seven blind_five))

def blind_quaternion_is_bicycle : Type ≔ BlindBicycleOn (blind_bn_set blind_eight) blind_quaternion_a blind_quaternion_b
def blind_quaternion_bicycle (w : blind_quaternion_is_bicycle) : BlindBicycles
  ≔ blind_bicycle_of (blind_bn_set blind_eight) blind_quaternion_a blind_quaternion_b w
def blind_Q8 (w : blind_quaternion_is_bicycle) : BlindGroup ≔ blind_bicycle_aut (blind_quaternion_bicycle w)

{` Litmus: a(0) = 1, a(1) = 4, b(0) = 7, b(1) = 6. `}
def blind_quaternion_check
  : Product (Id Nat (blind_fin_val blind_eight (blind_quaternion_a (blind_fin_of_nat blind_seven zero.))) (suc. zero.))
      (Product (Id Nat (blind_fin_val blind_eight (blind_quaternion_a (blind_fin_of_nat blind_seven (suc. zero.)))) blind_four)
        (Product (Id Nat (blind_fin_val blind_eight (blind_quaternion_b (blind_fin_of_nat blind_seven zero.))) blind_seven)
          (Id Nat (blind_fin_val blind_eight (blind_quaternion_b (blind_fin_of_nat blind_seven (suc. zero.)))) blind_six)))
  ≔ (refl (suc. zero.), (refl blind_four, (refl blind_seven, refl blind_six)))

{` lem:evisinj-bicycle. A path of bicycles acts on underlying elements
   by transport along its underlying path of types. `}
def blind_bicycle_ev (B B' : BlindBicycles) (x0 : B .fst .fst) (e : Id BlindBicycles B B') : B' .fst .fst
  ≔ transport Type (identity Type) (B .fst .fst) (B' .fst .fst)
      (map_path BlindBicycles Type (u ↦ u .fst .fst) B B' e) x0

def blind_lem_evisinj_bicycle : Type
  ≔ (B B' : BlindBicycles) (x0 : B .fst .fst) (e e' : Id BlindBicycles B B') →
    Id (B' .fst .fst) (blind_bicycle_ev B B' x0 e) (blind_bicycle_ev B B' x0 e') → Id (Id BlindBicycles B B') e e'

{` def:normal-bicycle. `}
def BlindNormalBicycle (B : BlindBicycles) : Type
  ≔ (x : B .fst .fst) → BookIsEquiv (Id BlindBicycles B B) (B .fst .fst) (blind_bicycle_ev B B x)

{` xca:normal-bicycle-equiv. `}
def blind_xca_normal_bicycle_equiv : Type
  ≔ (B : BlindBicycles) (x : B .fst .fst) →
    BookIsEquiv (Id BlindBicycles B B) (B .fst .fst) (blind_bicycle_ev B B x) → BlindNormalBicycle B

{` def:cbid-bicycle: the symmetry sending x to x'. `}
def blind_cbid (B : BlindBicycles) (hn : BlindNormalBicycle B) (x x' : B .fst .fst) : Id BlindBicycles B B
  ≔ hn x x' .center .fst

def blind_bsem (B : BlindBicycles) (l : BlindZZList) : B .fst .fst → B .fst .fst
  ≔ blind_sem (B .fst .fst) (B .snd .fst) (B .snd .snd .fst) l

{` xca (line 2142): normal iff H_x = H_y for all x, y. `}
def blind_bicycle_H (B : BlindBicycles) (x : B .fst .fst) : Subtypes BlindZZList
  ≔ l ↦ (Id (B .fst .fst) (blind_bsem B l x) x, B .fst .snd (blind_bsem B l x) x)
def blind_xca_normal_iff_H : Type
  ≔ (B : BlindBicycles) →
    BlindIff (BlindNormalBicycle B) ((x y : B .fst .fst) → Id (Subtypes BlindZZList) (blind_bicycle_H B x) (blind_bicycle_H B y))

{` xca (line 2146). `}
def BlindCommutingBicycle (B : BlindBicycles) : Type
  ≔ Id (B .fst .fst → B .fst .fst) (x ↦ B .snd .fst .map (B .snd .snd .fst .map x)) (x ↦ B .snd .snd .fst .map (B .snd .fst .map x))
def BlindCommutingBicycles : Type ≔ Σ BlindBicycles BlindCommutingBicycle

def blind_xca_commuting_normal : Type ≔ (B : BlindBicycles) → BlindCommutingBicycle B → BlindNormalBicycle B

def blind_xca_cycles_commuting_bicycles : Type
  ≔ Σ (Product Cycles Cycles → BlindCommutingBicycles) (F ↦
      Product
        ((c d : Cycles) →
          let X ≔ c .fst .fst .fst in
          let Y ≔ d .fst .fst .fst in
          let S : SetTypes ≔ (Product X Y, product_set X Y (c .fst .fst .snd) (d .fst .fst .snd)) in
          let a ≔ product_equiv X Y X Y (c .fst .snd) (identity_equiv Y) in
          let b ≔ product_equiv X Y X Y (identity_equiv X) (d .fst .snd) in
          Σ (BlindBicycleStr S a b) (h ↦ Id BlindBicycles (F (c, d) .fst) (S, (a, (b, h)))))
        (BookIsEquiv (Product Cycles Cycles) BlindCommutingBicycles F))

{` xca (line 2178): for a normal bicycle and x0, l ~ l' (i.e. [l](x0) =
   [l'](x0)) iff [l] = [l']. `}
def blind_xca_list_equivalence : Type
  ≔ (B : BlindBicycles) (hn : BlindNormalBicycle B) (x0 : B .fst .fst) (l l' : BlindZZList) →
    BlindIff (Id (B .fst .fst) (blind_bsem B l x0) (blind_bsem B l' x0))
      (Id (B .fst .fst → B .fst .fst) (blind_bsem B l) (blind_bsem B l'))

{` rem:bicycle-list-concat. Composition g ∘ f of symmetries is concat f g. `}
def blind_rem_sem_append : Type
  ≔ (X : Type) (a b : Equiv X X) (l l' : BlindZZList) →
    Id (X → X) (x ↦ blind_sem X a b l' (blind_sem X a b l x)) (blind_sem X a b (append (Sum Int Int) l' l))

def blind_rem_cbid_shift : Type
  ≔ (B : BlindBicycles) (hn : BlindNormalBicycle B) (x x' : B .fst .fst) (l : BlindZZList) →
    Id (Id BlindBicycles B B) (blind_cbid B hn x x') (blind_cbid B hn (blind_bsem B l x) (blind_bsem B l x'))

def blind_rem_cbid_concat : Type
  ≔ (B : BlindBicycles) (hn : BlindNormalBicycle B) (x0 : B .fst .fst) (l l' : BlindZZList) →
    let c ≔ blind_cbid B hn in
    let s ≔ blind_bsem B in
    Product
      (Id (Id BlindBicycles B B) (concat BlindBicycles B B B (c x0 (s l' x0)) (c x0 (s l x0)))
        (c x0 (s (append (Sum Int Int) l' l) x0)))
      (Id (Id BlindBicycles B B) (concat BlindBicycles B B B (c (s l' x0) x0) (c (s l x0) x0))
        (c (s (append (Sum Int Int) l l') x0) x0))

{` rem:inf-dihedral-frieze, with x0 = inl 0, T = (a x0 ↦ x0), R = (b x0 ↦ x0). `}
def blind_int_minus_one : Int ≔ neg. zero.
def blind_rem_dihedral_frieze : Type
  ≔ (w : blind_dihedral_is_bicycle) (hn : BlindNormalBicycle (blind_dihedral_bicycle w)) →
    let B ≔ blind_dihedral_bicycle w in
    let x0 : Sum Int Int ≔ inl. (pos. zero.) in
    let c ≔ blind_cbid B hn in
    let ainv ≔ equiv_inverse_map (Sum Int Int) (Sum Int Int) (B .snd .fst) in
    let binv ≔ equiv_inverse_map (Sum Int Int) (Sum Int Int) (B .snd .snd .fst) in
    let T ≔ c (blind_dihedral_a x0) x0 in
    let R ≔ c (blind_dihedral_b x0) x0 in
    let ev ≔ blind_bicycle_ev B B in
    Product (Id (Id BlindBicycles B B) T (c x0 (ainv x0)))
      (Product (Id (Id BlindBicycles B B) R (c x0 (binv x0)))
        (Product ((l : BlindZZList) → Id (Sum Int Int) (ev (blind_bsem B l x0) T)
            (blind_bsem B (append (Sum Int Int) l (cons. (inl. blind_int_minus_one) nil.)) x0))
          (Product ((l : BlindZZList) → Id (Sum Int Int) (ev (blind_bsem B l x0) R)
              (blind_bsem B (append (Sum Int Int) l (cons. (inr. blind_int_minus_one) nil.)) x0))
            ((n : Int) → Id (Sum Int Int) (ev (permutation_power (Sum Int Int) (B .snd .fst) n x0) R)
              (permutation_power (Sum Int Int) (B .snd .fst) n (blind_dihedral_b x0))))))

{` xca (line 2298): (X, a, b) is identified with (X, T, R). `}
def blind_xca_dihedral_geometric : Type
  ≔ (w : blind_dihedral_is_bicycle) (hn : BlindNormalBicycle (blind_dihedral_bicycle w)) →
    let B ≔ blind_dihedral_bicycle w in
    let x0 : Sum Int Int ≔ inl. (pos. zero.) in
    let tr : Id BlindBicycles B B → Equiv (Sum Int Int) (Sum Int Int) ≔ S ↦
      transport_equiv (Sum Int Int) (Sum Int Int) (map_path BlindBicycles Type (u ↦ u .fst .fst) B B S) in
    let T ≔ tr (blind_cbid B hn (blind_dihedral_a x0) x0) in
    let R ≔ tr (blind_cbid B hn (blind_dihedral_b x0) x0) in
    Σ (BlindBicycleStr blind_zz_set T R) (h ↦ Id BlindBicycles B (blind_zz_set, (T, (R, h))))

{` xca (line 2303): the hexagon bicycle (a = (0 1)(2 3)(4 5),
   b = (1 2)(3 4)(5 0)) and the prism bicycle on x_i = i, y_i = 3+i
   (a(x_i) = x_{i-1}, a(y_i) = y_{i+1}, b swaps x_i and y_i) have
   isomorphic automorphism groups, isomorphic to S_3. `}
def blind_hexagon_a (x : Fin blind_six) : Fin blind_six
  ≔ let v ≔ blind_fin_val blind_six x in
    blind_fin_of_nat blind_five (add v (blind_bool_if Nat (blind_nat_even v) (suc. zero.) blind_five))
def blind_hexagon_b (x : Fin blind_six) : Fin blind_six
  ≔ let v ≔ blind_fin_val blind_six x in
    blind_fin_of_nat blind_five (add v (blind_bool_if Nat (blind_nat_even v) blind_five (suc. zero.)))

def blind_prism_a_table (v : Nat) : Nat
  ≔ match v [
  | zero. ↦ two
  | suc. v1 ↦ match v1 [
    | zero. ↦ zero.
    | suc. v2 ↦ match v2 [
      | zero. ↦ suc. zero.
      | suc. v3 ↦ match v3 [
        | zero. ↦ blind_four
        | suc. v4 ↦ match v4 [ zero. ↦ blind_five | suc. _ ↦ blind_three ] ] ] ] ]
def blind_prism_a (x : Fin blind_six) : Fin blind_six
  ≔ blind_fin_of_nat blind_five (blind_prism_a_table (blind_fin_val blind_six x))
def blind_prism_b (x : Fin blind_six) : Fin blind_six
  ≔ blind_fin_of_nat blind_five (add (blind_fin_val blind_six x) blind_three)

def blind_xca_hexagon_prism : Type
  ≔ (w1 : BlindBicycleOn (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b)
    (w2 : BlindBicycleOn (blind_bn_set blind_six) blind_prism_a blind_prism_b) →
    let G1 ≔ blind_bicycle_aut (blind_bicycle_of (blind_bn_set blind_six) blind_hexagon_a blind_hexagon_b w1) in
    let G2 ≔ blind_bicycle_aut (blind_bicycle_of (blind_bn_set blind_six) blind_prism_a blind_prism_b w2) in
    Product (BlindIso G1 G2) (BlindIso G1 (blind_SG blind_three))
