{` Blind statements for chapter 8 (congp.tex), section "Semidirect products":
   the action of Σ_2 on C_n, dihedral groups, dihedral bicycles. `}
export "01-semidirect"
export "../../../src/568-s2-acts-on-c3"
export "../../../src/474-standard-bicycles"

{` The standard n-cycle (Z/~_n, s) of def:standard-cycle, for an order n : Order:
   the quotient of Z by the periods of n (module 69 standard_cycle n). `}
def BlindZn (n : Order) : Type ≔ SubgroupQuotient (order_periods n) (order_subgroup_laws n)
def blind_zn_class (n : Order) : Int → BlindZn n ≔ subgroup_class (order_periods n) (order_subgroup_laws n)
def blind_zn_set (n : Order) : isSet (BlindZn n) ≔ subgroup_quotient_set (order_periods n) (order_subgroup_laws n)

{` The relation on S × Z: (s,z) ~ (s,z') if z ~_n z', and (s,z) ~ (s',z') if s ≠ s' and z ~_n −z'.
   z ~_n z' is read as [z] = [z'] in Z/~_n. `}
def BlindDihRel (n : Order) (S : TwoElementSets) (u v : Product (two_set_carrier S) Int) : Type
  ≔ Sum (Product (Id (two_set_carrier S) (u .fst) (v .fst))
               (Id (BlindZn n) (blind_zn_class n (u .snd)) (blind_zn_class n (v .snd))))
        (Product (Not (Id (two_set_carrier S) (u .fst) (v .fst)))
               (Id (BlindZn n) (blind_zn_class n (u .snd)) (blind_zn_class n (int_neg (v .snd)))))

{` Footnote "Check that ~ defines an equivalence relation". `}
def blind_dihedral_relation_equivalence : Type
  ≔ (n : Order) (S : TwoElementSets)
    → Product ((u : Product (two_set_carrier S) Int) → BlindDihRel n S u u)
        (Product ((u v : Product (two_set_carrier S) Int) → BlindDihRel n S u v → BlindDihRel n S v u)
          ((u v w : Product (two_set_carrier S) Int) → BlindDihRel n S u v → BlindDihRel n S v w → BlindDihRel n S u w))

{` X ≔ (S × Z)/~, the set quotient realised as the image of u ↦ [u] (the repository's
   Quotient construction, here for the propositional truncation of ~). `}
def blind_dih_pred (n : Order) (S : TwoElementSets)
  : Product (two_set_carrier S) Int → Product (two_set_carrier S) Int → PropTypes
  ≔ u v ↦ (Mere (BlindDihRel n S u v), mere_isprop (BlindDihRel n S u v))

def BlindDihX (n : Order) (S : TwoElementSets) : Type
  ≔ Image (Product (two_set_carrier S) Int) (Product (two_set_carrier S) Int → PropTypes) (blind_dih_pred n S)

def blind_dih_class (n : Order) (S : TwoElementSets) (u : Product (two_set_carrier S) Int) : BlindDihX n S
  ≔ image_factor (Product (two_set_carrier S) Int) (Product (two_set_carrier S) Int → PropTypes) (blind_dih_pred n S) u

def blind_dih_set (n : Order) (S : TwoElementSets) : isSet (BlindDihX n S)
  ≔ image_set (Product (two_set_carrier S) Int) (Product (two_set_carrier S) Int → PropTypes) (blind_dih_pred n S)
      (subtypes_set (Product (two_set_carrier S) Int))

{` A function f : S → X → X with f_s[(s,z)] = [(s,z+1)] and f_s[(s',z)] = [(s',z−1)] for s' ≠ s. `}
def BlindDihedralF (n : Order) (S : TwoElementSets) : Type
  ≔ Σ (two_set_carrier S → BlindDihX n S → BlindDihX n S) (f ↦
      Product ((s : two_set_carrier S) (z : Int)
                → Id (BlindDihX n S) (f s (blind_dih_class n S (s, z))) (blind_dih_class n S (s, int_succ z)))
              ((s s' : two_set_carrier S) (z : Int) → Not (Id (two_set_carrier S) s' s)
                → Id (BlindDihX n S) (f s (blind_dih_class n S (s', z))) (blind_dih_class n S (s', int_pred z))))

{` congp.tex:79, first part: f is well defined. `}
def blind_xca_dihedral_well_defined : Type ≔ (n : Order) (S : TwoElementSets) → BlindDihedralF n S

{` congp.tex:79, second part: for n = 3, (X, f) = (1 ⊔ S, f) of ex:S2-acts-on-C3 in Σ_{X:Set}(S → X → X)
   (for every 2-element set S and any f as above; f is unique since the classes cover X). `}
def blind_xca_dihedral_three : Type
  ≔ (S : TwoElementSets) (w : BlindDihedralF (principal_order three) S)
    → Id (S2C3Type S) ((BlindDihX (principal_order three) S, blind_dih_set (principal_order three) S), w .fst)
         (s2c3_point S)

{` def:gen-dihedral. C̃_n(S) ≔ Aut_{Σ_{X:Set}(S→X→X)}(X, f) and D_n ≔ Σ_2 ⋉ C̃_n.
   f is a parameter (any choice satisfying the defining equations; it is unique). `}
def BlindDihedralData (n : Order) : Type ≔ (S : TwoElementSets) → BlindDihedralF n S

def blind_dihedral_shape (n : Order) (w : BlindDihedralData n) (S : TwoElementSets) : S2C3Type S
  ≔ ((BlindDihX n S, blind_dih_set n S), w S .fst)

def blind_cyclic_action (n : Order) (w : BlindDihedralData n) : TwoElementSets → Group
  ≔ S ↦ automorphism_group (S2C3Type S) (s2c3_type_groupoid S) (blind_dihedral_shape n w S)

def blind_dihedral (n : Order) (w : BlindDihedralData n) : Group
  ≔ blind_semidirect (symmetric_group two) (blind_cyclic_action n w)

{` The standard dihedral bicycle of degree n: (Z/~_n ⊔ Z/~_n, a, b) with
   a(inl[z]) = inl[z+1], a(inr[z]) = inr[z−1], b swaps the summands. `}
def blind_std_dih_a (n : Order) : Equiv (Sum (BlindZn n) (BlindZn n)) (Sum (BlindZn n) (BlindZn n))
  ≔ sum_equiv (BlindZn n) (BlindZn n) (BlindZn n) (BlindZn n)
      (subgroup_translation_equiv (order_periods n) (order_subgroup_laws n) (pos. (suc. zero.)))
      (subgroup_translation_equiv (order_periods n) (order_subgroup_laws n) (neg. zero.))

def blind_std_dih_b (n : Order) : Equiv (Sum (BlindZn n) (BlindZn n)) (Sum (BlindZn n) (BlindZn n))
  ≔ quasi_inverse_equiv (Sum (BlindZn n) (BlindZn n)) (Sum (BlindZn n) (BlindZn n))
      (sum_swap (BlindZn n) (BlindZn n)) (sum_swap (BlindZn n) (BlindZn n))
      (sum_swap_involutive (BlindZn n) (BlindZn n)) (sum_swap_involutive (BlindZn n) (BlindZn n))

{` Connectedness of the standard dihedral bicycle: every point is reached from inl[0]. `}
def blind_std_dih_reach_left (n : Order) (k : Int)
  : Id (Sum (BlindZn n) (BlindZn n)) (inl. (blind_zn_class n k))
      (permutation_power (Sum (BlindZn n) (BlindZn n)) (blind_std_dih_a n) k (inl. (blind_zn_class n int_zero)))
  ≔ concat (Sum (BlindZn n) (BlindZn n)) (inl. (blind_zn_class n k))
      (inl. (permutation_power (BlindZn n) (subgroup_successor (order_periods n) (order_subgroup_laws n)) k
               (blind_zn_class n int_zero)))
      (permutation_power (Sum (BlindZn n) (BlindZn n)) (blind_std_dih_a n) k (inl. (blind_zn_class n int_zero)))
      (refl ((q ↦ inl. q) : BlindZn n → Sum (BlindZn n) (BlindZn n))
        (subgroup_power_zero (order_periods n) (order_subgroup_laws n) k))
      (permutation_power_intertwine (BlindZn n) (Sum (BlindZn n) (BlindZn n))
        (subgroup_successor (order_periods n) (order_subgroup_laws n)) (blind_std_dih_a n) (q ↦ inl. q)
        (q ↦ refl (inl. (subgroup_successor (order_periods n) (order_subgroup_laws n) .map q) : Sum (BlindZn n) (BlindZn n)))
        k (blind_zn_class n int_zero))

def blind_std_dih_reach (n : Order) (y : Sum (BlindZn n) (BlindZn n))
  : Mere (BicycleWordFrom (Sum (BlindZn n) (BlindZn n)) (blind_std_dih_a n) (blind_std_dih_b n)
            (inl. (blind_zn_class n int_zero)) y)
  ≔ let X ≔ Sum (BlindZn n) (BlindZn n) in
    let a ≔ blind_std_dih_a n in let b ≔ blind_std_dih_b n in
    let x0 : X ≔ inl. (blind_zn_class n int_zero) in
    let R ≔ subgroup_relation (order_periods n) (order_subgroup_laws n) in
    match y [
    | inl. q ↦ mere_rec (BookFiber Int (BlindZn n) (blind_zn_class n) q) (Mere (BicycleWordFrom X a b x0 (inl. q)))
        (mere_isprop (BicycleWordFrom X a b x0 (inl. q)))
        (w ↦ mere (BicycleWordFrom X a b x0 (inl. q))
          (cons. (inl. (w .fst)) nil.,
           concat X (inl. q) (inl. (blind_zn_class n (w .fst)))
             (permutation_power X a (w .fst) x0)
             (refl ((r ↦ inl. r) : BlindZn n → X) (w .snd))
             (blind_std_dih_reach_left n (w .fst))))
        (quotient_surjective Int R q)
    | inr. q ↦ mere_rec (BookFiber Int (BlindZn n) (blind_zn_class n) q) (Mere (BicycleWordFrom X a b x0 (inr. q)))
        (mere_isprop (BicycleWordFrom X a b x0 (inr. q)))
        (w ↦ mere (BicycleWordFrom X a b x0 (inr. q))
          (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (w .fst)) nil.),
           concat X (inr. q) (inr. (blind_zn_class n (w .fst)))
             (b .map (permutation_power X a (w .fst) x0))
             (refl ((r ↦ inr. r) : BlindZn n → X) (w .snd))
             (refl (b .map) (blind_std_dih_reach_left n (w .fst)))))
        (quotient_surjective Int R q) ]

def blind_std_dih_connected (n : Order)
  : BicycleConnected (Sum (BlindZn n) (BlindZn n)) (blind_std_dih_a n) (blind_std_dih_b n)
  ≔ bicycle_connected_from_point (Sum (BlindZn n) (BlindZn n)) (blind_std_dih_a n) (blind_std_dih_b n)
      (inl. (blind_zn_class n int_zero)) (blind_std_dih_reach n)

def blind_std_dihedral_bicycle (n : Order) : Bicycles
  ≔ mkbicycle (Sum (BlindZn n) (BlindZn n), sum_set (BlindZn n) (BlindZn n) (blind_zn_set n) (blind_zn_set n))
      (blind_std_dih_a n) (blind_std_dih_b n) (blind_std_dih_connected n)

{` con:bidirectional-bicycle. A pointed equivalence BD_n ≃* (Bicyc_(standard dihedral bicycle), pt). `}
def blind_con_bidirectional_bicycle : Type
  ≔ (n : Order) (w : BlindDihedralData n)
    → BookPointedEquiv (BG (blind_dihedral n w))
        (NativeComponent Bicycles (blind_std_dihedral_bicycle n),
         component_point Bicycles (blind_std_dihedral_bicycle n))

{` congp.tex:189. The map φ(S, X, f) ≔ (S × X, a, b), a(s,x) = (s, f_s x), b(s,x) = (swap s, x)
   of the implementation is an equivalence BD_n → Bicyc_(std). Bicycles are compared through their
   underlying (carrier, a, b) as functions; the inverse ψ (orbit quotients Y/a, Y/b) is not named. `}
def BlindPreBicycle : Type ≔ Σ SetTypes (Y ↦ Product (Y .fst → Y .fst) (Y .fst → Y .fst))

def blind_bicycle_forget (B : Bicycles) : BlindPreBicycle
  ≔ (B .fst, (bicycle_a B .map, bicycle_b B .map))

def blind_bidirectional_formula (n : Order) (w : BlindDihedralData n) (u : BG (blind_dihedral n w) .carrier)
  : BlindPreBicycle
  ≔ let S ≔ u .fst in let X ≔ u .snd .fst .fst in let f ≔ u .snd .fst .snd in
    ((Product (two_set_carrier S) (X .fst),
      sigma_set (two_set_carrier S) (_ ↦ X .fst) (S .fst .snd) (_ ↦ X .snd)),
     (v ↦ (v .fst, f (v .fst) (v .snd)), v ↦ (two_set_swap S (v .fst), v .snd)))

def blind_xca_bidirectional_inverse : Type
  ≔ (n : Order) (w : BlindDihedralData n)
    → Σ (BG (blind_dihedral n w) .carrier → NativeComponent Bicycles (blind_std_dihedral_bicycle n)) (phi ↦
        Product ((u : BG (blind_dihedral n w) .carrier)
                  → Id BlindPreBicycle (blind_bicycle_forget (phi u .fst)) (blind_bidirectional_formula n w u))
                (BookIsEquiv (BG (blind_dihedral n w) .carrier) (NativeComponent Bicycles (blind_std_dihedral_bicycle n)) phi))

{` congp.tex:196. Q_8 and D_4 are not isomorphic. `}
def blind_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))

def blind_xca_q8_d4 : Type
  ≔ (w : BlindDihedralData (principal_order blind_four))
    → GroupIso quaternion_group (blind_dihedral (principal_order blind_four) w) → Empty
