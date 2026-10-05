export "02-dihedral"
export "../../../src/142-quotient-cycles"
export "../../../src/809-dihedral-three-comparison"
export "../../../src/812-dihedral-quaternion"
export "../../../src/816-dihedral-bicycle-loops"

{` Bridges for congp.tex, the dihedral blocks of the blind file
   02-dihedral (lines 79, 90 def:gen-dihedral, 109 con:bidirectional-bicycle,
   189, 196).

   Z/~_n: the blind BlindZn n is literally our SubgroupQuotient of the periods
   of n (the carrier of standard_cycle n). The blind relation on S × Z states
   z ~_n z' as [z] = [z'] in Z/~_n, ours as z − z' ∈ H (resp. z + z' ∈ H);
   they are logically equivalent (quotient_effective, −(−z') = z'). The blind
   X is the image of the truncated relation; written as the Quotient of the
   EquivalenceRelation b02_blind_relation it is judgmentally Quotient, so the
   two quotient_rec maps are inverse (on classes by refl) and commute with
   the classes judgmentally.

   Every f satisfying the two printed equations is our dihedral_move
   transported to the blind X (b02_f_unique, using that the classes cover X),
   so for every witness w the blind point (X, w) of T_S is identified with
   our dihedral_point (bridge_def_dihedral_shape). Hence the blind C̃_n and
   D_n are ours (bridge_def_cyclic_action, bridge_def_dihedral; the blind and
   our semidirect products are judgmentally equal). The blind standard
   dihedral bicycle has the same carrier and the same maps as ours
   (bridge_def_std_dihedral_bicycle). The statements are transported along
   these paths. `}

{` Z/~_n with its set structure. `}
def bridge_def_zn (n : Order) : Id SetTypes (BlindZn n, blind_zn_set n) (standard_cycle n .fst .fst)
  ≔ refl (standard_cycle n .fst .fst)

{` The relation. `}
def b02_eq_to (n : Order) (x y : Int) (e : Id (BlindZn n) (blind_zn_class n x) (blind_zn_class n y))
  : SubgroupMember (order_periods n) (int_sub x y)
  ≔ quotient_effective Int (subgroup_relation (order_periods n) (order_subgroup_laws n)) x y .map e

def b02_eq_from (n : Order) (x y : Int) (k : SubgroupMember (order_periods n) (int_sub x y))
  : Id (BlindZn n) (blind_zn_class n x) (blind_zn_class n y)
  ≔ quotient_encode Int (subgroup_relation (order_periods n) (order_subgroup_laws n)) x y k

def b02_neg_path (x y : Int) : Id Int (int_sub x (int_neg y)) (int_add x y)
  ≔ refl (int_add x) (int_neg_neg y)

def b02_rel_to (n : Order) (S : TwoElementSets) (u v : DihedralPair S) (r : BlindDihRel n S u v)
  : DihedralRel S (order_periods n) u v
  ≔ match r [
  | inl. a ↦ inl. (a .fst, b02_eq_to n (u .snd) (v .snd) (a .snd))
  | inr. b ↦ inr. (b .fst, refl (SubgroupMember (order_periods n)) (b02_neg_path (u .snd) (v .snd)) .trr
        (b02_eq_to n (u .snd) (int_neg (v .snd)) (b .snd))) ]

def b02_rel_from (n : Order) (S : TwoElementSets) (u v : DihedralPair S) (r : DihedralRel S (order_periods n) u v)
  : BlindDihRel n S u v
  ≔ match r [
  | inl. a ↦ inl. (a .fst, b02_eq_from n (u .snd) (v .snd) (a .snd))
  | inr. b ↦ inr. (b .fst, b02_eq_from n (u .snd) (int_neg (v .snd))
        (refl (SubgroupMember (order_periods n)) (b02_neg_path (u .snd) (v .snd)) .trl (b .snd))) ]

def bridge_def_dih_rel (n : Order) (S : TwoElementSets) (u v : DihedralPair S)
  : Product (BlindDihRel n S u v → DihedralRel S (order_periods n) u v)
      (DihedralRel S (order_periods n) u v → BlindDihRel n S u v)
  ≔ (b02_rel_to n S u v, b02_rel_from n S u v)

{` Footnote: ~ is an equivalence relation (from ours). `}
def bridge_dihedral_relation_equivalence : blind_dihedral_relation_equivalence
  ≔ n S ↦
    let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    (u ↦ b02_rel_from n S u u (dihedral_relation S H h .reflexive u),
     (u v r ↦ b02_rel_from n S v u (dihedral_rel_symmetric S H h u v (b02_rel_to n S u v r)),
      u v w r1 r2 ↦ b02_rel_from n S u w
        (dihedral_rel_transitive S H h u v w (b02_rel_to n S u v r1) (b02_rel_to n S v w r2))))

def b02_mere_to (n : Order) (S : TwoElementSets) (u v : DihedralPair S) (m : Mere (BlindDihRel n S u v))
  : DihedralRel S (order_periods n) u v
  ≔ mere_rec (BlindDihRel n S u v) (DihedralRel S (order_periods n) u v) (dihedral_rel_prop S (order_periods n) u v)
      (b02_rel_to n S u v) m

def b02_mere_from (n : Order) (S : TwoElementSets) (u v : DihedralPair S) (r : DihedralRel S (order_periods n) u v)
  : Mere (BlindDihRel n S u v)
  ≔ mere (BlindDihRel n S u v) (b02_rel_from n S u v r)

{` The blind truncated relation as an EquivalenceRelation; BlindDihX n S is
   judgmentally its Quotient. `}
def b02_blind_relation (n : Order) (S : TwoElementSets) : EquivalenceRelation (DihedralPair S)
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    (blind_dih_pred n S,
     u ↦ b02_mere_from n S u u (dihedral_relation S H h .reflexive u),
     u v r ↦ b02_mere_from n S v u (dihedral_rel_symmetric S H h u v (b02_mere_to n S u v r)),
     u v w r1 r2 ↦ b02_mere_from n S u w
       (dihedral_rel_transitive S H h u v w (b02_mere_to n S u v r1) (b02_mere_to n S v w r2)))

{` X: the blind image of the truncated relation vs our DihedralCycleSet. `}
def b02_x_to (n : Order) (S : TwoElementSets) (x : BlindDihX n S)
  : DihedralCycleSet S (order_periods n) (order_subgroup_laws n)
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    quotient_rec (DihedralPair S) (DihedralCycleSet S H h) (b02_blind_relation n S) (dihedral_cycle_set_set S H h)
      (u ↦ quotient_class (DihedralPair S) (dihedral_relation S H h) u)
      (u v r ↦ dihedral_class_path S H h u v (b02_mere_to n S u v r)) x

def b02_x_from (n : Order) (S : TwoElementSets) (x : DihedralCycleSet S (order_periods n) (order_subgroup_laws n))
  : BlindDihX n S
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    quotient_rec (DihedralPair S) (BlindDihX n S) (dihedral_relation S H h) (blind_dih_set n S)
      (u ↦ blind_dih_class n S u)
      (u v r ↦ quotient_encode (DihedralPair S) (b02_blind_relation n S) u v (b02_mere_from n S u v r)) x

def b02_x_to_from (n : Order) (S : TwoElementSets) (x : DihedralCycleSet S (order_periods n) (order_subgroup_laws n))
  : Id (DihedralCycleSet S (order_periods n) (order_subgroup_laws n)) (b02_x_to n S (b02_x_from n S x)) x
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (y ↦ Id (DihedralCycleSet S H h) (b02_x_to n S (b02_x_from n S y)) y)
      (y ↦ dihedral_cycle_set_set S H h (b02_x_to n S (b02_x_from n S y)) y)
      (u ↦ refl (quotient_class (DihedralPair S) (dihedral_relation S H h) u)) x

def b02_x_from_to (n : Order) (S : TwoElementSets) (x : BlindDihX n S)
  : Id (BlindDihX n S) (b02_x_from n S (b02_x_to n S x)) x
  ≔ quotient_prop_induction (DihedralPair S) (b02_blind_relation n S)
      (y ↦ Id (BlindDihX n S) (b02_x_from n S (b02_x_to n S y)) y)
      (y ↦ blind_dih_set n S (b02_x_from n S (b02_x_to n S y)) y)
      (u ↦ refl (blind_dih_class n S u)) x

def bridge_def_dih_x (n : Order) (S : TwoElementSets)
  : Equiv (BlindDihX n S) (DihedralCycleSet S (order_periods n) (order_subgroup_laws n))
  ≔ quasi_inverse_equiv (BlindDihX n S) (DihedralCycleSet S (order_periods n) (order_subgroup_laws n))
      (b02_x_to n S) (b02_x_from n S) (b02_x_from_to n S) (b02_x_to_from n S)

{` The equivalence commutes with the classes judgmentally. `}
def bridge_def_dih_x_class (n : Order) (S : TwoElementSets) (s : two_set_carrier S) (z : Int)
  : Id (DihedralCycleSet S (order_periods n) (order_subgroup_laws n))
      (bridge_def_dih_x n S .map (blind_dih_class n S (s, z))) (dihedral_class S (order_periods n) (order_subgroup_laws n) s z)
  ≔ refl (dihedral_class S (order_periods n) (order_subgroup_laws n) s z)

{` Our f transported to the blind X. `}
def b02_f0 (n : Order) (S : TwoElementSets) (s : two_set_carrier S) (x : BlindDihX n S) : BlindDihX n S
  ≔ b02_x_from n S (dihedral_move S (order_periods n) (order_subgroup_laws n) s (b02_x_to n S x))

{` congp.tex:79, first part. `}
def bridge_xca_dihedral_well_defined : blind_xca_dihedral_well_defined
  ≔ n S ↦
    let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    (b02_f0 n S,
     (s z ↦ refl (b02_x_from n S) (dihedral_move_self S H h s z),
      s s' z ne ↦ refl (b02_x_from n S) (dihedral_move_other S H h s s' ne z)))

{` Every f satisfying the two equations agrees with ours on classes ... `}
def b02_f_at (n : Order) (S : TwoElementSets) (w : BlindDihedralF n S) (s s' : two_set_carrier S) (z : Int)
  : Id (BlindDihX n S) (w .fst s (blind_dih_class n S (s', z))) (b02_f0 n S s (blind_dih_class n S (s', z)))
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    let X ≔ BlindDihX n S in
    match two_set_decidable S s' s [
    | inl. p ↦ transport (two_set_carrier S)
        (t ↦ Id X (w .fst s (blind_dih_class n S (t, z))) (b02_f0 n S s (blind_dih_class n S (t, z))))
        s s' (inverse (two_set_carrier S) s' s p)
        (concat X (w .fst s (blind_dih_class n S (s, z))) (blind_dih_class n S (s, int_succ z))
           (b02_f0 n S s (blind_dih_class n S (s, z)))
           (w .snd .fst s z)
           (inverse X (b02_f0 n S s (blind_dih_class n S (s, z))) (blind_dih_class n S (s, int_succ z))
              (refl (b02_x_from n S) (dihedral_move_self S H h s z))))
    | inr. ne ↦ concat X (w .fst s (blind_dih_class n S (s', z))) (blind_dih_class n S (s', int_pred z))
        (b02_f0 n S s (blind_dih_class n S (s', z)))
        (w .snd .snd s s' z ne)
        (inverse X (b02_f0 n S s (blind_dih_class n S (s', z))) (blind_dih_class n S (s', int_pred z))
           (refl (b02_x_from n S) (dihedral_move_other S H h s s' ne z))) ]

{` ... hence everywhere, since the classes cover X: f is unique. `}
def b02_f_unique (n : Order) (S : TwoElementSets) (w : BlindDihedralF n S)
  : Id (two_set_carrier S → BlindDihX n S → BlindDihX n S) (w .fst) (b02_f0 n S)
  ≔ funext (two_set_carrier S) (_ ↦ BlindDihX n S → BlindDihX n S) (w .fst) (b02_f0 n S)
      (s ↦ funext (BlindDihX n S) (_ ↦ BlindDihX n S) (w .fst s) (b02_f0 n S s)
        (x ↦ quotient_prop_induction (DihedralPair S) (b02_blind_relation n S)
          (y ↦ Id (BlindDihX n S) (w .fst s y) (b02_f0 n S s y))
          (y ↦ blind_dih_set n S (w .fst s y) (b02_f0 n S s y))
          (u ↦ b02_f_at n S w s (u .fst) (u .snd)) x))

def bridge_def_dihedral_f_unique (n : Order) (S : TwoElementSets) (w1 w2 : BlindDihedralF n S)
  : Id (two_set_carrier S → BlindDihX n S → BlindDihX n S) (w1 .fst) (w2 .fst)
  ≔ concat (two_set_carrier S → BlindDihX n S → BlindDihX n S) (w1 .fst) (b02_f0 n S) (w2 .fst)
      (b02_f_unique n S w1) (inverse (two_set_carrier S → BlindDihX n S → BlindDihX n S) (w2 .fst) (b02_f0 n S)
        (b02_f_unique n S w2))

{` For every witness, the blind (X, f) is our (X, f) in T_S. `}
def bridge_def_dihedral_shape (n : Order) (S : TwoElementSets) (w : BlindDihedralF n S)
  : Id (S2C3Type S) ((BlindDihX n S, blind_dih_set n S), w .fst) (dihedral_point S (order_periods n) (order_subgroup_laws n))
  ≔ let H ≔ order_periods n in let h ≔ order_subgroup_laws n in
    dihedral_s2c3_path S ((BlindDihX n S, blind_dih_set n S), w .fst) (dihedral_point S H h)
      (bridge_def_dih_x n S,
       s x ↦ concat (DihedralCycleSet S H h)
         (b02_x_to n S (w .fst s x)) (b02_x_to n S (b02_f0 n S s x)) (dihedral_move S H h s (b02_x_to n S x))
         (refl (b02_x_to n S) (b02_f_unique n S w (refl s) (refl x)))
         (b02_x_to_from n S (dihedral_move S H h s (b02_x_to n S x))))

{` congp.tex:79, second part (n = 3), from dihedral_three_point_path. `}
def bridge_xca_dihedral_three : blind_xca_dihedral_three
  ≔ S w ↦ concat (S2C3Type S)
      ((BlindDihX (principal_order three) S, blind_dih_set (principal_order three) S), w .fst)
      (dihedral_point S dihedral_three_H dihedral_three_laws) (s2c3_point S)
      (bridge_def_dihedral_shape (principal_order three) S w)
      (inverse (S2C3Type S) (s2c3_point S) (dihedral_point S dihedral_three_H dihedral_three_laws)
        (dihedral_three_point_path dihedral_three_H dihedral_three_laws dihedral_three_facts S))

{` def:gen-dihedral: C̃_n and D_n as functions of the point S ↦ (X_S, f). `}
def b02_our_shape (n : Order) (S : TwoElementSets) : S2C3Type S
  ≔ dihedral_point S (order_periods n) (order_subgroup_laws n)

def b02_shape_path (n : Order) (w : BlindDihedralData n)
  : Id ((S : TwoElementSets) → S2C3Type S) (blind_dihedral_shape n w) (b02_our_shape n)
  ≔ funext TwoElementSets S2C3Type (blind_dihedral_shape n w) (b02_our_shape n)
      (S ↦ bridge_def_dihedral_shape n S (w S))

def b02_action (sh : (S : TwoElementSets) → S2C3Type S) (S : TwoElementSets) : Group
  ≔ automorphism_group (S2C3Type S) (s2c3_type_groupoid S) (sh S)

def b02_group (sh : (S : TwoElementSets) → S2C3Type S) : Group
  ≔ blind_semidirect (symmetric_group two) (b02_action sh)

def bridge_def_cyclic_action (n : Order) (w : BlindDihedralData n)
  : Id (TwoElementSets → Group) (blind_cyclic_action n w) (dihedral_order_action n)
  ≔ refl b02_action (b02_shape_path n w)

{` The blind semidirect product is judgmentally ours. `}
def bridge_def_semidirect_dihedral (G : Group) (K : BG G .carrier → Group)
  : Id Group (blind_semidirect G K) (semidirect_product G K)
  ≔ refl (semidirect_product G K)

def bridge_def_dihedral (n : Order) (w : BlindDihedralData n)
  : Id Group (blind_dihedral n w) (generalized_dihedral_group n)
  ≔ refl b02_group (b02_shape_path n w)

{` The standard dihedral bicycle: same carrier, same a and b. `}
def b02_std_a_agree (n : Order) (y : Sum (BlindZn n) (BlindZn n))
  : Id (Sum (BlindZn n) (BlindZn n))
      (dihedral_standard_a (order_periods n) (order_subgroup_laws n) .map y) (blind_std_dih_a n .map y)
  ≔ match y [
  | inl. q ↦ refl (blind_std_dih_a n .map (inl. q))
  | inr. q ↦ refl (blind_std_dih_a n .map (inr. q)) ]

def b02_std_b_agree (n : Order) (y : Sum (BlindZn n) (BlindZn n))
  : Id (Sum (BlindZn n) (BlindZn n))
      (dihedral_standard_b (order_periods n) (order_subgroup_laws n) .map y) (blind_std_dih_b n .map y)
  ≔ match y [
  | inl. q ↦ refl (blind_std_dih_b n .map (inl. q))
  | inr. q ↦ refl (blind_std_dih_b n .map (inr. q)) ]

def bridge_def_std_dihedral_bicycle (n : Order)
  : Id Bicycles (standard_dihedral_bicycle n) (blind_std_dihedral_bicycle n)
  ≔ bicycle_path_from_iso (standard_dihedral_bicycle n) (blind_std_dihedral_bicycle n)
      (identity_equiv (Sum (BlindZn n) (BlindZn n)), (y ↦ b02_std_a_agree n y, y ↦ b02_std_b_agree n y))

{` con:bidirectional-bicycle, from bidirectional_bicycle_pointed_equiv. `}
def bridge_con_bidirectional_bicycle : blind_con_bidirectional_bicycle
  ≔ n w ↦
    transport Group
      (G ↦ BookPointedEquiv (BG G)
         (NativeComponent Bicycles (blind_std_dihedral_bicycle n), component_point Bicycles (blind_std_dihedral_bicycle n)))
      (generalized_dihedral_group n) (blind_dihedral n w)
      (inverse Group (blind_dihedral n w) (generalized_dihedral_group n) (bridge_def_dihedral n w))
      (transport Bicycles
         (B ↦ BookPointedEquiv (BG (generalized_dihedral_group n)) (NativeComponent Bicycles B, component_point Bicycles B))
         (standard_dihedral_bicycle n) (blind_std_dihedral_bicycle n) (bridge_def_std_dihedral_bicycle n)
         (bidirectional_bicycle_pointed_equiv n))

{` congp.tex:189: the statement as a family over the point S ↦ (X_S, f) and
   the target bicycle. `}
def b02_formula (sh : (S : TwoElementSets) → S2C3Type S) (u : BG (b02_group sh) .carrier) : BlindPreBicycle
  ≔ let S ≔ u .fst in let X ≔ u .snd .fst .fst in let f ≔ u .snd .fst .snd in
    ((Product (two_set_carrier S) (X .fst),
      sigma_set (two_set_carrier S) (_ ↦ X .fst) (S .fst .snd) (_ ↦ X .snd)),
     (v ↦ (v .fst, f (v .fst) (v .snd)), v ↦ (two_set_swap S (v .fst), v .snd)))

def B02Inverse (sh : (S : TwoElementSets) → S2C3Type S) (B : Bicycles) : Type
  ≔ Σ (BG (b02_group sh) .carrier → NativeComponent Bicycles B) (phi ↦
      Product ((u : BG (b02_group sh) .carrier)
                → Id BlindPreBicycle (blind_bicycle_forget (phi u .fst)) (b02_formula sh u))
              (BookIsEquiv (BG (b02_group sh) .carrier) (NativeComponent Bicycles B) phi))

def b02_inverse_ours (n : Order) : B02Inverse (b02_our_shape n) (standard_dihedral_bicycle n)
  ≔ (bidirectional_bicycle_pointed_equiv n .fst .fst,
     (u ↦ refl (b02_formula (b02_our_shape n) u), bidirectional_bicycle_pointed_equiv n .snd))

def bridge_xca_bidirectional_inverse : blind_xca_bidirectional_inverse
  ≔ n w ↦
    transport ((S : TwoElementSets) → S2C3Type S) (sh ↦ B02Inverse sh (blind_std_dihedral_bicycle n))
      (b02_our_shape n) (blind_dihedral_shape n w)
      (inverse ((S : TwoElementSets) → S2C3Type S) (blind_dihedral_shape n w) (b02_our_shape n) (b02_shape_path n w))
      (transport Bicycles (B ↦ B02Inverse (b02_our_shape n) B)
         (standard_dihedral_bicycle n) (blind_std_dihedral_bicycle n) (bridge_def_std_dihedral_bicycle n)
         (b02_inverse_ours n))

{` congp.tex:196: Q_8 and D_4 are not isomorphic, for every witness. `}
def bridge_xca_q8_d4 : blind_xca_q8_d4
  ≔ w ↦ transport Group (G ↦ GroupIso quaternion_group G → Empty)
      (generalized_dihedral_group (principal_order blind_four)) (blind_dihedral (principal_order blind_four) w)
      (inverse Group (blind_dihedral (principal_order blind_four) w) (generalized_dihedral_group (principal_order blind_four))
        (bridge_def_dihedral (principal_order blind_four) w))
      (f ↦ quaternion_dihedral_not_isomorphic f)
