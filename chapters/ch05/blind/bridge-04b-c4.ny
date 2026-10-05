{` Bridges for chapter 5: the C₄-set of 4-bit sequences (exa:fixed-free-neither, xca:fixed-free-neither,
   xca:fixed-free-neither-action-types, exa:prep-burnside / fig:C4-action-on-4-bits). `}
export "bridge-04-torsors"

def bridge_def_C4 : Id Group blind_C4 c4bits_group ≔ refl c4bits_group

def bridge_def_c4_set : Id (GSet c4bits_group) blind_c4_set bits4_gset ≔ refl bits4_gset

{` The blind Boolean tests agree with our row tables (checked on all 16 sequences by computation). `}
def bridge_c4_constant_row (f : Bits4) : Id Bool (blind_c4_constant f) (bits4_row_fixed (bits4_orbit_index f))
  ≔ bits4_check_point blind_c4_constant (x ↦ bits4_row_fixed (bits4_orbit_index x)) (refl (true. : Bool)) f

def bridge_c4_period2_row (f : Bits4) : Id Bool (blind_c4_period2 f) (bool_not (bits4_row_free (bits4_orbit_index f)))
  ≔ bits4_check_point blind_c4_period2 (x ↦ bool_not (bits4_row_free (bits4_orbit_index x))) (refl (true. : Bool)) f

def bridge_c4_bool_code : Bool → Type ≔ [ true. ↦ Unit | false. ↦ Empty ]

def bridge_c4_true_ne_false (p : Id Bool true. false.) : Empty ≔ transport Bool bridge_c4_bool_code true. false. p star.

def bridge_bnot_true (b : Bool) : Id Bool b true. → Id Bool (bool_not b) false.
  ≔ match b [ true. ↦ _ ↦ refl (false. : Bool) | false. ↦ h ↦ match bridge_c4_true_ne_false (inverse Bool false. true. h) [] ]

def bridge_bnot_false (b : Bool) : Id Bool (bool_not b) false. → Id Bool b true.
  ≔ match b [ true. ↦ _ ↦ refl (true. : Bool) | false. ↦ h ↦ match bridge_c4_true_ne_false h [] ]

{` exa:fixed-free-neither, the C₄ part: fixed iff constant, free iff not of period 2. `}
def bridge_c4_fixed_free : blind_c4_fixed_free
  ≔ f ↦
    let r ≔ bits4_orbit_index f in
    let c1 ≔ bridge_c4_constant_row f in
    let c2 ≔ bridge_c4_period2_row f in
    ((h ↦ concat Bool (blind_c4_constant f) (bits4_row_fixed r) true. c1 (bits4_fixed_row_equiv f .map h),
      e ↦ equiv_inverse_map (IsFixedElement c4bits_group bits4_gset f) (Id Bool (bits4_row_fixed r) true.) (bits4_fixed_row_equiv f)
            (concat Bool (bits4_row_fixed r) (blind_c4_constant f) true. (inverse Bool (blind_c4_constant f) (bits4_row_fixed r) c1) e)),
     (h ↦ concat Bool (blind_c4_period2 f) (bool_not (bits4_row_free r)) false. c2
            (bridge_bnot_true (bits4_row_free r) (bits4_free_row_equiv f .map (bridge_def_free c4bits_group bits4_gset f .fst h))),
      e ↦ bridge_def_free c4bits_group bits4_gset f .snd
            (equiv_inverse_map (IsFreeElement c4bits_group bits4_gset f) (Id Bool (bits4_row_free r) true.) (bits4_free_row_equiv f)
              (bridge_bnot_false (bits4_row_free r)
                (concat Bool (bool_not (bits4_row_free r)) (blind_c4_period2 f) false.
                  (inverse Bool (blind_c4_period2 f) (bool_not (bits4_row_free r)) c2) e)))))

{` The blind cardinality tables agree with our row tables. `}
def bridge_select_rows (a b d : Nat) (f : Bits4)
  : Id Nat (blind_select (blind_c4_constant f) (blind_c4_period2 f) a b d)
      (blind_select (bits4_row_fixed (bits4_orbit_index f)) (bool_not (bits4_row_free (bits4_orbit_index f))) a b d)
  ≔ concat Nat (blind_select (blind_c4_constant f) (blind_c4_period2 f) a b d)
      (blind_select (bits4_row_fixed (bits4_orbit_index f)) (blind_c4_period2 f) a b d)
      (blind_select (bits4_row_fixed (bits4_orbit_index f)) (bool_not (bits4_row_free (bits4_orbit_index f))) a b d)
      (refl ((c ↦ blind_select c (blind_c4_period2 f) a b d) : Bool → Nat) (bridge_c4_constant_row f))
      (refl ((p ↦ blind_select (bits4_row_fixed (bits4_orbit_index f)) p a b d) : Bool → Nat) (bridge_c4_period2_row f))

def bridge_row_stab (r : Fin c4bits_six)
  : Id Nat (blind_select (bits4_row_fixed r) (bool_not (bits4_row_free r)) blind_four two (suc. zero.)) (bits4_row_stab_card r)
  ≔ bits4_row_ind (r' ↦ Id Nat (blind_select (bits4_row_fixed r') (bool_not (bits4_row_free r')) blind_four two (suc. zero.))
        (bits4_row_stab_card r'))
      (refl blind_four) (refl blind_four) (refl (suc. zero. : Nat)) (refl (suc. zero. : Nat)) (refl two) (refl (suc. zero. : Nat)) r

def bridge_row_size (r : Fin c4bits_six)
  : Id Nat (blind_select (bits4_row_fixed r) (bool_not (bits4_row_free r)) (suc. zero.) two blind_four) (bits4_row_size r)
  ≔ bits4_row_ind (r' ↦ Id Nat (blind_select (bits4_row_fixed r') (bool_not (bits4_row_free r')) (suc. zero.) two blind_four)
        (bits4_row_size r'))
      (refl (suc. zero. : Nat)) (refl (suc. zero. : Nat)) (refl blind_four) (refl blind_four) (refl two) (refl blind_four) r

def bridge_c4_stab_card (f : Bits4) : Id Nat (bits4_row_stab_card (bits4_orbit_index f)) (blind_c4_stab_card f)
  ≔ inverse Nat (blind_c4_stab_card f) (bits4_row_stab_card (bits4_orbit_index f))
      (concat Nat (blind_c4_stab_card f)
        (blind_select (bits4_row_fixed (bits4_orbit_index f)) (bool_not (bits4_row_free (bits4_orbit_index f))) blind_four two (suc. zero.))
        (bits4_row_stab_card (bits4_orbit_index f))
        (bridge_select_rows blind_four two (suc. zero.) f) (bridge_row_stab (bits4_orbit_index f)))

def bridge_c4_orbit_card (f : Bits4) : Id Nat (bits4_row_size (bits4_orbit_index f)) (blind_c4_orbit_card f)
  ≔ inverse Nat (blind_c4_orbit_card f) (bits4_row_size (bits4_orbit_index f))
      (concat Nat (blind_c4_orbit_card f)
        (blind_select (bits4_row_fixed (bits4_orbit_index f)) (bool_not (bits4_row_free (bits4_orbit_index f))) (suc. zero.) two blind_four)
        (bits4_row_size (bits4_orbit_index f))
        (bridge_select_rows (suc. zero.) two blind_four f) (bridge_row_size (bits4_orbit_index f)))

{` xca:fixed-free-neither. `}
def bridge_xca_fixed_free_neither : blind_xca_fixed_free_neither
  ≔ (G S s ↦ bridge_triv_stabilizer_path G S s,
     (G g ↦ fixed_free_principal_classifying_contr G g,
      f ↦ (bits4_stabilizer_finite f,
           concat Nat (group_card (stabilizer_group c4bits_group bits4_gset f) (bits4_stabilizer_finite f))
             (bits4_row_stab_card (bits4_orbit_index f)) (blind_c4_stab_card f)
             (bits4_stabilizer_card f (bits4_stabilizer_finite f)) (bridge_c4_stab_card f))))

{` xca:fixed-free-neither-action-types. `}
def bridge_fixed_free_neither_action_types : blind_fixed_free_neither_action_types
  ≔ (G S s ↦ fixed_free_trivial_action_type_contr G S s,
     (G g ↦ fixed_free_principal_action_type_equiv G g,
      f ↦
        let T ≔ ActionType (stabilizer_group c4bits_group bits4_gset f) (stabilizer_tilde_gset c4bits_group bits4_gset f) in
        let n ≔ bits4_row_size (bits4_orbit_index f) in
        let p : Id Type T (Fin n) ≔ ua T (Fin n) (bits4_stabilizer_action_type_equiv f) in
        let h : IsFinite T ≔ mere (Σ Nat (k ↦ Id Type T (Fin k))) (n, p) in
        (h, concat Nat (cardinality T h) n (blind_c4_orbit_card f) (cardinality_from_path T h n p) (bridge_c4_orbit_card f))))

{` exa:prep-burnside. `}
def bridge_c4_underlying : blind_c4_underlying ≔ refl Bits4

def bridge_c4_six_orbits : blind_c4_six_orbits ≔ (bits4_orbits_finite, bits4_orbits_card bits4_orbits_finite)

def bridge_def_fixed_by (G : Group) (X : GSet G) (g : USym G) : Id Type (BlindFixedBy G X g) (FixedBy G X g)
  ≔ refl (FixedBy G X g)

def bridge_c4_24_pairs : blind_c4_24_pairs ≔ (bits4_fixed_pairs_finite, bits4_fixed_pairs_card bits4_fixed_pairs_finite)

def bridge_c4_orbit_times_stabilizer : blind_c4_orbit_times_stabilizer
  ≔ τ ↦ bridge_tau c4bits_group bits4_gset
      (τ' ↦ (f : Bits4) (h1 : IsFinite (BlindOrbitSet c4bits_group bits4_gset τ' f))
        (h2 : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset f))
        → Id Nat (mul (cardinality (BlindOrbitSet c4bits_group bits4_gset τ' f) h1) (group_card (stabilizer_group c4bits_group bits4_gset f) h2))
            blind_four)
      (f h1 h2 ↦ concat Nat
         (mul (cardinality (OrbitUnderlying c4bits_group bits4_gset f) h1) (group_card (stabilizer_group c4bits_group bits4_gset f) h2))
         (group_card c4bits_group (cyclic_group_fin_finite c4bits_three)) blind_four
         (bits4_orbit_stabilizer_product f h1 h2) (cyclic_group_fin_card c4bits_three))
      τ

{` exa:prep-burnside: s^k rotates sequences, (s^k · f)(a) = f(s^{-k}(a)). `}
def bridge_c4_power_trr (k : Int) (x : Bits4Pos)
  : Id Bits4Pos (cycle_group_power (finite_fin_cycle three) k .fst .fst .fst .fst .trr x)
      (permutation_power Bits4Pos (finite_fin_successor three) k x)
  ≔ let c ≔ finite_fin_cycle three in
    let g ≔ cycle_group_power c k in
    let lp ≔ loop_power Cycles c (cycle_generating_loop c) k in
    concat Bits4Pos (g .fst .fst .fst .fst .trr x) (cycle_path_evaluate c c (g .fst) x)
      (permutation_power Bits4Pos (finite_fin_successor three) k x)
      (inverse Bits4Pos (cycle_path_evaluate c c (g .fst) x) (g .fst .fst .fst .fst .trr x) (cycle_path_evaluate_transport c c (g .fst) x))
      (concat Bits4Pos (cycle_path_evaluate c c (g .fst) x) (cycle_path_evaluate c c lp x)
         (permutation_power Bits4Pos (finite_fin_successor three) k x)
         (refl ((l ↦ cycle_path_evaluate c c l x) : Id Cycles c c → Bits4Pos)
           (map_loop_power (NativeComponent Cycles c) Cycles (u ↦ u .fst) (component_point Cycles c) (cycle_group_generator c) k))
         (cycle_generator_power_eval c k x))

def bridge_c4_rotation : blind_c4_rotation
  ≔ k f a ↦
    let g ≔ cycle_group_power (finite_fin_cycle three) k in
    let s ≔ finite_fin_successor three in
    let P ≔ g .fst .fst .fst .fst in
    let y ≔ permutation_power Bits4Pos s (int_neg k) a in
    let e1 : Id Bits4Pos (P .trr y) a
      ≔ concat Bits4Pos (P .trr y) (permutation_power Bits4Pos s k y) a (bridge_c4_power_trr k y)
          (permutation_power_inverse_other Bits4Pos s k a) in
    let e2 : Id Bits4Pos (P .trl a) y
      ≔ concat Bits4Pos (P .trl a) (P .trl (P .trr y)) y
          (refl ((b ↦ P .trl b) : Bits4Pos → Bits4Pos) (inverse Bits4Pos (P .trr y) a e1))
          (type_path_trl_trr Bits4Pos Bits4Pos P y) in
    concat (Fin two) (gset_usym_act c4bits_group bits4_gset g f a) (f (P .trl a)) (f y) (bits4_act_pointwise g f a) (refl f e2)
