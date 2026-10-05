export "587-c4-bit-orbits"

{` exa:prep-burnside (part 3): stabilizers and counting.

   The right column of fig:C4-action-on-4-bits (bits4_row_stab): the symmetry
   g stabilizes x iff g(0) is listed in the row of x (bits4_stabilizes_equiv);
   USym((C_4)_x) has 4, 4, 1, 1, 2, 1 elements in the six rows
   (bits4_stabilizer_usym_equiv); Card(C_4 · x) × Card((C_4)_x) = Card(C_4) = 4
   for every x (bits4_orbit_stabilizer_product); the stabilizing symmetries
   only depend on the orbit (bits4_same_orbit_same_stabilizer); and there are
   24 pairs (g, x) with g · x = x (bits4_fixed_pairs_card). `}

{` Right column of fig:C4-action-on-4-bits: k is listed in row r. `}
def bits4_row_stab (r : Fin c4bits_six) (k : Bits4Pos) : Bool
  ≔ bits4_row_ind (_ ↦ Bits4Pos → Bool) (_ ↦ true.) (_ ↦ true.)
      (k' ↦ bits4_pos_ind (_ ↦ Bool) true. false. false. false. k')
      (k' ↦ bits4_pos_ind (_ ↦ Bool) true. false. false. false. k')
      (k' ↦ bits4_pos_ind (_ ↦ Bool) true. false. true. false. k')
      (k' ↦ bits4_pos_ind (_ ↦ Bool) true. false. false. false. k') r k

def bits4_stab_bool (x : Bits4) (k : Bits4Pos) : Bool ≔ bits4_eqb (bits4_rot k x) x

{` The table is correct (all 16 × 4 cases). `}
def bits4_stab_check
  : Id Bool (bits4_all (x ↦ bits4_pos_all (k ↦
      bits4_bool_eqb (bits4_stab_bool x k) (bits4_row_stab (bits4_orbit_index x) k)))) true.
  ≔ refl (true. : Bool)

def bits4_stab_bool_table (x : Bits4) (k : Bits4Pos)
  : Id Bool (bits4_stab_bool x k) (bits4_row_stab (bits4_orbit_index x) k)
  ≔ bits4_bool_eqb_sound (bits4_stab_bool x k) (bits4_row_stab (bits4_orbit_index x) k)
      (bits4_fin_all_sound c4bits_four
        (k' ↦ bits4_bool_eqb (bits4_stab_bool x k') (bits4_row_stab (bits4_orbit_index x) k'))
        (bits4_all_sound (x' ↦ bits4_pos_all (k' ↦
            bits4_bool_eqb (bits4_stab_bool x' k') (bits4_row_stab (bits4_orbit_index x') k')))
          bits4_stab_check x) k)

{` g · x = x iff g(0) is listed in the row of x. `}
def bits4_stabilizes_equiv (g : USym c4bits_group) (x : Bits4)
  : Equiv (Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x)
      (Id Bool (bits4_row_stab (bits4_orbit_index x) (bits4_index g)) true.)
  ≔ let k ≔ bits4_index g in
    let r ≔ bits4_orbit_index x in
    let gx ≔ gset_usym_act c4bits_group bits4_gset g x in
    iff_equiv (Id Bits4 gx x) (Id Bool (bits4_row_stab r k) true.)
      (bits4_set gx x) (bool_set (bits4_row_stab r k) true.)
      (p ↦ concat Bool (bits4_row_stab r k) (bits4_stab_bool x k) true.
        (inverse Bool (bits4_stab_bool x k) (bits4_row_stab r k) (bits4_stab_bool_table x k))
        (bits4_eqb_complete (bits4_rot k x) x
          (concat Bits4 (bits4_rot k x) gx x (inverse Bits4 gx (bits4_rot k x) (bits4_act_rot g x)) p)))
      (h ↦ concat Bits4 gx (bits4_rot k x) x (bits4_act_rot g x)
        (bits4_eqb_sound (bits4_rot k x) x
          (concat Bool (bits4_stab_bool x k) (bits4_row_stab r k) true. (bits4_stab_bool_table x k) h)))

{` Number of stabilizing symmetries in each row. `}
def bits4_row_stab_card (r : Fin c4bits_six) : Nat
  ≔ bits4_row_ind (_ ↦ Nat) c4bits_four c4bits_four (suc. zero.) (suc. zero.) two (suc. zero.) r

def bits4_row_stab_count (r : Fin c4bits_six) : Id Nat (true_count c4bits_four (bits4_row_stab r)) (bits4_row_stab_card r)
  ≔ bits4_row_ind (r' ↦ Id Nat (true_count c4bits_four (bits4_row_stab r')) (bits4_row_stab_card r'))
      (refl c4bits_four) (refl c4bits_four) (refl (suc. zero. : Nat)) (refl (suc. zero. : Nat)) (refl two)
      (refl (suc. zero. : Nat)) r

{` USym((C_4)_x) ≃ Fin (number of stabilizing symmetries). `}
def bits4_stabilizer_usym_equiv (x : Bits4)
  : Equiv (USym (stabilizer_group c4bits_group bits4_gset x)) (Fin (bits4_row_stab_card (bits4_orbit_index x)))
  ≔ let r ≔ bits4_orbit_index x in
    let S ≔ Σ (USym c4bits_group) (g ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x) in
    let T ≔ Σ (USym c4bits_group) (g ↦ Id Bool (bits4_row_stab r (bits4_index g)) true.) in
    compose_equiv (USym (stabilizer_group c4bits_group bits4_gset x)) S (Fin (bits4_row_stab_card r))
      (stabilizer_usym_equiv c4bits_group bits4_gset x)
      (compose_equiv S T (Fin (bits4_row_stab_card r))
        (family_equiv (USym c4bits_group) (g ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x)
          (g ↦ Id Bool (bits4_row_stab r (bits4_index g)) true.) (g ↦ bits4_stabilizes_equiv g x))
        (compose_equiv T (BoolCarrier c4bits_four (bits4_row_stab r)) (Fin (bits4_row_stab_card r))
          (sigma_pullback_equiv (USym c4bits_group) Bits4Pos bits4_index_equiv (k ↦ Id Bool (bits4_row_stab r k) true.))
          (compose_equiv (BoolCarrier c4bits_four (bits4_row_stab r)) (Fin (true_count c4bits_four (bits4_row_stab r)))
            (Fin (bits4_row_stab_card r))
            (bool_carrier_fin c4bits_four (bits4_row_stab r))
            (transport_equiv (Fin (true_count c4bits_four (bits4_row_stab r))) (Fin (bits4_row_stab_card r))
              (refl Fin (bits4_row_stab_count r))))))

def bits4_stabilizer_finite (x : Bits4) : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset x)
  ≔ finite_from_equiv (USym (stabilizer_group c4bits_group bits4_gset x)) (bits4_row_stab_card (bits4_orbit_index x))
      (bits4_stabilizer_usym_equiv x)

def bits4_stabilizer_card (x : Bits4) (h : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset x))
  : Id Nat (group_card (stabilizer_group c4bits_group bits4_gset x) h) (bits4_row_stab_card (bits4_orbit_index x))
  ≔ cardinality_from_path (USym (stabilizer_group c4bits_group bits4_gset x)) h (bits4_row_stab_card (bits4_orbit_index x))
      (ua (USym (stabilizer_group c4bits_group bits4_gset x)) (Fin (bits4_row_stab_card (bits4_orbit_index x)))
        (bits4_stabilizer_usym_equiv x))

def bits4_row_product (r : Fin c4bits_six) : Id Nat (mul (bits4_row_size r) (bits4_row_stab_card r)) c4bits_four
  ≔ bits4_row_ind (r' ↦ Id Nat (mul (bits4_row_size r') (bits4_row_stab_card r')) c4bits_four)
      (refl c4bits_four) (refl c4bits_four) (refl c4bits_four) (refl c4bits_four) (refl c4bits_four) (refl c4bits_four) r

{` exa:prep-burnside: Card(C_4 · x) × Card((C_4)_x) = Card(C_4) = 4 for every
   x, for any finiteness witnesses. `}
def bits4_orbit_stabilizer_product (x : Bits4) (hO : IsFinite (OrbitUnderlying c4bits_group bits4_gset x))
  (hS : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset x))
  : Id Nat (mul (cardinality (OrbitUnderlying c4bits_group bits4_gset x) hO) (group_card (stabilizer_group c4bits_group bits4_gset x) hS))
      (group_card c4bits_group (cyclic_group_fin_finite c4bits_three))
  ≔ let r ≔ bits4_orbit_index x in
    let cO ≔ cardinality (OrbitUnderlying c4bits_group bits4_gset x) hO in
    let cS ≔ group_card (stabilizer_group c4bits_group bits4_gset x) hS in
    calc
      mul cO cS
      = mul (bits4_row_size r) cS by refl ((n ↦ mul n cS) : Nat → Nat) (bits4_orbit_card x hO)
      = mul (bits4_row_size r) (bits4_row_stab_card r) by refl (mul (bits4_row_size r)) (bits4_stabilizer_card x hS)
      = c4bits_four by bits4_row_product r
      = group_card c4bits_group (cyclic_group_fin_finite c4bits_three)
        by inverse Nat (group_card c4bits_group (cyclic_group_fin_finite c4bits_three)) c4bits_four
             (cyclic_group_fin_card c4bits_three) ∎

{` "The particular x one chooses within each orbit is irrelevant": elements
   of the same orbit have the same stabilizing symmetries (here literally the
   same, C_4 being abelian), hence stabilizers of the same cardinality. `}
def bits4_same_orbit_same_stabilizer (x y : Bits4)
  (p : Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
  (g : USym c4bits_group) (e : Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x)
  : Id Bits4 (gset_usym_act c4bits_group bits4_gset g y) y
  ≔ equiv_inverse_map (Id Bits4 (gset_usym_act c4bits_group bits4_gset g y) y)
      (Id Bool (bits4_row_stab (bits4_orbit_index y) (bits4_index g)) true.) (bits4_stabilizes_equiv g y)
      (transport (Fin c4bits_six) (r ↦ Id Bool (bits4_row_stab r (bits4_index g)) true.)
        (bits4_orbit_index x) (bits4_orbit_index y) (bits4_same_orbit_equiv x y .map p)
        (bits4_stabilizes_equiv g x .map e))

def bits4_same_orbit_stabilizer_card (x y : Bits4)
  (p : Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
  (hx : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset x)) (hy : IsFiniteGroup (stabilizer_group c4bits_group bits4_gset y))
  : Id Nat (group_card (stabilizer_group c4bits_group bits4_gset x) hx) (group_card (stabilizer_group c4bits_group bits4_gset y) hy)
  ≔ calc
      group_card (stabilizer_group c4bits_group bits4_gset x) hx
      = bits4_row_stab_card (bits4_orbit_index x) by bits4_stabilizer_card x hx
      = bits4_row_stab_card (bits4_orbit_index y) by refl bits4_row_stab_card (bits4_same_orbit_equiv x y .map p)
      = group_card (stabilizer_group c4bits_group bits4_gset y) hy
        by inverse Nat (group_card (stabilizer_group c4bits_group bits4_gset y) hy) (bits4_row_stab_card (bits4_orbit_index y))
             (bits4_stabilizer_card y hy) ∎

{` The 24 pairs (g, x) with g · x = x. `}
def bits4_fixed_count (k : Bits4Pos) : Nat
  ≔ true_count c4bits_sixteen (j ↦ bits4_row_stab (bits4_orbit_index (bits4_decode j)) k)

def bits4_fixed_pairs_equiv
  : Equiv (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)) (Σ Bits4Pos (k ↦ Fin (bits4_fixed_count k)))
  ≔ compose_equiv (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g))
      (Σ (USym c4bits_group) (g ↦ Fin (bits4_fixed_count (bits4_index g)))) (Σ Bits4Pos (k ↦ Fin (bits4_fixed_count k)))
      (family_equiv (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g) (g ↦ Fin (bits4_fixed_count (bits4_index g)))
        (g ↦ compose_equiv (FixedBy c4bits_group bits4_gset g)
          (Σ Bits4 (x ↦ Id Bool (bits4_row_stab (bits4_orbit_index x) (bits4_index g)) true.))
          (Fin (bits4_fixed_count (bits4_index g)))
          (family_equiv Bits4 (x ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x)
            (x ↦ Id Bool (bits4_row_stab (bits4_orbit_index x) (bits4_index g)) true.) (x ↦ bits4_stabilizes_equiv g x))
          (bits4_sigma_bool_equiv (x ↦ bits4_row_stab (bits4_orbit_index x) (bits4_index g)))))
      (sigma_pullback_equiv (USym c4bits_group) Bits4Pos bits4_index_equiv (k ↦ Fin (bits4_fixed_count k)))

{` Sum over Fin 4 by four steps. `}
def bits4_arithmetic_sum_four (f : Bits4Pos → Nat)
  : Id Nat (arithmetic_sum Bits4Pos (fin_is_finite c4bits_four) f)
      (add (add (add (add zero. (f bits4_p3)) (f bits4_p2)) (f bits4_p1)) (f bits4_p0))
  ≔ let f1 : Fin c4bits_three → Nat ≔ i ↦ f (inl. i) in
    let f2 : Fin two → Nat ≔ i ↦ f1 (inl. i) in
    let f3 : Fin (suc. zero.) → Nat ≔ i ↦ f2 (inl. i) in
    let f4 : Fin zero. → Nat ≔ i ↦ f3 (inl. i) in
    calc
      arithmetic_sum Bits4Pos (fin_is_finite c4bits_four) f
      = add (arithmetic_sum (Fin c4bits_three) (fin_is_finite c4bits_three) f1) (f bits4_p0)
        by arithmetic_sum_step c4bits_three f
      = add (add (arithmetic_sum (Fin two) (fin_is_finite two) f2) (f bits4_p1)) (f bits4_p0)
        by refl ((n ↦ add n (f bits4_p0)) : Nat → Nat) (arithmetic_sum_step two f1)
      = add (add (add (arithmetic_sum (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) f3) (f bits4_p2)) (f bits4_p1)) (f bits4_p0)
        by refl ((n ↦ add (add n (f bits4_p1)) (f bits4_p0)) : Nat → Nat) (arithmetic_sum_step (suc. zero.) f2)
      = add (add (add (add (arithmetic_sum (Fin zero.) (fin_is_finite zero.) f4) (f bits4_p3)) (f bits4_p2)) (f bits4_p1)) (f bits4_p0)
        by refl ((n ↦ add (add (add n (f bits4_p2)) (f bits4_p1)) (f bits4_p0)) : Nat → Nat) (arithmetic_sum_step zero. f3)
      = add (add (add (add zero. (f bits4_p3)) (f bits4_p2)) (f bits4_p1)) (f bits4_p0)
        by refl ((n ↦ add (add (add (add n (f bits4_p3)) (f bits4_p2)) (f bits4_p1)) (f bits4_p0)) : Nat → Nat)
             (arithmetic_sum_empty f4) ∎

def bits4_fixed_pairs_finite : IsFinite (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g))
  ≔ finite_of_equiv (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)) (Σ Bits4Pos (k ↦ Fin (bits4_fixed_count k)))
      bits4_fixed_pairs_equiv
      (finite_sigma Bits4Pos (fin_is_finite c4bits_four) (k ↦ Fin (bits4_fixed_count k)) (k ↦ fin_is_finite (bits4_fixed_count k)))

{` "there are in total 24 pairs (g, x) with g · x = x" (24 = 6 × 4). `}
def bits4_fixed_pairs_card (h : IsFinite (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)))
  : Id Nat (cardinality (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)) h) (mul c4bits_six c4bits_four)
  ≔ concat Nat (cardinality (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)) h)
      (arithmetic_sum Bits4Pos (fin_is_finite c4bits_four) bits4_fixed_count) (mul c4bits_six c4bits_four)
      (cardinality_equiv (Σ (USym c4bits_group) (g ↦ FixedBy c4bits_group bits4_gset g)) (Σ Bits4Pos (k ↦ Fin (bits4_fixed_count k)))
        bits4_fixed_pairs_equiv h
        (finite_sigma Bits4Pos (fin_is_finite c4bits_four) (k ↦ Fin (bits4_fixed_count k)) (k ↦ fin_is_finite (bits4_fixed_count k))))
      (bits4_arithmetic_sum_four bits4_fixed_count)

{` Litmus: 0101 is stabilized by r_2 but not by r_1; its stabilizer has 2 symmetries. `}
def bits4_litmus_0101_r2
  : Id Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry bits4_p2) (bits4_mk bits4_o bits4_l bits4_o bits4_l))
      (bits4_mk bits4_o bits4_l bits4_o bits4_l)
  ≔ concat Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry bits4_p2) (bits4_mk bits4_o bits4_l bits4_o bits4_l))
      (bits4_rot bits4_p2 (bits4_mk bits4_o bits4_l bits4_o bits4_l)) (bits4_mk bits4_o bits4_l bits4_o bits4_l)
      (bits4_symmetry_act bits4_p2 (bits4_mk bits4_o bits4_l bits4_o bits4_l))
      (bits4_eqb_sound (bits4_rot bits4_p2 (bits4_mk bits4_o bits4_l bits4_o bits4_l)) (bits4_mk bits4_o bits4_l bits4_o bits4_l)
        (refl (true. : Bool)))

def bits4_litmus_0101_card
  : Id Nat (bits4_row_stab_card (bits4_orbit_index (bits4_mk bits4_o bits4_l bits4_o bits4_l))) two
  ≔ refl two
