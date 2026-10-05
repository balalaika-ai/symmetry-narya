export "589-c4-bit-fixed-free"
export "1011-cyclic-group-homs"
export "1012-finite-group-orders"
export "1021-lagrange-counting"
export "1002-prime-numbers-euclid"

{` Chapter 5, xca:fixed-free-neither (third item, row 4): for
   f = 0101 and f = 1010 in the C_4-set of 4-bit sequences, the stabilizer
   group (C_4)_f is C_2, as an identification of groups
   (C_4)_f = cyclic_group_fin 1, hence BG_f = BC_2 as pointed types.

   General step (ord2_group_path): every group G with an equivalence
   USym G ≃ Fin 2 is identified with C_2. The non-unit symmetry g (the
   preimage of the other element of Fin 2) satisfies g ≠ e and g² = e
   (g·g ≠ g by cancellation, so g·g is the remaining element e). Hence g
   generates a cyclic subgroup with underlying group C_2 (chapter 10,
   cyclic_prime_subgroup_group_path), which has the order of G and so is
   the full subgroup (lagrange_counting_equal_order). This is the argument
   of prime_order_group_cyclic (module 1006) with an explicit generator
   instead of Cauchy's theorem, so the identification is not merely
   asserted. `}

def ord2_swap_ne (k : Fin two) (p : Id (Fin two) (fin2_swap k) k) : Empty
  ≔ match k [
  | inr. u ↦ transport (Fin two) fin2_code (inr. u) (inl. (inr. u)) (inverse (Fin two) (inl. (inr. u)) (inr. u) p) star.
  | inl. (inr. u) ↦ transport (Fin two) fin2_code (inr. u) (inl. (inr. u)) p star.
  | inl. (inl. e) ↦ match e [] ]

{` The non-unit symmetry of a group with two symmetries. `}
def ord2_generator (G : Group) (e : Equiv (USym G) (Fin two)) : USym G
  ≔ equiv_inverse_map (USym G) (Fin two) e (fin2_swap (e .map (usym_unit G)))

def ord2_generator_value (G : Group) (e : Equiv (USym G) (Fin two))
  : Id (Fin two) (e .map (ord2_generator G e)) (fin2_swap (e .map (usym_unit G)))
  ≔ equiv_counit (USym G) (Fin two) e (fin2_swap (e .map (usym_unit G)))

def ord2_generator_ne (G : Group) (e : Equiv (USym G) (Fin two))
  (p : Id (USym G) (ord2_generator G e) (usym_unit G)) : Empty
  ≔ ord2_swap_ne (e .map (usym_unit G))
      (concat (Fin two) (fin2_swap (e .map (usym_unit G))) (e .map (ord2_generator G e)) (e .map (usym_unit G))
        (inverse (Fin two) (e .map (ord2_generator G e)) (fin2_swap (e .map (usym_unit G))) (ord2_generator_value G e))
        (refl (e .map) p))

{` g · g ≠ g. `}
def ord2_square_ne (G : Group) (e : Equiv (USym G) (Fin two))
  (p : Id (USym G) (usym_mul G (ord2_generator G e) (ord2_generator G e)) (ord2_generator G e)) : Empty
  ≔ let A ≔ BG G .carrier in
    let s ≔ shape G in
    let g ≔ ord2_generator G e in
    ord2_generator_ne G e
      (concat_cancel_right A s s s g (refl s) g
        (concat (Id A s s) (concat A s s s g g) g (concat A s s s (refl s) g) p
          (inverse (Id A s s) (concat A s s s (refl s) g) g (concat_1p A s s g))))

def ord2_square_unit (G : Group) (e : Equiv (USym G) (Fin two))
  : Id (USym G) (usym_power G (ord2_generator G e) two) (usym_unit G)
  ≔ let U ≔ USym G in
    let g ≔ ord2_generator G e in
    let u ≔ usym_unit G in
    let m ≔ usym_mul G g g in
    let em : Id (Fin two) (e .map m) (fin2_swap (e .map g))
      ≔ fin2_distinct_other (e .map g) (e .map m)
          (q ↦ ord2_square_ne G e (equivalence_injective U (Fin two) e m g (inverse (Fin two) (e .map g) (e .map m) q))) in
    let eu : Id (Fin two) (e .map u) (fin2_swap (e .map g))
      ≔ fin2_distinct_other (e .map g) (e .map u)
          (q ↦ ord2_generator_ne G e (equivalence_injective U (Fin two) e g u q)) in
    concat U (usym_power G g two) m u
      (refl (usym_mul G g) (usym_power_one G g))
      (equivalence_injective U (Fin two) e m u
        (concat (Fin two) (e .map m) (fin2_swap (e .map g)) (e .map u) em
          (inverse (Fin two) (e .map u) (fin2_swap (e .map g)) eu)))

{` A group with exactly two symmetries is C_2. `}
def ord2_group_path (G : Group) (e : Equiv (USym G) (Fin two)) : Id Group G (cyclic_group two)
  ≔ let C ≔ cyclic_group two in
    let g ≔ ord2_generator G e in
    let S ≔ cyclic_prime_subgroup (suc. zero.) nat_prime_two G g (ord2_square_unit G e) (ord2_generator_ne G e) in
    let pS : Id Group (subgroup_group G S) C
      ≔ cyclic_prime_subgroup_group_path (suc. zero.) nat_prime_two G g (ord2_square_unit G e) (ord2_generator_ne G e) in
    let hG : IsFiniteGroup G ≔ finite_from_equiv (USym G) two e in
    let hc : Id Nat (group_card G hG) two ≔ cardinality_from_path (USym G) hG two (ua (USym G) (Fin two) e) in
    let hC ≔ cyclic_group_finite (suc. zero.) in
    let hS ≔ group_finite_path C (subgroup_group G S) (inverse Group (subgroup_group G S) C pS) hC in
    let cS : Id Nat (group_card (subgroup_group G S) hS) (group_card G hG)
      ≔ concat Nat (group_card (subgroup_group G S) hS) two (group_card G hG)
          (concat Nat (group_card (subgroup_group G S) hS) (group_card C hC) two
            (group_card_path (subgroup_group G S) C pS hS hC)
            (cyclic_group_card (suc. zero.) hC))
          (inverse Nat (group_card G hG) two hc) in
    let full : Id (Subgroups G) S (group_full_subgroup G) ≔ lagrange_counting_equal_order G hG S hS cS in
    concat Group G (subgroup_group G (group_full_subgroup G)) C
      (inverse Group (subgroup_group G (group_full_subgroup G)) G
        (mono_subgroup_group_path G (G, (group_hom_id G, group_hom_id_mono G))))
      (concat Group (subgroup_group G (group_full_subgroup G)) (subgroup_group G S) C
        (refl ((T ↦ subgroup_group G T) : Subgroups G → Group) (inverse (Subgroups G) S (group_full_subgroup G) full))
        pS)

{` xca:fixed-free-neither, row 4: (C_4)_f = C_2 for f in the orbit {0101, 1010}. `}
def bits4_neither_stabilizer_group_path (x : Bits4) (h : Id (Fin c4bits_six) (bits4_orbit_index x) bits4_r4)
  : Id Group (stabilizer_group c4bits_group bits4_gset x) (cyclic_group_fin (suc. zero.))
  ≔ concat Group (stabilizer_group c4bits_group bits4_gset x) (cyclic_group two) (cyclic_group_fin (suc. zero.))
      (ord2_group_path (stabilizer_group c4bits_group bits4_gset x) (bits4_neither_stabilizer_usym_equiv x h))
      (inverse Group (cyclic_group_fin (suc. zero.)) (cyclic_group two) (cyclic_group_fin_path (suc. zero.)))

{` BG_f = BC_2 as pointed types, and BG_f ≃ BC_2. `}
def bits4_neither_classifying_path (x : Bits4) (h : Id (Fin c4bits_six) (bits4_orbit_index x) bits4_r4)
  : Id Pointed (BG (stabilizer_group c4bits_group bits4_gset x)) (BG (cyclic_group_fin (suc. zero.)))
  ≔ group_path_pointed_equiv (stabilizer_group c4bits_group bits4_gset x) (cyclic_group_fin (suc. zero.))
      .map (bits4_neither_stabilizer_group_path x h)

def bits4_neither_classifying_equiv (x : Bits4) (h : Id (Fin c4bits_six) (bits4_orbit_index x) bits4_r4)
  : Equiv (BG (stabilizer_group c4bits_group bits4_gset x) .carrier) (BG (cyclic_group_fin (suc. zero.)) .carrier)
  ≔ id_to_equiv (BG (stabilizer_group c4bits_group bits4_gset x) .carrier) (BG (cyclic_group_fin (suc. zero.)) .carrier)
      (refl ((X ↦ X .carrier) : Pointed → Type) (bits4_neither_classifying_path x h))

def bits4_c0101_stabilizer_group_path
  : Id Group (stabilizer_group c4bits_group bits4_gset bits4_c0101) (cyclic_group_fin (suc. zero.))
  ≔ bits4_neither_stabilizer_group_path bits4_c0101 (refl bits4_r4)

def bits4_c1010_stabilizer_group_path
  : Id Group (stabilizer_group c4bits_group bits4_gset bits4_c1010) (cyclic_group_fin (suc. zero.))
  ≔ bits4_neither_stabilizer_group_path bits4_c1010 (refl bits4_r4)

def bits4_c0101_classifying_path
  : Id Pointed (BG (stabilizer_group c4bits_group bits4_gset bits4_c0101)) (BG (cyclic_group_fin (suc. zero.)))
  ≔ bits4_neither_classifying_path bits4_c0101 (refl bits4_r4)

def bits4_c1010_classifying_path
  : Id Pointed (BG (stabilizer_group c4bits_group bits4_gset bits4_c1010)) (BG (cyclic_group_fin (suc. zero.)))
  ≔ bits4_neither_classifying_path bits4_c1010 (refl bits4_r4)

{` Litmus: Σ_2 (two symmetries) is C_2 by the general step. `}
def ord2_sigma2_litmus : Id Group (symmetric_group two) (cyclic_group two)
  ≔ ord2_group_path (symmetric_group two) sigma2_usym_equiv
