export "588-c4-bit-stabilizers"

{` exa:fixed-free-neither, xca:fixed-free-neither and
   xca:fixed-free-neither-action-types.

   Trivial and principal G-sets: every s : S is fixed under triv_G S
   (trivial_gset_fixed, core 505) and every g : USym G is free under P_G
   (principal_gset_free, core 505). Here: the C_4 part. In the C_4-set of
   binary sequences of length 4, the fixed elements are 0000 and 1111
   (bits4_fixed_elements), the free elements are those with x ∘ rot_2 ≠ x,
   i.e. the twelve elements of rows 2, 3, 5 (bits4_free_elements), and the
   elements that are neither are 0101 and 1010 (bits4_neither_elements).

   xca:fixed-free-neither: BG_s ≃ BG via i_s for triv_G S; BG_g is
   contractible for P_G; for the C_4 example BG_f ≃ BC_4 (via i_f) for f fixed,
   BG_f is contractible for f free, and USym(C_4)_f ≃ Fin 2 (the symmetries
   r_0, r_2) for f = 0101, 1010.

   xca:fixed-free-neither-action-types: (G̃_x)_{hG_x} ≃ G · x
   (orbit_stabilizer_equiv, module 525), which is contractible for triv_G S,
   ≃ USym G for P_G, and has 1, 4 or 2 elements for the C_4 example. `}

{` b ≠ true iff not b = true. `}
def bits4_not_true (b : Bool)
  : Product (Not (Id Bool b true.) → Id Bool (bool_not b) true.) (Id Bool (bool_not b) true. → Not (Id Bool b true.))
  ≔ match b [
  | false. ↦ (_ ↦ refl (true. : Bool), _ h ↦ bool_encode false. true. h)
  | true. ↦ (n ↦ absurd (Id Bool false. true.) (n (refl (true. : Bool))), e _ ↦ bool_encode false. true. e) ]

{` Pointwise consequence of a Boolean check P = Q over all sequences. `}
def bits4_check_point (P Q : Bits4 → Bool) (h : Id Bool (bits4_all (x ↦ bits4_bool_eqb (P x) (Q x))) true.) (x : Bits4)
  : Id Bool (P x) (Q x)
  ≔ bits4_bool_eqb_sound (P x) (Q x) (bits4_all_sound (y ↦ bits4_bool_eqb (P y) (Q y)) h x)

def bits4_c0000 : Bits4 ≔ bits4_mk bits4_o bits4_o bits4_o bits4_o
def bits4_c1111 : Bits4 ≔ bits4_mk bits4_l bits4_l bits4_l bits4_l
def bits4_c0101 : Bits4 ≔ bits4_mk bits4_o bits4_l bits4_o bits4_l
def bits4_c1010 : Bits4 ≔ bits4_mk bits4_l bits4_o bits4_l bits4_o

{` Rows whose elements are fixed (all four symmetries stabilize). `}
def bits4_row_fixed (r : Fin c4bits_six) : Bool ≔ bits4_pos_all (bits4_row_stab r)

{` Rows whose elements are free. `}
def bits4_row_free (r : Fin c4bits_six) : Bool
  ≔ bits4_row_ind (_ ↦ Bool) false. false. true. true. false. true. r

{` x is fixed iff its row is fixed. `}
def bits4_fixed_row_equiv (x : Bits4)
  : Equiv (IsFixedElement c4bits_group bits4_gset x) (Id Bool (bits4_row_fixed (bits4_orbit_index x)) true.)
  ≔ let r ≔ bits4_orbit_index x in
    let F ≔ (g : USym c4bits_group) → Id Bits4 x (gset_usym_act c4bits_group bits4_gset g x) in
    iff_equiv (IsFixedElement c4bits_group bits4_gset x) (Id Bool (bits4_row_fixed r) true.)
      (is_fixed_element_prop c4bits_group bits4_gset x) (bool_set (bits4_row_fixed r) true.)
      (h ↦ bits4_fin_all_complete c4bits_four (bits4_row_stab r)
        (k ↦ transport Bits4Pos (k' ↦ Id Bool (bits4_row_stab r k') true.) (bits4_index (bits4_symmetry k)) k
          (bits4_symmetry_index k)
          (bits4_stabilizes_equiv (bits4_symmetry k) x .map
            (inverse Bits4 x (gset_usym_act c4bits_group bits4_gset (bits4_symmetry k) x)
              (fixed_element_fixed_by_all c4bits_group bits4_gset x .map h (bits4_symmetry k))))))
      (e ↦ equiv_inverse_map (IsFixedElement c4bits_group bits4_gset x) F (fixed_element_fixed_by_all c4bits_group bits4_gset x)
        (g ↦ inverse Bits4 (gset_usym_act c4bits_group bits4_gset g x) x
          (equiv_inverse_map (Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) x)
            (Id Bool (bits4_row_stab r (bits4_index g)) true.) (bits4_stabilizes_equiv g x)
            (bits4_fin_all_sound c4bits_four (bits4_row_stab r) e (bits4_index g)))))

def bits4_fin_one_contr : BookIsContr (Fin (suc. zero.))
  ≔ (inr. star., [ inr. star. ↦ refl (inr. star. : Fin (suc. zero.)) | inl. e ↦ match e [] ])

def bits4_fin_big_not_contr (n : Nat) (c : BookIsContr (Fin (suc. (suc. n)))) : Empty
  ≔ sum_encode (Fin (suc. n)) Unit (inr. star.) (inl. (inr. star.))
      (concat (Fin (suc. (suc. n))) (inr. star.) (c .center) (inl. (inr. star.))
        (inverse (Fin (suc. (suc. n))) (c .center) (inr. star.) (c .contract (inr. star.)))
        (c .contract (inl. (inr. star.))))

def bits4_row_free_contr (r : Fin c4bits_six)
  : Product (BookIsContr (Fin (bits4_row_stab_card r)) → Id Bool (bits4_row_free r) true.)
      (Id Bool (bits4_row_free r) true. → BookIsContr (Fin (bits4_row_stab_card r)))
  ≔ bits4_row_ind (r' ↦ Product (BookIsContr (Fin (bits4_row_stab_card r')) → Id Bool (bits4_row_free r') true.)
        (Id Bool (bits4_row_free r') true. → BookIsContr (Fin (bits4_row_stab_card r'))))
      (c ↦ absurd (Id Bool false. true.) (bits4_fin_big_not_contr two c),
       e ↦ absurd (BookIsContr (Fin c4bits_four)) (bool_encode false. true. e))
      (c ↦ absurd (Id Bool false. true.) (bits4_fin_big_not_contr two c),
       e ↦ absurd (BookIsContr (Fin c4bits_four)) (bool_encode false. true. e))
      (_ ↦ refl (true. : Bool), _ ↦ bits4_fin_one_contr)
      (_ ↦ refl (true. : Bool), _ ↦ bits4_fin_one_contr)
      (c ↦ absurd (Id Bool false. true.) (bits4_fin_big_not_contr zero. c),
       e ↦ absurd (BookIsContr (Fin two)) (bool_encode false. true. e))
      (_ ↦ refl (true. : Bool), _ ↦ bits4_fin_one_contr) r

{` x is free iff its row is free. `}
def bits4_free_row_equiv (x : Bits4)
  : Equiv (IsFreeElement c4bits_group bits4_gset x) (Id Bool (bits4_row_free (bits4_orbit_index x)) true.)
  ≔ let r ≔ bits4_orbit_index x in
    let H ≔ stabilizer_group c4bits_group bits4_gset x in
    let E ≔ book_contractibility_equiv (USym H) (Fin (bits4_row_stab_card r)) (bits4_stabilizer_usym_equiv x) in
    iff_equiv (IsFreeElement c4bits_group bits4_gset x) (Id Bool (bits4_row_free r) true.)
      (is_free_element_prop c4bits_group bits4_gset x) (bool_set (bits4_row_free r) true.)
      (h ↦ bits4_row_free_contr r .fst (E .map (orbit_trivial_group_usym_contractible H h)))
      (e ↦ orbit_usym_contractible_trivial_group H
        (equiv_inverse_map (BookIsContr (USym H)) (BookIsContr (Fin (bits4_row_stab_card r))) E (bits4_row_free_contr r .snd e)))

{` Boolean descriptions of the three cases, checked on all 16 sequences. `}
def bits4_fixed_list_check
  : Id Bool (bits4_all (x ↦ bits4_bool_eqb (bits4_row_fixed (bits4_orbit_index x))
      (bits4_or (bits4_eqb x bits4_c0000) (bits4_eqb x bits4_c1111)))) true.
  ≔ refl (true. : Bool)

def bits4_free_list_check
  : Id Bool (bits4_all (x ↦ bits4_bool_eqb (bits4_row_free (bits4_orbit_index x))
      (bool_not (bits4_stab_bool x bits4_p2)))) true.
  ≔ refl (true. : Bool)

def bits4_neither_list_check
  : Id Bool (bits4_all (x ↦ bits4_bool_eqb
      (bits4_and (bool_not (bits4_row_fixed (bits4_orbit_index x))) (bool_not (bits4_row_free (bits4_orbit_index x))))
      (bits4_or (bits4_eqb x bits4_c0101) (bits4_eqb x bits4_c1010)))) true.
  ≔ refl (true. : Bool)

{` exa:fixed-free-neither (C_4 part): the fixed elements are 0000 and 1111. `}
def bits4_fixed_elements (x : Bits4)
  : Product (IsFixedElement c4bits_group bits4_gset x → Sum (Id Bits4 x bits4_c0000) (Id Bits4 x bits4_c1111))
      (Sum (Id Bits4 x bits4_c0000) (Id Bits4 x bits4_c1111) → IsFixedElement c4bits_group bits4_gset x)
  ≔ let P : Bits4 → Bool ≔ y ↦ bits4_row_fixed (bits4_orbit_index y) in
    let Q : Bits4 → Bool ≔ y ↦ bits4_or (bits4_eqb y bits4_c0000) (bits4_eqb y bits4_c1111) in
    let pt ≔ bits4_check_point P Q bits4_fixed_list_check x in
    (h ↦ match bits4_or_elim (bits4_eqb x bits4_c0000) (bits4_eqb x bits4_c1111)
          (concat Bool (Q x) (P x) true. (inverse Bool (P x) (Q x) pt) (bits4_fixed_row_equiv x .map h)) [
        | inl. a ↦ inl. (bits4_eqb_sound x bits4_c0000 a)
        | inr. b ↦ inr. (bits4_eqb_sound x bits4_c1111 b) ],
     s ↦ equiv_inverse_map (IsFixedElement c4bits_group bits4_gset x) (Id Bool (P x) true.) (bits4_fixed_row_equiv x)
          (concat Bool (P x) (Q x) true. pt (match s [
            | inl. p ↦ bits4_or_left (bits4_eqb x bits4_c0000) (bits4_eqb x bits4_c1111) (bits4_eqb_complete x bits4_c0000 p)
            | inr. p ↦ bits4_or_right (bits4_eqb x bits4_c0000) (bits4_eqb x bits4_c1111) (bits4_eqb_complete x bits4_c1111 p) ])))

{` exa:fixed-free-neither (C_4 part): x is free iff rotating by two positions
   moves it (rows 2, 3, 5: twelve elements). `}
def bits4_free_elements (x : Bits4)
  : Product (IsFreeElement c4bits_group bits4_gset x → Not (Id Bits4 (bits4_rot bits4_p2 x) x))
      (Not (Id Bits4 (bits4_rot bits4_p2 x) x) → IsFreeElement c4bits_group bits4_gset x)
  ≔ let P : Bits4 → Bool ≔ y ↦ bits4_row_free (bits4_orbit_index y) in
    let Q : Bits4 → Bool ≔ y ↦ bool_not (bits4_stab_bool y bits4_p2) in
    let pt ≔ bits4_check_point P Q bits4_free_list_check x in
    (h q ↦ bits4_not_true (bits4_stab_bool x bits4_p2) .snd
        (concat Bool (Q x) (P x) true. (inverse Bool (P x) (Q x) pt) (bits4_free_row_equiv x .map h))
        (bits4_eqb_complete (bits4_rot bits4_p2 x) x q),
     n ↦ equiv_inverse_map (IsFreeElement c4bits_group bits4_gset x) (Id Bool (P x) true.) (bits4_free_row_equiv x)
        (concat Bool (P x) (Q x) true. pt
          (bits4_not_true (bits4_stab_bool x bits4_p2) .fst (e ↦ n (bits4_eqb_sound (bits4_rot bits4_p2 x) x e)))))

{` exa:fixed-free-neither (C_4 part): the elements that are neither fixed nor
   free are 0101 and 1010. `}
def bits4_neither_elements (x : Bits4)
  : Product (Product (Not (IsFixedElement c4bits_group bits4_gset x)) (Not (IsFreeElement c4bits_group bits4_gset x))
        → Sum (Id Bits4 x bits4_c0101) (Id Bits4 x bits4_c1010))
      (Sum (Id Bits4 x bits4_c0101) (Id Bits4 x bits4_c1010)
        → Product (Not (IsFixedElement c4bits_group bits4_gset x)) (Not (IsFreeElement c4bits_group bits4_gset x)))
  ≔ let a ≔ bits4_row_fixed (bits4_orbit_index x) in
    let b ≔ bits4_row_free (bits4_orbit_index x) in
    let P : Bits4 → Bool ≔ y ↦ bits4_and (bool_not (bits4_row_fixed (bits4_orbit_index y))) (bool_not (bits4_row_free (bits4_orbit_index y))) in
    let Q : Bits4 → Bool ≔ y ↦ bits4_or (bits4_eqb y bits4_c0101) (bits4_eqb y bits4_c1010) in
    let pt ≔ bits4_check_point P Q bits4_neither_list_check x in
    (u ↦ match bits4_or_elim (bits4_eqb x bits4_c0101) (bits4_eqb x bits4_c1010)
          (concat Bool (Q x) (P x) true. (inverse Bool (P x) (Q x) pt)
            (bits4_and_intro (bool_not a) (bool_not b)
              (bits4_not_true a .fst (e ↦ u .fst (equiv_inverse_map (IsFixedElement c4bits_group bits4_gset x) (Id Bool a true.)
                (bits4_fixed_row_equiv x) e)))
              (bits4_not_true b .fst (e ↦ u .snd (equiv_inverse_map (IsFreeElement c4bits_group bits4_gset x) (Id Bool b true.)
                (bits4_free_row_equiv x) e))))) [
        | inl. p ↦ inl. (bits4_eqb_sound x bits4_c0101 p)
        | inr. p ↦ inr. (bits4_eqb_sound x bits4_c1010 p) ],
     s ↦ let ab : Id Bool (P x) true.
           ≔ concat Bool (P x) (Q x) true. pt (match s [
               | inl. p ↦ bits4_or_left (bits4_eqb x bits4_c0101) (bits4_eqb x bits4_c1010) (bits4_eqb_complete x bits4_c0101 p)
               | inr. p ↦ bits4_or_right (bits4_eqb x bits4_c0101) (bits4_eqb x bits4_c1010) (bits4_eqb_complete x bits4_c1010 p) ]) in
         (h ↦ bits4_not_true a .snd (bits4_and_left (bool_not a) (bool_not b) ab) (bits4_fixed_row_equiv x .map h),
          h ↦ bits4_not_true b .snd (bits4_and_right (bool_not a) (bool_not b) ab) (bits4_free_row_equiv x .map h)))

{` xca:fixed-free-neither, first item: BG_s ≃ BG via i_s for the trivial G-set. `}
def fixed_free_trivial_classifying_equiv (G : Group) (S : SetTypes) (s : S .fst)
  : BookEquiv (BG (stabilizer_group G (gset_trivial G S) s) .carrier) (BG G .carrier)
  ≔ (hom_function (stabilizer_group G (gset_trivial G S) s) G (stabilizer_inclusion G (gset_trivial G S) s),
     trivial_gset_fixed G S s)

{` xca:fixed-free-neither, second item: BG_g is contractible for P_G. `}
def fixed_free_principal_classifying_contr (G : Group) (g : USym G)
  : BookIsContr (BG (stabilizer_group G (principal_gset G) g) .carrier)
  ≔ principal_gset_free G g

{` xca:fixed-free-neither, third item (C_4 example): BG_f ≃ BC_4 via i_f in
   rows 0, 1; BG_f contractible in rows 2, 3, 5; USym (C_4)_f ≃ Fin 2 in row 4. `}
def bits4_fixed_classifying_equiv (x : Bits4) (h : Id Bool (bits4_row_fixed (bits4_orbit_index x)) true.)
  : BookEquiv (BG (stabilizer_group c4bits_group bits4_gset x) .carrier) (BG c4bits_group .carrier)
  ≔ (hom_function (stabilizer_group c4bits_group bits4_gset x) c4bits_group (stabilizer_inclusion c4bits_group bits4_gset x),
     equiv_inverse_map (IsFixedElement c4bits_group bits4_gset x) (Id Bool (bits4_row_fixed (bits4_orbit_index x)) true.)
       (bits4_fixed_row_equiv x) h)

def bits4_free_classifying_contr (x : Bits4) (h : Id Bool (bits4_row_free (bits4_orbit_index x)) true.)
  : BookIsContr (BG (stabilizer_group c4bits_group bits4_gset x) .carrier)
  ≔ equiv_inverse_map (IsFreeElement c4bits_group bits4_gset x) (Id Bool (bits4_row_free (bits4_orbit_index x)) true.)
      (bits4_free_row_equiv x) h

def bits4_neither_stabilizer_usym_equiv (x : Bits4) (h : Id (Fin c4bits_six) (bits4_orbit_index x) bits4_r4)
  : Equiv (USym (stabilizer_group c4bits_group bits4_gset x)) (Fin two)
  ≔ compose_equiv (USym (stabilizer_group c4bits_group bits4_gset x)) (Fin (bits4_row_stab_card (bits4_orbit_index x))) (Fin two)
      (bits4_stabilizer_usym_equiv x)
      (transport_equiv (Fin (bits4_row_stab_card (bits4_orbit_index x))) (Fin two)
        (refl Fin (refl bits4_row_stab_card h)))

{` xca:fixed-free-neither-action-types, first item: (G̃_s)_{hG_s} is contractible
   (as is G · s). `}
def fixed_free_trivial_action_type_contr (G : Group) (S : SetTypes) (s : S .fst)
  : BookIsContr (ActionType (stabilizer_group G (gset_trivial G S) s) (stabilizer_tilde_gset G (gset_trivial G S) s))
  ≔ equiv_inverse_map
      (BookIsContr (ActionType (stabilizer_group G (gset_trivial G S) s) (stabilizer_tilde_gset G (gset_trivial G S) s)))
      (BookIsContr (OrbitUnderlying G (gset_trivial G S) s))
      (book_contractibility_equiv
        (ActionType (stabilizer_group G (gset_trivial G S) s) (stabilizer_tilde_gset G (gset_trivial G S) s))
        (OrbitUnderlying G (gset_trivial G S) s) (orbit_stabilizer_equiv G (gset_trivial G S) s))
      (fixed_element_orbit_contractible G (gset_trivial G S) s .map (trivial_gset_fixed G S s))

{` Second item: (G̃_g)_{hG_g} ≃ G · g ≃ USym G. `}
def fixed_free_principal_action_type_equiv (G : Group) (g : USym G)
  : Equiv (ActionType (stabilizer_group G (principal_gset G) g) (stabilizer_tilde_gset G (principal_gset G) g)) (USym G)
  ≔ compose_equiv (ActionType (stabilizer_group G (principal_gset G) g) (stabilizer_tilde_gset G (principal_gset G) g))
      (OrbitUnderlying G (principal_gset G) g) (USym G)
      (orbit_stabilizer_equiv G (principal_gset G) g)
      (canonical_inverse_equiv (USym G) (OrbitUnderlying G (principal_gset G) g)
        (native_equivalence (USym G) (OrbitUnderlying G (principal_gset G) g)
          (free_orbit_action_equiv G (principal_gset G) g (principal_gset_free G g))))

{` Third item: (G̃_f)_{hG_f} ≃ C_4 · f, which has 1, 1, 4, 4, 2, 4 elements by row. `}
def bits4_stabilizer_action_type_equiv (x : Bits4)
  : Equiv (ActionType (stabilizer_group c4bits_group bits4_gset x) (stabilizer_tilde_gset c4bits_group bits4_gset x))
      (Fin (bits4_row_size (bits4_orbit_index x)))
  ≔ compose_equiv (ActionType (stabilizer_group c4bits_group bits4_gset x) (stabilizer_tilde_gset c4bits_group bits4_gset x))
      (OrbitUnderlying c4bits_group bits4_gset x) (Fin (bits4_row_size (bits4_orbit_index x)))
      (orbit_stabilizer_equiv c4bits_group bits4_gset x) (bits4_orbit_underlying_equiv x)

{` Litmus: 0000 is fixed, 0001 is free, 0101 is neither. `}
def bits4_litmus_0000_fixed : IsFixedElement c4bits_group bits4_gset bits4_c0000
  ≔ bits4_fixed_elements bits4_c0000 .snd (inl. (refl bits4_c0000))

def bits4_litmus_0001_free : IsFreeElement c4bits_group bits4_gset (bits4_mk bits4_o bits4_o bits4_o bits4_l)
  ≔ equiv_inverse_map (IsFreeElement c4bits_group bits4_gset (bits4_mk bits4_o bits4_o bits4_o bits4_l)) (Id Bool true. true.)
      (bits4_free_row_equiv (bits4_mk bits4_o bits4_o bits4_o bits4_l)) (refl (true. : Bool))

def bits4_litmus_0101_neither
  : Product (Not (IsFixedElement c4bits_group bits4_gset bits4_c0101)) (Not (IsFreeElement c4bits_group bits4_gset bits4_c0101))
  ≔ bits4_neither_elements bits4_c0101 .snd (inl. (refl bits4_c0101))
