export "505-gset-core-litmus"
export "525-orbit-stabilizer"

{` exa:prep-burnside (part 1): the C_4-set of binary sequences of length 4.

   C_4 is the book's literal Aut_Cyc(Fin 4, s) = cyclic_group_fin 3. The
   C_4-set X maps (A, f) : BC_4 to the set A → Fin 2, so its underlying set is
   Fin 4 → Fin 2 (binary sequences x(0) x(1) x(2) x(3)). Positions of Fin 4 are
   0 = inr star, 1 = inl (inr star), ... as in module 406, and the bit 0 of
   Fin 2 is inr star, the bit 1 is inl (inr star).

   Main result (bits4_act_rot): a symmetry g acts on a sequence by cyclic
   rotation, (g · x)(i) = x(i − k) where k : Fin 4 is the image of g under the
   evaluation equivalence USym C_4 ≃ Fin 4 of cor:id-m-cycle
   (cyclic_group_fin_usym_equiv, g ↦ g(0)). The proof follows the footnote of
   the book: cor:id-m-cycle, univalence, and transport in a function type
   (computed natively by HOTT). `}

def c4bits_three : Nat ≔ suc. (suc. (suc. zero.))

def c4bits_four : Nat ≔ suc. c4bits_three

{` C_4 = Aut_Cyc(Fin 4, s). `}
def c4bits_group : Group ≔ cyclic_group_fin c4bits_three

def Bits4Pos : Type ≔ Fin c4bits_four

{` Binary sequences of length 4. `}
def Bits4 : Type ≔ Bits4Pos → Fin two

def bits4_set : isSet Bits4 ≔ pi_set Bits4Pos (_ ↦ Fin two) (_ ↦ fin_set two)

def bits4_p0 : Bits4Pos ≔ inr. star.
def bits4_p1 : Bits4Pos ≔ inl. (inr. star.)
def bits4_p2 : Bits4Pos ≔ inl. (inl. (inr. star.))
def bits4_p3 : Bits4Pos ≔ inl. (inl. (inl. (inr. star.)))

{` The bits 0 and 1. `}
def bits4_o : Fin two ≔ inr. star.
def bits4_l : Fin two ≔ inl. (inr. star.)

{` Case analysis on positions and bits. `}
def bits4_pos_ind (P : Bits4Pos → Type) (h0 : P bits4_p0) (h1 : P bits4_p1) (h2 : P bits4_p2) (h3 : P bits4_p3)
  (i : Bits4Pos) : P i
  ≔ match i [
  | inr. star. ↦ h0
  | inl. (inr. star.) ↦ h1
  | inl. (inl. (inr. star.)) ↦ h2
  | inl. (inl. (inl. (inr. star.))) ↦ h3
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def bits4_bit_ind (P : Fin two → Type) (h0 : P bits4_o) (h1 : P bits4_l) (b : Fin two) : P b
  ≔ match b [
  | inr. star. ↦ h0
  | inl. (inr. star.) ↦ h1
  | inl. (inl. e) ↦ match e [] ]

{` The sequence a b c d. `}
def bits4_mk (a b c d : Fin two) : Bits4
  ≔ i ↦ bits4_pos_ind (_ ↦ Fin two) a b c d i

def bits4_mk_eta (x : Bits4) : Id Bits4 (bits4_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3)) x
  ≔ funext Bits4Pos (_ ↦ Fin two) (bits4_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3)) x
      (bits4_pos_ind (i ↦ Id (Fin two) (bits4_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3) i) (x i))
        (refl (x bits4_p0)) (refl (x bits4_p1)) (refl (x bits4_p2)) (refl (x bits4_p3)))

{` Arithmetic of Z/4 on positions, by explicit tables. `}
def bits4_succ (i : Bits4Pos) : Bits4Pos
  ≔ bits4_pos_ind (_ ↦ Bits4Pos) bits4_p1 bits4_p2 bits4_p3 bits4_p0 i

{` The successor s of the book's cycle (Fin 4, s) is this table. `}
def bits4_succ_agrees (i : Bits4Pos)
  : Id Bits4Pos (finite_fin_successor c4bits_three .map i) (bits4_succ i)
  ≔ bits4_pos_ind (j ↦ Id Bits4Pos (finite_fin_successor c4bits_three .map j) (bits4_succ j))
      (refl bits4_p1) (refl bits4_p2) (refl bits4_p3) (refl bits4_p0) i

{` j + k, by iterating the successor j times on k. `}
def bits4_add (j k : Bits4Pos) : Bits4Pos
  ≔ bits4_pos_ind (_ ↦ Bits4Pos) k (bits4_succ k) (bits4_succ (bits4_succ k))
      (bits4_succ (bits4_succ (bits4_succ k))) j

def bits4_neg (k : Bits4Pos) : Bits4Pos
  ≔ bits4_pos_ind (_ ↦ Bits4Pos) bits4_p0 bits4_p3 bits4_p2 bits4_p1 k

{` i − k. `}
def bits4_sub (i k : Bits4Pos) : Bits4Pos ≔ bits4_add i (bits4_neg k)

def bits4_sub_add (i k : Bits4Pos) : Id Bits4Pos (bits4_add (bits4_sub i k) k) i
  ≔ bits4_pos_ind (i' ↦ (k' : Bits4Pos) → Id Bits4Pos (bits4_add (bits4_sub i' k') k') i')
      (bits4_pos_ind (k' ↦ Id Bits4Pos (bits4_add (bits4_sub bits4_p0 k') k') bits4_p0)
        (refl bits4_p0) (refl bits4_p0) (refl bits4_p0) (refl bits4_p0))
      (bits4_pos_ind (k' ↦ Id Bits4Pos (bits4_add (bits4_sub bits4_p1 k') k') bits4_p1)
        (refl bits4_p1) (refl bits4_p1) (refl bits4_p1) (refl bits4_p1))
      (bits4_pos_ind (k' ↦ Id Bits4Pos (bits4_add (bits4_sub bits4_p2 k') k') bits4_p2)
        (refl bits4_p2) (refl bits4_p2) (refl bits4_p2) (refl bits4_p2))
      (bits4_pos_ind (k' ↦ Id Bits4Pos (bits4_add (bits4_sub bits4_p3 k') k') bits4_p3)
        (refl bits4_p3) (refl bits4_p3) (refl bits4_p3) (refl bits4_p3)) i k

{` Backward transport undoes forward transport along a path of types. `}
def type_path_trl_trr_base (A : Type) (a : A) : Id A (refl A .trl (refl A .trr a)) a
  ≔ concat A (refl A .trl (refl A .trr a)) (refl A .trr a) a (refl A .liftl (refl A .trr a))
      (inverse A a (refl A .trr a) (refl A .liftr a))

def type_path_trl_trr (A B : Type) (e : Id Type A B) (a : A) : Id A (e .trl (e .trr a)) a
  ≔ J Type A (B' e' ↦ (a' : A) → Id A (e' .trl (e' .trr a')) a') (a' ↦ type_path_trl_trr_base A a') B e a

{` def:Gset for exa:prep-burnside: X(A, f) ≔ (A → Fin 2). `}
def bits4_gset : GSet c4bits_group
  ≔ z ↦ (z .fst .fst .fst .fst → Fin two, pi_set (z .fst .fst .fst .fst) (_ ↦ Fin two) (_ ↦ fin_set two))

{` The underlying set of X is Fin 4 → Fin 2 (by definition). `}
def bits4_gset_underlying : Id Type (gset_underlying c4bits_group bits4_gset) Bits4 ≔ refl Bits4

{` The carrier permutation of a symmetry g of (Fin 4, s): transport along
   the underlying path of types. `}
def bits4_carrier (g : USym c4bits_group) (j : Bits4Pos) : Bits4Pos ≔ g .fst .fst .fst .fst .trr j

{` cor:id-m-cycle: g ↦ g(0) is the equivalence USym C_4 ≃ Fin 4. `}
def bits4_index_equiv : Equiv (USym c4bits_group) Bits4Pos ≔ cyclic_group_fin_usym_equiv c4bits_three

def bits4_index (g : USym c4bits_group) : Bits4Pos ≔ bits4_index_equiv .map g

def bits4_index_carrier (g : USym c4bits_group) : Id Bits4Pos (bits4_index g) (bits4_carrier g bits4_p0)
  ≔ refl (bits4_index g)

{` The carrier permutation commutes with the successor. `}
def bits4_carrier_commutes (g : USym c4bits_group) (j : Bits4Pos)
  : Id Bits4Pos (bits4_carrier g (finite_fin_successor c4bits_three .map j))
      (finite_fin_successor c4bits_three .map (bits4_carrier g j))
  ≔ cycle_paths_equiv (finite_fin_cycle c4bits_three) (finite_fin_cycle c4bits_three) .map (g .fst) .snd j

def bits4_carrier_succ (g : USym c4bits_group) (j : Bits4Pos)
  : Id Bits4Pos (bits4_carrier g (bits4_succ j)) (bits4_succ (bits4_carrier g j))
  ≔ calc
      bits4_carrier g (bits4_succ j)
      = bits4_carrier g (finite_fin_successor c4bits_three .map j)
        by refl (bits4_carrier g) (inverse Bits4Pos (finite_fin_successor c4bits_three .map j) (bits4_succ j)
             (bits4_succ_agrees j))
      = finite_fin_successor c4bits_three .map (bits4_carrier g j) by bits4_carrier_commutes g j
      = bits4_succ (bits4_carrier g j) by bits4_succ_agrees (bits4_carrier g j) ∎

{` A symmetry with g(0) = k is rotation by k: g(j) = j + k. `}
def bits4_carrier_add (g : USym c4bits_group) (j : Bits4Pos)
  : Id Bits4Pos (bits4_carrier g j) (bits4_add j (bits4_carrier g bits4_p0))
  ≔ let t ≔ bits4_carrier g in
    let k ≔ t bits4_p0 in
    let e1 : Id Bits4Pos (t bits4_p1) (bits4_succ k) ≔ bits4_carrier_succ g bits4_p0 in
    let e2 : Id Bits4Pos (t bits4_p2) (bits4_succ (bits4_succ k))
      ≔ concat Bits4Pos (t bits4_p2) (bits4_succ (t bits4_p1)) (bits4_succ (bits4_succ k))
          (bits4_carrier_succ g bits4_p1) (refl bits4_succ e1) in
    let e3 : Id Bits4Pos (t bits4_p3) (bits4_succ (bits4_succ (bits4_succ k)))
      ≔ concat Bits4Pos (t bits4_p3) (bits4_succ (t bits4_p2)) (bits4_succ (bits4_succ (bits4_succ k)))
          (bits4_carrier_succ g bits4_p2) (refl bits4_succ e2) in
    bits4_pos_ind (j' ↦ Id Bits4Pos (t j') (bits4_add j' k)) (refl k) e1 e2 e3 j

{` The inverse permutation (backward transport) is rotation by −k. `}
def bits4_carrier_inverse (g : USym c4bits_group) (i : Bits4Pos)
  : Id Bits4Pos (g .fst .fst .fst .fst .trl i) (bits4_sub i (bits4_index g))
  ≔ let e ≔ g .fst .fst .fst .fst in
    let k ≔ bits4_index g in
    let j ≔ bits4_sub i k in
    calc
      e .trl i
      = e .trl (bits4_add j k) by refl ((y ↦ e .trl y) : Bits4Pos → Bits4Pos) (inverse Bits4Pos (bits4_add j k) i (bits4_sub_add i k))
      = e .trl (e .trr j) by refl ((y ↦ e .trl y) : Bits4Pos → Bits4Pos)
           (inverse Bits4Pos (bits4_carrier g j) (bits4_add j k) (bits4_carrier_add g j))
      = j by type_path_trl_trr Bits4Pos Bits4Pos e j ∎

{` Rotation of a sequence by k positions: (rot_k x)(i) = x(i − k). `}
def bits4_rot (k : Bits4Pos) (x : Bits4) : Bits4 ≔ i ↦ x (bits4_sub i k)

{` Transport in the function-type family, computed natively. `}
def bits4_act_pointwise (g : USym c4bits_group) (x : Bits4) (i : Bits4Pos)
  : Id (Fin two) (gset_usym_act c4bits_group bits4_gset g x i) (x (g .fst .fst .fst .fst .trl i))
  ≔ inverse (Fin two) (x (g .fst .fst .fst .fst .trl i)) (refl (Fin two) .trr (x (g .fst .fst .fst .fst .trl i)))
      (refl (Fin two) .liftr (x (g .fst .fst .fst .fst .trl i)))

{` exa:prep-burnside: "the group action induced by X cyclically rotates
   such sequences": g · x = rot_k x with k = g(0). `}
def bits4_act_rot (g : USym c4bits_group) (x : Bits4)
  : Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) (bits4_rot (bits4_index g) x)
  ≔ funext Bits4Pos (_ ↦ Fin two) (gset_usym_act c4bits_group bits4_gset g x) (bits4_rot (bits4_index g) x)
      (i ↦ concat (Fin two) (gset_usym_act c4bits_group bits4_gset g x i) (x (g .fst .fst .fst .fst .trl i))
        (x (bits4_sub i (bits4_index g)))
        (bits4_act_pointwise g x i) (refl x (bits4_carrier_inverse g i)))

{` The symmetry r_k with r_k(0) = k; every rotation (by 0, 1, 2 or 3
   positions) is realised by a symmetry. `}
def bits4_symmetry (k : Bits4Pos) : USym c4bits_group
  ≔ equiv_inverse_map (USym c4bits_group) Bits4Pos bits4_index_equiv k

def bits4_symmetry_index (k : Bits4Pos) : Id Bits4Pos (bits4_index (bits4_symmetry k)) k
  ≔ equiv_counit (USym c4bits_group) Bits4Pos bits4_index_equiv k

def bits4_symmetry_act (k : Bits4Pos) (x : Bits4)
  : Id Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry k) x) (bits4_rot k x)
  ≔ concat Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry k) x)
      (bits4_rot (bits4_index (bits4_symmetry k)) x) (bits4_rot k x)
      (bits4_act_rot (bits4_symmetry k) x)
      (refl ((k' ↦ bits4_rot k' x) : Bits4Pos → Bits4) (bits4_symmetry_index k))

{` Litmus: the generator r_1 rotates 0001 to 1000 ((r_1 · x)(i) = x(i − 1)). `}
def bits4_rot_litmus
  : Id Bits4 (bits4_rot bits4_p1 (bits4_mk bits4_o bits4_o bits4_o bits4_l)) (bits4_mk bits4_l bits4_o bits4_o bits4_o)
  ≔ funext Bits4Pos (_ ↦ Fin two) (bits4_rot bits4_p1 (bits4_mk bits4_o bits4_o bits4_o bits4_l))
      (bits4_mk bits4_l bits4_o bits4_o bits4_o)
      (bits4_pos_ind (i ↦ Id (Fin two) (bits4_rot bits4_p1 (bits4_mk bits4_o bits4_o bits4_o bits4_l) i)
          (bits4_mk bits4_l bits4_o bits4_o bits4_o i))
        (refl bits4_l) (refl bits4_o) (refl bits4_o) (refl bits4_o))

def bits4_generator_act_litmus
  : Id Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry bits4_p1) (bits4_mk bits4_o bits4_o bits4_o bits4_l))
      (bits4_mk bits4_l bits4_o bits4_o bits4_o)
  ≔ concat Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry bits4_p1) (bits4_mk bits4_o bits4_o bits4_o bits4_l))
      (bits4_rot bits4_p1 (bits4_mk bits4_o bits4_o bits4_o bits4_l)) (bits4_mk bits4_l bits4_o bits4_o bits4_o)
      (bits4_symmetry_act bits4_p1 (bits4_mk bits4_o bits4_o bits4_o bits4_l)) bits4_rot_litmus
