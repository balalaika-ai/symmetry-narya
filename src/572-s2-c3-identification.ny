import "568-s2-acts-on-c3"
import "150-paths-over-and-pairs"

{` Chapter 5, ex:S2-acts-on-C3 (last sentence): G(Fin 2) is identified with
   C_3 = Aut_Cyc(Fin 3, s) by (X, f) ↦ (X, f_yes), identifying the 3-cycle
   (1 ⊔ Fin 2, f_yes) with (Fin 3, s) by inl 0 ↦ 0 (yes ↦ 1, no ↦ 2).

   Method: on T ≔ Σ_{X:Set} (Fin 2 → X → X) take the proposition
   Q(X, f) ≔ "f_yes is an equivalence, (X, f_yes) is cyclic and
   f_no = f_yes ∘ f_yes". Then Aut_T(pt) = Aut_{ΣTQ}(pt, q₀) (subtype),
   Σ T Q ≃ Cycles by (X, f) ↦ (X, f_yes) (f_no is determined), and the
   image of (pt, q₀) is identified with (Fin 3, s). `}

def s2c3_std : TwoElementSets ≔ shape (symmetric_group two)

def S2C3Carrier : Type ≔ Sum (Fin (suc. zero.)) (Fin two)

def s2c3_zero : S2C3Carrier ≔ inl. (inr. star.)

def s2c3_yes : S2C3Carrier ≔ inr. s2c3_fin2_yes

def s2c3_no : S2C3Carrier ≔ inr. s2c3_fin2_no

def s2c3_fy : S2C3Carrier → S2C3Carrier ≔ s2c3_move s2c3_std s2c3_fin2_yes

def s2c3_fn : S2C3Carrier → S2C3Carrier ≔ s2c3_move s2c3_std s2c3_fin2_no

{` The swaps in Fin 2 (the other element). `}
def s2c3_swap_yes : Id (Fin two) (two_set_swap s2c3_std s2c3_fin2_yes) s2c3_fin2_no
  ≔ inverse (Fin two) s2c3_fin2_no (two_set_swap s2c3_std s2c3_fin2_yes)
      (two_set_other_is_swap s2c3_std s2c3_fin2_yes s2c3_fin2_no s2c3_fin2_no_not_yes)

def s2c3_swap_no : Id (Fin two) (two_set_swap s2c3_std s2c3_fin2_no) s2c3_fin2_yes
  ≔ inverse (Fin two) s2c3_fin2_yes (two_set_swap s2c3_std s2c3_fin2_no)
      (two_set_other_is_swap s2c3_std s2c3_fin2_no s2c3_fin2_yes s2c3_fin2_yes_not_no)

{` The values of f_yes and f_no on the three points. `}
def s2c3_fy_yes : Id S2C3Carrier (s2c3_fy s2c3_yes) s2c3_no
  ≔ concat S2C3Carrier (s2c3_fy s2c3_yes) (inr. (two_set_swap s2c3_std s2c3_fin2_yes)) s2c3_no
      (s2c3_move_self s2c3_std s2c3_fin2_yes)
      (refl ((s ↦ inr. s) : Fin two → S2C3Carrier) s2c3_swap_yes)

def s2c3_fy_no : Id S2C3Carrier (s2c3_fy s2c3_no) s2c3_zero
  ≔ s2c3_branch_no s2c3_std s2c3_fin2_yes s2c3_fin2_no s2c3_fin2_no_not_yes
      (two_set_decidable s2c3_std s2c3_fin2_no s2c3_fin2_yes)

def s2c3_fn_yes : Id S2C3Carrier (s2c3_fn s2c3_yes) s2c3_zero
  ≔ s2c3_branch_no s2c3_std s2c3_fin2_no s2c3_fin2_yes s2c3_fin2_yes_not_no
      (two_set_decidable s2c3_std s2c3_fin2_yes s2c3_fin2_no)

def s2c3_fn_no : Id S2C3Carrier (s2c3_fn s2c3_no) s2c3_yes
  ≔ concat S2C3Carrier (s2c3_fn s2c3_no) (inr. (two_set_swap s2c3_std s2c3_fin2_no)) s2c3_yes
      (s2c3_move_self s2c3_std s2c3_fin2_no)
      (refl ((s ↦ inr. s) : Fin two → S2C3Carrier) s2c3_swap_no)

{` f_no = f_yes ∘ f_yes, f_no ∘ f_yes = id and f_yes ∘ f_no = id, pointwise. `}
def s2c3_fn_square (x : S2C3Carrier) : Id S2C3Carrier (s2c3_fn x) (s2c3_fy (s2c3_fy x))
  ≔ match x [
  | inl. (inr. star.) ↦ inverse S2C3Carrier (s2c3_fy (s2c3_fy s2c3_zero)) s2c3_no s2c3_fy_yes
  | inl. (inl. e) ↦ match e []
  | inr. (inr. star.) ↦ concat S2C3Carrier (s2c3_fn s2c3_yes) s2c3_zero (s2c3_fy (s2c3_fy s2c3_yes)) s2c3_fn_yes
      (inverse S2C3Carrier (s2c3_fy (s2c3_fy s2c3_yes)) s2c3_zero
        (concat S2C3Carrier (s2c3_fy (s2c3_fy s2c3_yes)) (s2c3_fy s2c3_no) s2c3_zero
          (refl s2c3_fy s2c3_fy_yes) s2c3_fy_no))
  | inr. (inl. (inr. star.)) ↦ concat S2C3Carrier (s2c3_fn s2c3_no) s2c3_yes (s2c3_fy (s2c3_fy s2c3_no)) s2c3_fn_no
      (inverse S2C3Carrier (s2c3_fy (s2c3_fy s2c3_no)) s2c3_yes (refl s2c3_fy s2c3_fy_no))
  | inr. (inl. (inl. e)) ↦ match e [] ]

def s2c3_fn_fy (x : S2C3Carrier) : Id S2C3Carrier (s2c3_fn (s2c3_fy x)) x
  ≔ match x [
  | inl. (inr. star.) ↦ s2c3_fn_yes
  | inl. (inl. e) ↦ match e []
  | inr. (inr. star.) ↦ concat S2C3Carrier (s2c3_fn (s2c3_fy s2c3_yes)) (s2c3_fn s2c3_no) s2c3_yes
      (refl s2c3_fn s2c3_fy_yes) s2c3_fn_no
  | inr. (inl. (inr. star.)) ↦ refl s2c3_fn s2c3_fy_no
  | inr. (inl. (inl. e)) ↦ match e [] ]

def s2c3_fy_fn (x : S2C3Carrier) : Id S2C3Carrier (s2c3_fy (s2c3_fn x)) x
  ≔ match x [
  | inl. (inr. star.) ↦ s2c3_fy_no
  | inl. (inl. e) ↦ match e []
  | inr. (inr. star.) ↦ refl s2c3_fy s2c3_fn_yes
  | inr. (inl. (inr. star.)) ↦ concat S2C3Carrier (s2c3_fy (s2c3_fn s2c3_no)) (s2c3_fy s2c3_yes) s2c3_no
      (refl s2c3_fy s2c3_fn_no) s2c3_fy_yes
  | inr. (inl. (inl. e)) ↦ match e [] ]

def s2c3_fy_equiv : Equiv S2C3Carrier S2C3Carrier
  ≔ quasi_inverse_equiv S2C3Carrier S2C3Carrier s2c3_fy s2c3_fn s2c3_fn_fy s2c3_fy_fn

{` ψ : 1 ⊔ Fin 2 ≃ Fin 3, inl 0 ↦ 0, yes ↦ 1, no ↦ 2. `}
def s2c3_psi (x : S2C3Carrier) : Fin three
  ≔ match x [ inl. _ ↦ fin3_zero | inr. (inr. _) ↦ fin3_one | inr. (inl. _) ↦ fin3_two ]

def s2c3_psi_inv : Fin three → S2C3Carrier
  ≔ [ inr. _ ↦ s2c3_zero | inl. (inr. _) ↦ s2c3_yes | inl. (inl. (inr. _)) ↦ s2c3_no | inl. (inl. (inl. e)) ↦ match e [] ]

def s2c3_psi_sect (x : S2C3Carrier) : Id S2C3Carrier (s2c3_psi_inv (s2c3_psi x)) x
  ≔ match x [
  | inl. (inr. star.) ↦ refl s2c3_zero
  | inl. (inl. e) ↦ match e []
  | inr. (inr. star.) ↦ refl s2c3_yes
  | inr. (inl. (inr. star.)) ↦ refl s2c3_no
  | inr. (inl. (inl. e)) ↦ match e [] ]

def s2c3_psi_retr (k : Fin three) : Id (Fin three) (s2c3_psi (s2c3_psi_inv k)) k
  ≔ match k [
  | inr. star. ↦ refl fin3_zero
  | inl. (inr. star.) ↦ refl fin3_one
  | inl. (inl. (inr. star.)) ↦ refl fin3_two
  | inl. (inl. (inl. e)) ↦ match e [] ]

def s2c3_psi_equiv : Equiv S2C3Carrier (Fin three)
  ≔ quasi_inverse_equiv S2C3Carrier (Fin three) s2c3_psi s2c3_psi_inv s2c3_psi_sect s2c3_psi_retr

{` ψ ∘ f_yes = s ∘ ψ. `}
def s2c3_succ_zero : Id (Fin three) (finite_fin_successor two .map (inr. star.)) (inl. (inr. star.)) ≔ refl (inl. (inr. star.) : Fin three)

def s2c3_succ_one : Id (Fin three) (finite_fin_successor two .map fin3_one) fin3_two ≔ refl fin3_two

def s2c3_succ_two : Id (Fin three) (finite_fin_successor two .map fin3_two) fin3_zero ≔ refl fin3_zero

def s2c3_psi_fy_yes : Id (Fin three) (s2c3_psi (s2c3_fy s2c3_yes)) fin3_two
  ≔ refl ((x ↦ s2c3_psi x) : S2C3Carrier → Fin three) s2c3_fy_yes

def s2c3_psi_fy_no : Id (Fin three) (s2c3_psi (s2c3_fy s2c3_no)) fin3_zero
  ≔ refl ((x ↦ s2c3_psi x) : S2C3Carrier → Fin three) s2c3_fy_no

def s2c3_psi_commutes_at (x : S2C3Carrier)
  : Id (Fin three) (s2c3_psi (s2c3_fy x)) (finite_fin_successor two .map (s2c3_psi x))
  ≔ match x [
  | inl. (inr. star.) ↦ s2c3_succ_zero
  | inl. (inl. e) ↦ match e []
  | inr. (inr. star.) ↦ s2c3_psi_fy_yes
  | inr. (inl. (inr. star.)) ↦ s2c3_psi_fy_no
  | inr. (inl. (inl. e)) ↦ match e [] ]

def s2c3_psi_commutes
  : Commutes S2C3Carrier (Fin three) s2c3_fy_equiv (finite_fin_successor two) s2c3_psi
  ≔ x ↦ s2c3_psi_commutes_at x

def s2c3_permutation : Permutations ≔ (s2c3_one_plus s2c3_std, s2c3_fy_equiv)

def s2c3_permutation_path : Id Permutations s2c3_permutation (finite_fin_cycle two .fst)
  ≔ equiv_inverse_map (Id Permutations s2c3_permutation (finite_fin_cycle two .fst))
      (PermutationIsomorphisms s2c3_permutation (finite_fin_cycle two .fst))
      (permutation_paths_equiv s2c3_permutation (finite_fin_cycle two .fst))
      (s2c3_psi_equiv, s2c3_psi_commutes)

def s2c3_cyclic : Cyclic S2C3Carrier s2c3_fy_equiv
  ≔ transport Permutations (p ↦ Cyclic (p .fst .fst) (p .snd)) (finite_fin_cycle two .fst) s2c3_permutation
      (inverse Permutations s2c3_permutation (finite_fin_cycle two .fst) s2c3_permutation_path)
      (finite_fin_cycle two .snd)

def s2c3_cycle : Cycles ≔ (s2c3_permutation, s2c3_cyclic)

{` (1 ⊔ Fin 2, f_yes) = (Fin 3, s) as 3-cycles. `}
def s2c3_cycle_path : Id Cycles s2c3_cycle (finite_fin_cycle two)
  ≔ subtype_equal Permutations (p ↦ Cyclic (p .fst .fst) (p .snd)) (p ↦ cyclic_prop (p .fst .fst) (p .snd))
      s2c3_cycle (finite_fin_cycle two) s2c3_permutation_path

{` The proposition Q on T = Σ_{X:Set} (Fin 2 → X → X). `}
def S2C3Prop (u : S2C3Type s2c3_std) : Type
  ≔ Σ (isEquiv (u .fst .fst) (u .fst .fst) (u .snd s2c3_fin2_yes)) (ie ↦
      Product (Cyclic (u .fst .fst) (u .snd s2c3_fin2_yes, ie))
        (Id (u .fst .fst → u .fst .fst) (u .snd s2c3_fin2_no) (x ↦ u .snd s2c3_fin2_yes (u .snd s2c3_fin2_yes x))))

def s2c3_prop_isprop (u : S2C3Type s2c3_std) : isProp (S2C3Prop u)
  ≔ let X ≔ u .fst .fst in
    let fy ≔ u .snd s2c3_fin2_yes in
    sigma_prop (isEquiv X X fy)
      (ie ↦ Product (Cyclic X (fy, ie)) (Id (X → X) (u .snd s2c3_fin2_no) (x ↦ fy (fy x))))
      (isequiv_isprop X X fy)
      (ie ↦ product_prop (Cyclic X (fy, ie)) (Id (X → X) (u .snd s2c3_fin2_no) (x ↦ fy (fy x)))
        (cyclic_prop X (fy, ie))
        (pi_set X (_ ↦ X) (_ ↦ u .fst .snd) (u .snd s2c3_fin2_no) (x ↦ fy (fy x))))

def s2c3_prop_point : S2C3Prop (s2c3_point s2c3_std)
  ≔ (s2c3_fy_equiv .equiv, (s2c3_cyclic,
      funext S2C3Carrier (_ ↦ S2C3Carrier) s2c3_fn (x ↦ s2c3_fy (s2c3_fy x)) s2c3_fn_square))

def S2C3Sub : Type ≔ Σ (S2C3Type s2c3_std) S2C3Prop

def s2c3_two_fn (X : Type) (t : X → X) : Fin two → X → X
  ≔ [ inr. _ ↦ t | inl. (inr. _) ↦ x ↦ t (t x) | inl. (inl. e) ↦ match e [] ]

def s2c3_sub_to_cycles (v : S2C3Sub) : Cycles
  ≔ ((v .fst .fst, (v .fst .snd s2c3_fin2_yes, v .snd .fst)), v .snd .snd .fst)

def s2c3_cycles_to_sub (c : Cycles) : S2C3Sub
  ≔ ((c .fst .fst, s2c3_two_fn (c .fst .fst .fst) (c .fst .snd .map)),
     (c .fst .snd .equiv, (c .snd, refl ((x ↦ c .fst .snd .map (c .fst .snd .map x)) : c .fst .fst .fst → c .fst .fst .fst))))

def s2c3_sub_roundtrip (v : S2C3Sub) : Id S2C3Sub (s2c3_cycles_to_sub (s2c3_sub_to_cycles v)) v
  ≔ let X ≔ v .fst .fst in
    let f ≔ v .fst .snd in
    let h ≔ v .snd .snd .snd in
    subtype_equal (S2C3Type s2c3_std) S2C3Prop s2c3_prop_isprop (s2c3_cycles_to_sub (s2c3_sub_to_cycles v)) v
      (pair_path SetTypes (Y ↦ Fin two → Y .fst → Y .fst) X X (s2c3_two_fn (X .fst) (f s2c3_fin2_yes)) f (refl X)
        (funext (Fin two) (_ ↦ X .fst → X .fst) (s2c3_two_fn (X .fst) (f s2c3_fin2_yes)) f
          [ inr. star. ↦ refl (f s2c3_fin2_yes)
          | inl. (inr. star.) ↦ inverse (X .fst → X .fst) (f s2c3_fin2_no) (x ↦ f s2c3_fin2_yes (f s2c3_fin2_yes x)) h
          | inl. (inl. e) ↦ match e [] ]))

def s2c3_sub_cycles_equiv : Equiv S2C3Sub Cycles
  ≔ quasi_inverse_equiv S2C3Sub Cycles s2c3_sub_to_cycles s2c3_cycles_to_sub s2c3_sub_roundtrip (c ↦ refl c)

def s2c3_sub_groupoid : isGroupoid S2C3Sub
  ≔ hlevel_to_groupoid S2C3Sub
      (hlevel_sigma (suc. (suc. (suc. zero.))) (S2C3Type s2c3_std) S2C3Prop
        (groupoid_to_hlevel (S2C3Type s2c3_std) (s2c3_type_groupoid s2c3_std))
        (u ↦ hlevel_raise (suc. (suc. zero.)) (S2C3Prop u)
          (hlevel_raise (suc. zero.) (S2C3Prop u) (prop_to_hlevel_one (S2C3Prop u) (s2c3_prop_isprop u)))))

{` ex:S2-acts-on-C3: G(Fin 2) = C_3. The underlying map of classifying types
   sends (X, f) to the 3-cycle (X, f_yes). `}
def s2c3_group_c3_path : Id Group (s2c3_group s2c3_std) (cyclic_group_fin two)
  ≔ let T ≔ S2C3Type s2c3_std in
    let u0 : S2C3Sub ≔ (s2c3_point s2c3_std, s2c3_prop_point) in
    concat Group (s2c3_group s2c3_std) (automorphism_group S2C3Sub s2c3_sub_groupoid u0) (cyclic_group_fin two)
      (inverse Group (automorphism_group S2C3Sub s2c3_sub_groupoid u0) (s2c3_group s2c3_std)
        (automorphism_group_subtype_path T S2C3Prop s2c3_prop_isprop s2c3_sub_groupoid (s2c3_type_groupoid s2c3_std) u0))
      (automorphism_group_equiv_path_at S2C3Sub Cycles s2c3_sub_groupoid cycles_groupoid s2c3_sub_cycles_equiv u0
        (finite_fin_cycle two) s2c3_cycle_path)

{` The 3-cycle attached to the designated shape is (1 ⊔ Fin 2, f_yes), and
   f_no = f_yes ∘ f_yes there. `}
def s2c3_point_cycle : Id Cycles (s2c3_sub_to_cycles (s2c3_point s2c3_std, s2c3_prop_point)) s2c3_cycle
  ≔ refl s2c3_cycle
