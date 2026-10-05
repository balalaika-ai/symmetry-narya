export "410-pointed-connected-groupoids"
export "505-gset-core-litmus"

{` Chapter 5 (actions.tex), ex:S2-acts-on-C3: the action of Σ_2 on C_3.

   BΣ_2 ≡ BookFiniteSetsAt 2 (2-element sets S with ‖(Fin 2, !) = S‖).
   For S : BΣ_2 the type T_S ≔ Σ_{X:Set} (S → (X → X)) contains
   (1 ⊔ S, f) with f_s(inl 0) = inr s, f_s(inr s) = inr (swap s) and
   f_s(inr (swap s)) = inl 0, where swap s is the other element of S
   (the center of the contractible type of elements different from s) and
   the case distinction uses the decidable equality of S. Both are
   transported from Fin 2 (they are propositions). G(S) ≔ Aut_{T_S}(1 ⊔ S, f)
   gives the action S ↦ G(S) : BΣ_2 → Group.

   G(Fin 2) is identified with C_3 = cyclic_group_fin 2 = Aut_Cyc(Fin 3, s)
   through the chain T_{Fin 2} ≃ Σ_{X:Set} (X → X) × (X → X), the subtype
   where the first map is an equivalence with left inverse the second,
   ≃ Permutations (the first map, f_yes), and the identification of
   (1 ⊔ Fin 2, f_yes) with (Fin 3, s) sending inl 0 to 0 (yes ≔ 0 = inr ⋆,
   no ≔ 1 of Fin 2). `}

def TwoElementSets : Type ≔ BG (symmetric_group two) .carrier

def two_set_carrier (S : TwoElementSets) : Type ≔ S .fst .fst

{` Propositions about sets hold for every 2-element set once they hold for Fin 2. `}
def two_set_prop_transfer (Q : SetTypes → Type) (hQ : (T : SetTypes) → isProp (Q T)) (q0 : Q (standard_set two))
  (S : TwoElementSets) : Q (S .fst)
  ≔ mere_rec (Id SetTypes (standard_set two) (S .fst)) (Q (S .fst)) (hQ (S .fst))
      (p ↦ transport SetTypes Q (standard_set two) (S .fst) p q0) (S .snd)

def two_set_decidable (S : TwoElementSets) : DecidableEquality (two_set_carrier S)
  ≔ two_set_prop_transfer (T ↦ DecidableEquality (T .fst)) (T ↦ decidable_equality_prop (T .fst) (T .snd))
      (fin_decidable_equality two) S

{` The other element: Σ_{s'} (s' ≠ s) is contractible in a 2-element set. `}
def TwoSetOther (A : Type) (s : A) : Type ≔ Σ A (s' ↦ Not (Id A s' s))

def s2c3_fin2_yes : Fin two ≔ inr. star.

def s2c3_fin2_no : Fin two ≔ inl. (inr. star.)

def s2c3_fin2_code : Fin two → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def s2c3_fin2_yes_not_no (p : Id (Fin two) s2c3_fin2_yes s2c3_fin2_no) : Empty
  ≔ transport (Fin two) s2c3_fin2_code s2c3_fin2_yes s2c3_fin2_no p star.

def s2c3_fin2_no_not_yes (p : Id (Fin two) s2c3_fin2_no s2c3_fin2_yes) : Empty
  ≔ s2c3_fin2_yes_not_no (inverse (Fin two) s2c3_fin2_no s2c3_fin2_yes p)

def s2c3_other_path (A : Type) (s : A) (u v : TwoSetOther A s) (p : Id A (u .fst) (v .fst)) : Id (TwoSetOther A s) u v
  ≔ subtype_equal A (s' ↦ Not (Id A s' s)) (s' ↦ negation_prop (Id A s' s)) u v p

def fin_two_other_unique_yes (y : Fin two) (h : Not (Id (Fin two) y s2c3_fin2_yes))
  : Id (TwoSetOther (Fin two) s2c3_fin2_yes) (s2c3_fin2_no, s2c3_fin2_no_not_yes) (y, h)
  ≔ match y [
  | inr. star. ↦ absurd (Id (TwoSetOther (Fin two) s2c3_fin2_yes) (s2c3_fin2_no, s2c3_fin2_no_not_yes) (inr. star., h))
      (h (refl s2c3_fin2_yes))
  | inl. (inr. star.) ↦ s2c3_other_path (Fin two) s2c3_fin2_yes (s2c3_fin2_no, s2c3_fin2_no_not_yes) (inl. (inr. star.), h)
      (refl s2c3_fin2_no)
  | inl. (inl. e) ↦ match e [] ]

def fin_two_other_unique_no (y : Fin two) (h : Not (Id (Fin two) y s2c3_fin2_no))
  : Id (TwoSetOther (Fin two) s2c3_fin2_no) (s2c3_fin2_yes, s2c3_fin2_yes_not_no) (y, h)
  ≔ match y [
  | inr. star. ↦ s2c3_other_path (Fin two) s2c3_fin2_no (s2c3_fin2_yes, s2c3_fin2_yes_not_no) (inr. star., h)
      (refl s2c3_fin2_yes)
  | inl. (inr. star.) ↦ absurd (Id (TwoSetOther (Fin two) s2c3_fin2_no) (s2c3_fin2_yes, s2c3_fin2_yes_not_no) (inl. (inr. star.), h))
      (h (refl s2c3_fin2_no))
  | inl. (inl. e) ↦ match e [] ]

def fin_two_other_contractible (s : Fin two) : BookIsContr (TwoSetOther (Fin two) s)
  ≔ match s [
  | inr. star. ↦ ((s2c3_fin2_no, s2c3_fin2_no_not_yes), u ↦ fin_two_other_unique_yes (u .fst) (u .snd))
  | inl. (inr. star.) ↦ ((s2c3_fin2_yes, s2c3_fin2_yes_not_no), u ↦ fin_two_other_unique_no (u .fst) (u .snd))
  | inl. (inl. e) ↦ match e [] ]

def two_set_other_contractible (S : TwoElementSets) (s : two_set_carrier S)
  : BookIsContr (TwoSetOther (two_set_carrier S) s)
  ≔ two_set_prop_transfer (T ↦ (t : T .fst) → BookIsContr (TwoSetOther (T .fst) t))
      (T ↦ pi_prop (T .fst) (t ↦ BookIsContr (TwoSetOther (T .fst) t)) (t ↦ book_iscontr_isprop (TwoSetOther (T .fst) t)))
      fin_two_other_contractible S s

def two_set_swap (S : TwoElementSets) (s : two_set_carrier S) : two_set_carrier S
  ≔ two_set_other_contractible S s .center .fst

def two_set_swap_ne (S : TwoElementSets) (s : two_set_carrier S) : Not (Id (two_set_carrier S) (two_set_swap S s) s)
  ≔ two_set_other_contractible S s .center .snd

{` Any element different from s is swap s. `}
def two_set_other_is_swap (S : TwoElementSets) (s s' : two_set_carrier S) (h : Not (Id (two_set_carrier S) s' s))
  : Id (two_set_carrier S) s' (two_set_swap S s)
  ≔ inverse (two_set_carrier S) (two_set_swap S s) s'
      (refl ((u ↦ u .fst) : TwoSetOther (two_set_carrier S) s → two_set_carrier S)
        (two_set_other_contractible S s .contract (s', h)))

{` 1 ⊔ S and the functions f_s. `}
def s2c3_one_plus (S : TwoElementSets) : SetTypes
  ≔ (Sum (Fin (suc. zero.)) (two_set_carrier S),
     sum_set (Fin (suc. zero.)) (two_set_carrier S) (fin_set (suc. zero.)) (S .fst .snd))

def s2c3_branch (S : TwoElementSets) (s s' : two_set_carrier S) (d : Decidable (Id (two_set_carrier S) s' s))
  : Sum (Fin (suc. zero.)) (two_set_carrier S)
  ≔ match d [ inl. _ ↦ inr. (two_set_swap S s) | inr. _ ↦ inl. (inr. star.) ]

def s2c3_move (S : TwoElementSets) (s : two_set_carrier S) (x : Sum (Fin (suc. zero.)) (two_set_carrier S))
  : Sum (Fin (suc. zero.)) (two_set_carrier S)
  ≔ match x [ inl. _ ↦ inr. s | inr. s' ↦ s2c3_branch S s s' (two_set_decidable S s' s) ]

{` The book's three defining equations of f_s. `}
def s2c3_branch_yes (S : TwoElementSets) (s s' : two_set_carrier S) (p : Id (two_set_carrier S) s' s)
  (d : Decidable (Id (two_set_carrier S) s' s))
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (s2c3_branch S s s' d) (inr. (two_set_swap S s))
  ≔ match d [ inl. _ ↦ refl (inr. (two_set_swap S s) : Sum (Fin (suc. zero.)) (two_set_carrier S))
            | inr. n ↦ absurd (Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (inl. (inr. star.)) (inr. (two_set_swap S s))) (n p) ]

def s2c3_branch_no (S : TwoElementSets) (s s' : two_set_carrier S) (n : Not (Id (two_set_carrier S) s' s))
  (d : Decidable (Id (two_set_carrier S) s' s))
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (s2c3_branch S s s' d) (inl. (inr. star.))
  ≔ match d [ inl. p ↦ absurd (Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (inr. (two_set_swap S s)) (inl. (inr. star.))) (n p)
            | inr. _ ↦ refl (inl. (inr. star.) : Sum (Fin (suc. zero.)) (two_set_carrier S)) ]

def s2c3_move_zero (S : TwoElementSets) (s : two_set_carrier S)
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (s2c3_move S s (inl. (inr. star.))) (inr. s)
  ≔ refl (inr. s : Sum (Fin (suc. zero.)) (two_set_carrier S))

def s2c3_move_self (S : TwoElementSets) (s : two_set_carrier S)
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (s2c3_move S s (inr. s)) (inr. (two_set_swap S s))
  ≔ s2c3_branch_yes S s s (refl s) (two_set_decidable S s s)

def s2c3_move_swap (S : TwoElementSets) (s : two_set_carrier S)
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (s2c3_move S s (inr. (two_set_swap S s))) (inl. (inr. star.))
  ≔ s2c3_branch_no S s (two_set_swap S s) (two_set_swap_ne S s) (two_set_decidable S (two_set_swap S s) s)

{` T_S ≔ Σ_{X:Set} (S → (X → X)), a groupoid, and its point (1 ⊔ S, f). `}
def S2C3Type (S : TwoElementSets) : Type ≔ Σ SetTypes (X ↦ two_set_carrier S → X .fst → X .fst)

def s2c3_type_groupoid (S : TwoElementSets) : isGroupoid (S2C3Type S)
  ≔ hlevel_to_groupoid (S2C3Type S)
      (hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes (X ↦ two_set_carrier S → X .fst → X .fst)
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (X ↦ hlevel_raise (suc. (suc. zero.)) (two_set_carrier S → X .fst → X .fst)
          (set_to_hlevel_two (two_set_carrier S → X .fst → X .fst)
            (pi_set (two_set_carrier S) (_ ↦ X .fst → X .fst) (_ ↦ pi_set (X .fst) (_ ↦ X .fst) (_ ↦ X .snd))))))

def s2c3_point (S : TwoElementSets) : S2C3Type S ≔ (s2c3_one_plus S, s2c3_move S)

{` G(S) ≔ Aut_{T_S}(1 ⊔ S, f), and the action S ↦ G(S) : BΣ_2 → Group. `}
def s2c3_group (S : TwoElementSets) : Group ≔ automorphism_group (S2C3Type S) (s2c3_type_groupoid S) (s2c3_point S)

def s2_acts_on_c3 : ActionInType (symmetric_group two) Group ≔ S ↦ s2c3_group S
