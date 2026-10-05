export "1001-divisibility-lemmas"
export "1104-one-vertex-graphs"

{` The rank in the corollary at fggroups.tex:851 is well defined: free groups on
   finite sets of different cardinalities are not isomorphic (free_rank_unique).
   Proof: Hom(F_T, C_2) ≃ (T → USym C_2) ≃ (T → Fin 2) has 2^|T| elements, and
   an isomorphism F_T ≅ F_T' identifies the hom sets; 2^a = 2^b implies a = b. `}

def pow_two (a : Nat) : Nat ≔ match a [ zero. ↦ suc. zero. | suc. a ↦ mul (pow_two a) (suc. (suc. zero.)) ]

def empty_fin_two_function (i : Fin zero.) : Fin (suc. (suc. zero.)) ≔ match i []

def fin_bool_functions_equiv (a : Nat) : Equiv (Fin a → Fin (suc. (suc. zero.))) (Fin (pow_two a))
  ≔ match a [
  | zero. ↦ quasi_inverse_equiv (Fin zero. → Fin (suc. (suc. zero.))) (Fin (suc. zero.))
      (_ ↦ inr. star.) (_ ↦ empty_fin_two_function)
      (f ↦ funext (Fin zero.) (_ ↦ Fin (suc. (suc. zero.))) empty_fin_two_function f (i ↦ match i []))
      (u ↦ match u [ inl. z ↦ match z [] | inr. s ↦ match s [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ])
  | suc. a ↦ compose_equiv (Fin (suc. a) → Fin (suc. (suc. zero.)))
      (Product (Fin a → Fin (suc. (suc. zero.))) (Fin (suc. (suc. zero.))))
      (Fin (pow_two (suc. a)))
      (sum_pi_split_equiv (Fin a) (_ ↦ Fin (suc. (suc. zero.))))
      (compose_equiv (Product (Fin a → Fin (suc. (suc. zero.))) (Fin (suc. (suc. zero.))))
        (Product (Fin (pow_two a)) (Fin (suc. (suc. zero.)))) (Fin (pow_two (suc. a)))
        (product_equiv (Fin a → Fin (suc. (suc. zero.))) (Fin (suc. (suc. zero.))) (Fin (pow_two a)) (Fin (suc. (suc. zero.)))
          (fin_bool_functions_equiv a) (identity_equiv (Fin (suc. (suc. zero.)))))
        (fin_product_equiv (pow_two a) (suc. (suc. zero.)))) ]

def ZeroCode (n : Nat) : Type ≔ match n [ zero. ↦ Unit | suc. _ ↦ Empty ]

def zero_not_suc (n : Nat) (p : Id Nat zero. (suc. n)) : Empty
  ≔ transport Nat ZeroCode zero. (suc. n) p star.

def pow_two_positive (a : Nat) : Σ Nat (y ↦ Id Nat (pow_two a) (suc. y))
  ≔ match a [
  | zero. ↦ (zero., refl (suc. zero. : Nat))
  | suc. a ↦ let r ≔ pow_two_positive a in
      (add (add zero. (suc. (r .fst))) (r .fst),
       refl ((x : Nat) ↦ mul x (suc. (suc. zero.))) (r .snd)) ]

def one_not_double (y : Nat) (p : Id Nat (suc. zero.) (mul (suc. y) (suc. (suc. zero.)))) : Empty
  ≔ zero_not_suc (add (add zero. y) y)
      (concat Nat zero. (add (suc. (add zero. y)) y) (suc. (add (add zero. y) y))
        (refl nat_pred p) (add_suc_left (add zero. y) y))

def one_not_pow_double (b : Nat) (p : Id Nat (suc. zero.) (mul (pow_two b) (suc. (suc. zero.)))) : Empty
  ≔ let r ≔ pow_two_positive b in
    one_not_double (r .fst)
      (concat Nat (suc. zero.) (mul (pow_two b) (suc. (suc. zero.))) (mul (suc. (r .fst)) (suc. (suc. zero.))) p
        (refl ((x : Nat) ↦ mul x (suc. (suc. zero.))) (r .snd)))

def pow_two_injective (a b : Nat) (p : Id Nat (pow_two a) (pow_two b)) : Id Nat a b
  ≔ match a, b [
  | zero., zero. ↦ refl (zero. : Nat)
  | zero., suc. b ↦ match one_not_pow_double b p []
  | suc. a, zero. ↦ match one_not_pow_double a (inverse Nat (pow_two (suc. a)) (suc. zero.) p) []
  | suc. a, suc. b ↦ refl ((n : Nat) ↦ (suc. n : Nat))
      (pow_two_injective a b (nat_mul_cancel_right (suc. zero.) (pow_two a) (pow_two b) p)) ]

def two_group : Group ≔ cyclic_group_fin (suc. zero.)

def free_hom_two_equiv (T : Type) (dT : DecidableEquality T) (a : Nat) (p : Id Type T (Fin a))
  : Equiv (GroupHom (constructed_free_group T dT) two_group) (Fin (pow_two a))
  ≔ compose_equiv (GroupHom (constructed_free_group T dT) two_group) (T → USym two_group) (Fin (pow_two a))
      (constructed_free_group_hom_equiv T dT two_group)
      (compose_equiv (T → USym two_group) (Fin a → Fin (suc. (suc. zero.)))  (Fin (pow_two a))
        (transport Type (X ↦ Equiv (X → USym two_group) (Fin a → Fin (suc. (suc. zero.)))) (Fin a) T
          (inverse Type T (Fin a) p)
          (pi_family_equiv (Fin a) (_ ↦ USym two_group) (_ ↦ Fin (suc. (suc. zero.)))
            (_ ↦ cyclic_group_fin_usym_equiv (suc. zero.))))
        (fin_bool_functions_equiv a))

{` Free groups on finite sets of cardinalities a and b are isomorphic only if a = b. `}
def free_rank_unique (T T' : Type) (dT : DecidableEquality T) (dT' : DecidableEquality T') (a b : Nat)
  (ha : Mere (Id Type T (Fin a))) (hb : Mere (Id Type T' (Fin b)))
  (i : GroupIso (constructed_free_group T dT) (constructed_free_group T' dT'))
  : Id Nat a b
  ≔ mere_rec (Id Type T (Fin a)) (Id Nat a b) (nat_set a b) (pa ↦
      mere_rec (Id Type T' (Fin b)) (Id Nat a b) (nat_set a b) (pb ↦
        pow_two_injective a b
          (fin_equiv_cardinality (pow_two a) (pow_two b)
            (compose_equiv (Fin (pow_two a)) (GroupHom (constructed_free_group T dT) two_group) (Fin (pow_two b))
              (canonical_inverse_equiv (GroupHom (constructed_free_group T dT) two_group) (Fin (pow_two a))
                (free_hom_two_equiv T dT a pa))
              (compose_equiv (GroupHom (constructed_free_group T dT) two_group)
                (GroupHom (constructed_free_group T' dT') two_group) (Fin (pow_two b))
                (id_to_equiv (GroupHom (constructed_free_group T dT) two_group) (GroupHom (constructed_free_group T' dT') two_group)
                  (refl ((K : Group) ↦ GroupHom K two_group)
                    (group_path_from_iso (constructed_free_group T dT) (constructed_free_group T' dT') i)))
                (free_hom_two_equiv T' dT' b pb))))) hb) ha

{` Litmus: 2^3 = 8 and F_{Fin 1} is not isomorphic to F_{Fin 2}. `}
def pow_two_three : Id Nat (pow_two (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  ≔ refl (pow_two (suc. (suc. (suc. zero.))))

def free_one_not_free_two
  (i : GroupIso (constructed_free_group (Fin (suc. zero.)) (fin_decidable_equality (suc. zero.)))
         (constructed_free_group (Fin (suc. (suc. zero.))) (fin_decidable_equality (suc. (suc. zero.)))))
  : Empty
  ≔ zero_not_suc zero.
      (refl nat_pred (free_rank_unique (Fin (suc. zero.)) (Fin (suc. (suc. zero.)))
        (fin_decidable_equality (suc. zero.)) (fin_decidable_equality (suc. (suc. zero.)))
        (suc. zero.) (suc. (suc. zero.))
        (mere (Id Type (Fin (suc. zero.)) (Fin (suc. zero.))) (refl (Fin (suc. zero.))))
        (mere (Id Type (Fin (suc. (suc. zero.))) (Fin (suc. (suc. zero.)))) (refl (Fin (suc. (suc. zero.))))) i))
