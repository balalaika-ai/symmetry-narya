export "592-c6-half-subgroup-group"
export "1030-subgroup-containment"
export "1011-cyclic-group-homs"
export "1012-finite-group-orders"

{` Chapter 5, running text after def:decidable-subgroup
   (actions.tex 897): "There are other decidable subgroups of C_6, and they
   are accounted for simply by the various factorizations of the number 6."

   Formal content. Work with C_6 = cyclic_group 6 (generator s, chapter 10)
   and transport to the book's C_6 = Aut_Cyc(Fin 6, s) = cyclic_group_fin 5
   along cyclic_group_fin_path at the end. For each factorization 6 = d·k
   (index c : Fin 4 for d = 1, 2, 3, 6) T_c is the cyclic subgroup generated
   by s^d (s^6 = e for d = 6); its underlying group is C_k
   (c6sub_subgroup_group_path) and its underlying set has d elements
   (c6sub_index_card, Lagrange counting). Classification
   (c6sub_classification): every decidable subgroup S of C_6 equals T_c for
   the c computed from which of s, s^2, ..., s^5 fix the point of S; distinct
   c give distinct subgroups (c6sub_subgroup_injective, by the orders k).
   Hence the type of decidable subgroups of C_6 is equivalent to Fin 4, the
   set of factorizations (c6sub_decidable_subgroups_equiv, and
   c6sub_book_equiv for the book's C_6).

   Proof of the classification: decidability of S makes "s^i fixes the
   point" a Boolean a_i; a_0 = true and closure of the fixing symmetries
   under multiplication give 12 Boolean implications a_i ∧ a_j ⇒ a_(i+j mod 6);
   a finite check over the 64 Boolean vectors (c6sub_check_all) shows that
   a is then the indicator of the multiples of d for one of d = 1, 2, 3, 6.
   Since every symmetry is a power s^k, k < 6, S and T_c fix the same
   symmetries, so they contain each other (subgroup_le_antisym, chapter 10).

   The book's subgroup (X/2, [0]) of exa:C3subC6 (c6half_subgroup, module
   592) is the factorization 6 = 2·3 (c6sub_book_half_index). `}

def c6sub_group : Group ≔ cyclic_group c6half_six

def c6sub_gen : USym c6sub_group ≔ cyclic_group_generator c6half_five

def c6sub_pow (k : Nat) : USym c6sub_group ≔ usym_power c6sub_group c6sub_gen k

def c6sub_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))

{` The four factorizations 6 = d · k, indexed by d = 1, 2, 3, 6. `}
def C6SubIndex : Type ≔ Fin c6sub_four

def c6sub_c1 : C6SubIndex ≔ inr. star.
def c6sub_c2 : C6SubIndex ≔ inl. (inr. star.)
def c6sub_c3 : C6SubIndex ≔ inl. (inl. (inr. star.))
def c6sub_c6 : C6SubIndex ≔ inl. (inl. (inl. (inr. star.)))

def c6sub_divisor : C6SubIndex → Nat ≔ [
  | inr. _ ↦ suc. zero.
  | inl. (inr. _) ↦ two
  | inl. (inl. (inr. _)) ↦ c6half_three
  | inl. (inl. (inl. (inr. _))) ↦ c6half_six
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_cofactor : C6SubIndex → Nat ≔ [
  | inr. _ ↦ c6half_six
  | inl. (inr. _) ↦ c6half_three
  | inl. (inl. (inr. _)) ↦ two
  | inl. (inl. (inl. (inr. _))) ↦ suc. zero.
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_factorization (c : C6SubIndex) : Id Nat (mul (c6sub_divisor c) (c6sub_cofactor c)) c6half_six
  ≔ match c [
  | inr. _ ↦ refl c6half_six
  | inl. (inr. _) ↦ refl c6half_six
  | inl. (inl. (inr. _)) ↦ refl c6half_six
  | inl. (inl. (inl. (inr. _))) ↦ refl c6half_six
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_cofactor_positive (c : C6SubIndex) : Lt zero. (c6sub_cofactor c)
  ≔ match c [
  | inr. _ ↦ star.
  | inl. (inr. _) ↦ star.
  | inl. (inl. (inr. _)) ↦ star.
  | inl. (inl. (inl. (inr. _))) ↦ star.
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

{` "t fixes the point of S". `}
def C6SubFixes (S : Subgroups c6sub_group) (t : USym c6sub_group) : Type
  ≔ Id (gset_underlying c6sub_group (S .gset)) (gset_usym_act c6sub_group (S .gset) t (S .point)) (S .point)

def c6sub_fixes_path (S : Subgroups c6sub_group) (t t' : USym c6sub_group) (p : Id (USym c6sub_group) t t')
  (h : C6SubFixes S t) : C6SubFixes S t'
  ≔ transport (USym c6sub_group) (C6SubFixes S) t t' p h

{` A symmetry fixing x fixes x under all its powers. `}
def c6sub_fix_power (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G)
  (hg : Id (gset_underlying G X) (gset_usym_act G X g x) x) (k : Nat)
  : Id (gset_underlying G X) (gset_usym_act G X (usym_power G g k) x) x
  ≔ match k [
  | zero. ↦ gset_act_unit G X x
  | suc. k ↦ concat (gset_underlying G X) (gset_usym_act G X (usym_mul G g (usym_power G g k)) x)
      (gset_usym_act G X g (gset_usym_act G X (usym_power G g k) x)) x
      (gset_act_mul G X g (usym_power G g k) x)
      (concat (gset_underlying G X) (gset_usym_act G X g (gset_usym_act G X (usym_power G g k) x)) (gset_usym_act G X g x) x
        (refl (gset_usym_act G X g) (c6sub_fix_power G X x g hg k)) hg) ]

{` Closure: if s^i and s^j fix the point, so does s^(i+j) (= s^r). `}
def c6sub_pair (S : Subgroups c6sub_group) (i j r : Nat) (p : Id (USym c6sub_group) (c6sub_pow (add i j)) (c6sub_pow r))
  (hi : C6SubFixes S (c6sub_pow i)) (hj : C6SubFixes S (c6sub_pow j)) : C6SubFixes S (c6sub_pow r)
  ≔ let G ≔ c6sub_group in
    let X ≔ S .gset in
    let x ≔ S .point in
    let U ≔ gset_underlying G X in
    c6sub_fixes_path S (c6sub_pow (add i j)) (c6sub_pow r) p
      (concat U (gset_usym_act G X (c6sub_pow (add i j)) x) (gset_usym_act G X (usym_mul G (c6sub_pow j) (c6sub_pow i)) x) x
        (refl ((t ↦ gset_usym_act G X t x) : USym G → U) (usym_power_add G c6sub_gen i j))
        (concat U (gset_usym_act G X (usym_mul G (c6sub_pow j) (c6sub_pow i)) x)
          (gset_usym_act G X (c6sub_pow j) (gset_usym_act G X (c6sub_pow i) x)) x
          (gset_act_mul G X (c6sub_pow j) (c6sub_pow i) x)
          (concat U (gset_usym_act G X (c6sub_pow j) (gset_usym_act G X (c6sub_pow i) x)) (gset_usym_act G X (c6sub_pow j) x) x
            (refl (gset_usym_act G X (c6sub_pow j)) hi) hj)))

{` s^(r+6) = s^r. `}
def c6sub_period (r : Nat) : Id (USym c6sub_group) (c6sub_pow (add r c6half_six)) (c6sub_pow r)
  ≔ let G ≔ c6sub_group in
    concat (USym G) (c6sub_pow (add r c6half_six)) (usym_mul G (c6sub_pow c6half_six) (c6sub_pow r)) (c6sub_pow r)
      (usym_power_add G c6sub_gen r c6half_six)
      (concat (USym G) (usym_mul G (c6sub_pow c6half_six) (c6sub_pow r)) (usym_mul G (usym_unit G) (c6sub_pow r)) (c6sub_pow r)
        (refl ((u ↦ usym_mul G u (c6sub_pow r)) : USym G → USym G) (cyclic_group_generator_order c6half_five))
        (concat_p1 (BG G .carrier) (shape G) (shape G) (c6sub_pow r)))

{` The Boolean layer. a_i = [s^i fixes the point of S]. `}
def c6sub_bv (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S) (k : Nat) : Bool
  ≔ decision_bool (C6SubFixes S (c6sub_pow k))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow k) (S .point)) (S .point))

def c6sub_bv_sound (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S) (k : Nat)
  (h : Id Bool (c6sub_bv S dS k) true.) : C6SubFixes S (c6sub_pow k)
  ≔ decision_bool_reflect (C6SubFixes S (c6sub_pow k))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow k) (S .point)) (S .point)) h

def c6sub_bv_complete (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S) (k : Nat)
  (x : C6SubFixes S (c6sub_pow k)) : Id Bool (c6sub_bv S dS k) true.
  ≔ decision_bool_true (C6SubFixes S (c6sub_pow k))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow k) (S .point)) (S .point)) x

def c6sub_imp (x y z : Bool) : Bool ≔ bits4_implies (bits4_and x y) z

def c6sub_bool_imp (A B C : Type) (dA : Decidable A) (dB : Decidable B) (dC : Decidable C) (h : A → B → C)
  : Id Bool (c6sub_imp (decision_bool A dA) (decision_bool B dB) (decision_bool C dC)) true.
  ≔ match dA [
  | inr. _ ↦ refl (true. : Bool)
  | inl. a ↦ match dB [
    | inr. _ ↦ refl (true. : Bool)
    | inl. b ↦ match dC [
      | inl. _ ↦ refl (true. : Bool)
      | inr. n ↦ absurd (Id Bool false. true.) (n (h a b)) ] ] ]

{` The 12 closure implications that determine a closed set of exponents. `}
def c6sub_closedb (a1 a2 a3 a4 a5 : Bool) : Bool
  ≔ bits4_and (c6sub_imp a1 a1 a2) (bits4_and (c6sub_imp a2 a1 a3) (bits4_and (c6sub_imp a3 a1 a4) (bits4_and (c6sub_imp a4 a1 a5) (bits4_and (c6sub_imp a5 a5 a4) (bits4_and (c6sub_imp a4 a5 a3) (bits4_and (c6sub_imp a3 a5 a2) (bits4_and (c6sub_imp a2 a5 a1) (bits4_and (c6sub_imp a2 a2 a4) (bits4_and (c6sub_imp a4 a4 a2) (bits4_and (c6sub_imp a2 a3 a5) (c6sub_imp a4 a3 a1)))))))))))

{` Indicator of the multiples of d among 0, ..., 5. `}
def c6sub_pat_even (i : Nat) : Bool ≔ match i [ zero. ↦ true. | suc. zero. ↦ false. | suc. (suc. k) ↦ c6sub_pat_even k ]

def c6sub_pat_three (i : Nat) : Bool
  ≔ match i [ zero. ↦ true. | suc. zero. ↦ false. | suc. (suc. zero.) ↦ false. | suc. (suc. (suc. k)) ↦ c6sub_pat_three k ]

def c6sub_pat_zero (i : Nat) : Bool ≔ match i [ zero. ↦ true. | suc. _ ↦ false. ]

def c6sub_pattern : C6SubIndex → Nat → Bool ≔ [
  | inr. _ ↦ _ ↦ true.
  | inl. (inr. _) ↦ c6sub_pat_even
  | inl. (inl. (inr. _)) ↦ c6sub_pat_three
  | inl. (inl. (inl. (inr. _))) ↦ c6sub_pat_zero
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

{` The class of a closed vector: d = 1 if s or s^5 is in, else 2 if s^2 or
   s^4 is in, else 3 if s^3 is in, else 6. `}
def c6sub_dclass (a1 a2 a3 a4 a5 : Bool) : C6SubIndex
  ≔ match a1 [
  | true. ↦ c6sub_c1
  | false. ↦ match a5 [
    | true. ↦ c6sub_c1
    | false. ↦ match a2 [
      | true. ↦ c6sub_c2
      | false. ↦ match a4 [
        | true. ↦ c6sub_c2
        | false. ↦ match a3 [ true. ↦ c6sub_c3 | false. ↦ c6sub_c6 ] ] ] ] ]

def c6sub_eqv (a0 a1 a2 a3 a4 a5 : Bool) (c : C6SubIndex) : Bool
  ≔ bits4_and (bits4_bool_eqb a0 (c6sub_pattern c zero.)) (bits4_and (bits4_bool_eqb a1 (c6sub_pattern c (suc. zero.))) (bits4_and (bits4_bool_eqb a2 (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb a3 (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb a4 (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb a5 (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))))))))

def c6sub_check (a0 a1 a2 a3 a4 a5 : Bool) : Bool
  ≔ bits4_implies (bits4_and a0 (c6sub_closedb a1 a2 a3 a4 a5)) (c6sub_eqv a0 a1 a2 a3 a4 a5 (c6sub_dclass a1 a2 a3 a4 a5))

{` The finite check over all 64 Boolean vectors. `}
def c6sub_check_all (a0 a1 a2 a3 a4 a5 : Bool) : Id Bool (c6sub_check a0 a1 a2 a3 a4 a5) true.
  ≔ match a0 [
  | false. ↦ refl (true. : Bool)
  | true. ↦ match a1 [
      | true. ↦ match a2 [
        | true. ↦ match a3 [
          | true. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ]
          | false. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ] ]
        | false. ↦ match a3 [
          | true. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ]
          | false. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ] ] ]
      | false. ↦ match a2 [
        | true. ↦ match a3 [
          | true. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ]
          | false. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ] ]
        | false. ↦ match a3 [
          | true. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ]
          | false. ↦ match a4 [
            | true. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ]
            | false. ↦ match a5 [
              | true. ↦ refl (true. : Bool)
              | false. ↦ refl (true. : Bool) ] ] ] ] ] ]

{` Reading off the six equations a_k = pattern(c)(k), k < 6. `}
def c6sub_eqv_index (f : Nat → Bool) (c : C6SubIndex)
  (h : Id Bool (c6sub_eqv (f zero.) (f (suc. zero.)) (f two) (f c6half_three) (f c6sub_four) (f c6half_five) c) true.)
  (k : Nat) (hk : Lt k c6half_six) : Id Bool (f k) (c6sub_pattern c k)
  ≔ let r0 ≔ h in
    let r1 ≔ bits4_and_right (bits4_bool_eqb (f zero.) (c6sub_pattern c zero.)) (bits4_and (bits4_bool_eqb (f (suc. zero.)) (c6sub_pattern c (suc. zero.))) (bits4_and (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))))))) r0 in
    let r2 ≔ bits4_and_right (bits4_bool_eqb (f (suc. zero.)) (c6sub_pattern c (suc. zero.))) (bits4_and (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))))))) r1 in
    let r3 ≔ bits4_and_right (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))))) r2 in
    let r4 ≔ bits4_and_right (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))))) r3 in
    let r5 ≔ bits4_and_right (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))) r4 in
    match k [
  | zero. ↦ bits4_bool_eqb_sound (f zero.) (c6sub_pattern c zero.) (bits4_and_left (bits4_bool_eqb (f zero.) (c6sub_pattern c zero.)) (bits4_and (bits4_bool_eqb (f (suc. zero.)) (c6sub_pattern c (suc. zero.))) (bits4_and (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))))))) r0)
  | suc. zero. ↦ bits4_bool_eqb_sound (f (suc. zero.)) (c6sub_pattern c (suc. zero.)) (bits4_and_left (bits4_bool_eqb (f (suc. zero.)) (c6sub_pattern c (suc. zero.))) (bits4_and (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))))))) r1)
  | suc. (suc. zero.) ↦ bits4_bool_eqb_sound (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.))) (bits4_and_left (bits4_bool_eqb (f (suc. (suc. zero.))) (c6sub_pattern c (suc. (suc. zero.)))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))))) r2)
  | suc. (suc. (suc. zero.)) ↦ bits4_bool_eqb_sound (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.)))) (bits4_and_left (bits4_bool_eqb (f (suc. (suc. (suc. zero.)))) (c6sub_pattern c (suc. (suc. (suc. zero.))))) (bits4_and (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))))) r3)
  | suc. (suc. (suc. (suc. zero.))) ↦ bits4_bool_eqb_sound (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.))))) (bits4_and_left (bits4_bool_eqb (f (suc. (suc. (suc. (suc. zero.))))) (c6sub_pattern c (suc. (suc. (suc. (suc. zero.)))))) (bits4_bool_eqb (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.))))))) r4)
  | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ bits4_bool_eqb_sound (f (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. zero.)))))) (r5)
  | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd (Id Bool (f (suc. (suc. (suc. (suc. (suc. (suc. n))))))) (c6sub_pattern c (suc. (suc. (suc. (suc. (suc. (suc. n)))))))) hk ]

{` Membership in the cyclic subgroup ⟨g⟩ (copies of module 1013's
   cyclic_subgroup_member_power / cyclic_subgroup_power_member, whose module
   imports the Sylow chain). `}
def c6sub_cyclic_member_power (b : Nat) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k (suc. b) → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (t : USym G)
  (r : Id (gset_underlying G (cyclic_subgroup_of_element b G g h hyp .gset))
     (gset_usym_act G (cyclic_subgroup_of_element b G g h hyp .gset) t (cyclic_subgroup_of_element b G g h hyp .point))
     (cyclic_subgroup_of_element b G g h hyp .point))
  : Mere (Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym G) t (usym_power G g k))))
  ≔ let m ≔ cyclic_mono_of_element b G g h hyp in
    let S ≔ cyclic_subgroup_of_element b G g h hyp in
    let C ≔ cyclic_group (suc. b) in
    let f ≔ cyclic_hom_of_element b G g h in
    let T ≔ Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym G) t (usym_power G g k))) in
    mere_rec (Σ (USym C) (c ↦ Id (USym G) t (usym_hom C G f c))) (Mere T) (mere_isprop T)
      (w ↦ let v ≔ cyclic_symmetry_power_index b (w .fst) in
        mere T (v .fst, (v .snd .fst,
          concat (USym G) t (usym_hom C G f (w .fst)) (usym_power G g (v .fst)) (w .snd)
            (concat (USym G) (usym_hom C G f (w .fst)) (usym_hom C G f (usym_power C (cyclic_group_generator b) (v .fst)))
              (usym_power G g (v .fst))
              (refl (usym_hom C G f) (inverse (USym C) (usym_power C (cyclic_group_generator b) (v .fst)) (w .fst) (v .snd .snd)))
              (cyclic_hom_generator_power b G g h (v .fst))))))
      (mono_preserves_symmetries G S m (inverse (GroupMonos G) (subgroup_to_mono G S) m (mono_subgroup_roundtrip G m)) t .fst r)

def c6sub_cyclic_power_member (b : Nat) (G : Group) (g : USym G)
  (h : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k (suc. b) → Id (USym G) (usym_power G g k) (usym_unit G) → Empty)
  (k : Nat)
  : Id (gset_underlying G (cyclic_subgroup_of_element b G g h hyp .gset))
      (gset_usym_act G (cyclic_subgroup_of_element b G g h hyp .gset) (usym_power G g k) (cyclic_subgroup_of_element b G g h hyp .point))
      (cyclic_subgroup_of_element b G g h hyp .point)
  ≔ let m ≔ cyclic_mono_of_element b G g h hyp in
    let S ≔ cyclic_subgroup_of_element b G g h hyp in
    let C ≔ cyclic_group (suc. b) in
    let f ≔ cyclic_hom_of_element b G g h in
    mono_preserves_symmetries G S m (inverse (GroupMonos G) (subgroup_to_mono G S) m (mono_subgroup_roundtrip G m))
      (usym_power G g k) .snd
      (mere (Σ (USym C) (c ↦ Id (USym G) (usym_power G g k) (usym_hom C G f c)))
        (usym_power C (cyclic_group_generator b) k,
         inverse (USym G) (usym_hom C G f (usym_power C (cyclic_group_generator b) k)) (usym_power G g k)
           (cyclic_hom_generator_power b G g h k)))

{` g^k = e for 0 < k < order would contradict the order 6 of s. `}
def c6sub_nontrivial (d m : Nat) (h0 : Lt zero. (mul d m)) (h1 : Lt (mul d m) c6half_six)
  (e : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow d) m) (usym_unit c6sub_group)) : Empty
  ≔ cyclic_group_generator_powers_nontrivial c6half_five (mul d m) (lt_to_book zero. (mul d m) h0)
      (lt_to_book (mul d m) c6half_six h1)
      (concat (USym c6sub_group) (c6sub_pow (mul d m)) (usym_power c6sub_group (c6sub_pow d) m) (usym_unit c6sub_group)
        (usym_power_mul c6sub_group c6sub_gen d m) e)

def c6sub_h1 : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) (usym_unit c6sub_group)
  ≔ concat (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_pow c6half_six) (usym_unit c6sub_group)
      (inverse (USym c6sub_group) (c6sub_pow c6half_six) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))
        (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
      (cyclic_group_generator_order c6half_five)

def c6sub_hyp1 (m : Nat) (h0 : BookLt zero. m) (hm : BookLt m (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))
  (e : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. zero.)) m) (usym_unit c6sub_group)) : Empty
  ≔ match m [
  | zero. ↦ absurd Empty (lt_from_book zero. zero. h0)
  | suc. zero. ↦ c6sub_nontrivial (suc. zero.) (suc. zero.) star. star. e
  | suc. (suc. zero.) ↦ c6sub_nontrivial (suc. zero.) (suc. (suc. zero.)) star. star. e
  | suc. (suc. (suc. zero.)) ↦ c6sub_nontrivial (suc. zero.) (suc. (suc. (suc. zero.))) star. star. e
  | suc. (suc. (suc. (suc. zero.))) ↦ c6sub_nontrivial (suc. zero.) (suc. (suc. (suc. (suc. zero.)))) star. star. e
  | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ c6sub_nontrivial (suc. zero.) (suc. (suc. (suc. (suc. (suc. zero.))))) star. star. e
  | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd Empty (lt_from_book (suc. (suc. (suc. (suc. (suc. (suc. n)))))) (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) hm) ]

def c6sub_h2 : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. zero.))) (suc. (suc. (suc. zero.)))) (usym_unit c6sub_group)
  ≔ concat (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. zero.))) (suc. (suc. (suc. zero.)))) (c6sub_pow c6half_six) (usym_unit c6sub_group)
      (inverse (USym c6sub_group) (c6sub_pow c6half_six) (usym_power c6sub_group (c6sub_pow (suc. (suc. zero.))) (suc. (suc. (suc. zero.))))
        (usym_power_mul c6sub_group c6sub_gen (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))))
      (cyclic_group_generator_order c6half_five)

def c6sub_hyp2 (m : Nat) (h0 : BookLt zero. m) (hm : BookLt m (suc. (suc. (suc. zero.))))
  (e : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. zero.))) m) (usym_unit c6sub_group)) : Empty
  ≔ match m [
  | zero. ↦ absurd Empty (lt_from_book zero. zero. h0)
  | suc. zero. ↦ c6sub_nontrivial (suc. (suc. zero.)) (suc. zero.) star. star. e
  | suc. (suc. zero.) ↦ c6sub_nontrivial (suc. (suc. zero.)) (suc. (suc. zero.)) star. star. e
  | suc. (suc. (suc. n)) ↦ absurd Empty (lt_from_book (suc. (suc. (suc. n))) (suc. (suc. (suc. zero.))) hm) ]

def c6sub_h3 : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. (suc. zero.)))) (suc. (suc. zero.))) (usym_unit c6sub_group)
  ≔ concat (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. (suc. zero.)))) (suc. (suc. zero.))) (c6sub_pow c6half_six) (usym_unit c6sub_group)
      (inverse (USym c6sub_group) (c6sub_pow c6half_six) (usym_power c6sub_group (c6sub_pow (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
        (usym_power_mul c6sub_group c6sub_gen (suc. (suc. (suc. zero.))) (suc. (suc. zero.))))
      (cyclic_group_generator_order c6half_five)

def c6sub_hyp3 (m : Nat) (h0 : BookLt zero. m) (hm : BookLt m (suc. (suc. zero.)))
  (e : Id (USym c6sub_group) (usym_power c6sub_group (c6sub_pow (suc. (suc. (suc. zero.)))) m) (usym_unit c6sub_group)) : Empty
  ≔ match m [
  | zero. ↦ absurd Empty (lt_from_book zero. zero. h0)
  | suc. zero. ↦ c6sub_nontrivial (suc. (suc. (suc. zero.))) (suc. zero.) star. star. e
  | suc. (suc. n) ↦ absurd Empty (lt_from_book (suc. (suc. n)) (suc. (suc. zero.)) hm) ]

def c6sub_h6 : Id (USym c6sub_group) (usym_power c6sub_group (usym_unit c6sub_group) (suc. zero.)) (usym_unit c6sub_group)
  ≔ usym_power_unit c6sub_group (suc. zero.)

def c6sub_hyp6 (m : Nat) (h0 : BookLt zero. m) (hm : BookLt m (suc. zero.))
  (e : Id (USym c6sub_group) (usym_power c6sub_group (usym_unit c6sub_group) m) (usym_unit c6sub_group)) : Empty
  ≔ match m [
  | zero. ↦ absurd Empty (lt_from_book zero. zero. h0)
  | suc. n ↦ absurd Empty (lt_from_book (suc. n) (suc. zero.) hm) ]

def c6sub_t1 : Subgroups c6sub_group ≔ cyclic_subgroup_of_element c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1

def c6sub_t2 : Subgroups c6sub_group ≔ cyclic_subgroup_of_element (suc. (suc. zero.)) c6sub_group (c6sub_pow two) c6sub_h2 c6sub_hyp2

def c6sub_t3 : Subgroups c6sub_group ≔ cyclic_subgroup_of_element (suc. zero.) c6sub_group (c6sub_pow c6half_three) c6sub_h3 c6sub_hyp3

def c6sub_t6 : Subgroups c6sub_group ≔ cyclic_subgroup_of_element zero. c6sub_group (usym_unit c6sub_group) c6sub_h6 c6sub_hyp6

{` T_c: the cyclic subgroup generated by s^d. `}
def c6sub_subgroup : C6SubIndex → Subgroups c6sub_group ≔ [
  | inr. _ ↦ c6sub_t1
  | inl. (inr. _) ↦ c6sub_t2
  | inl. (inl. (inr. _)) ↦ c6sub_t3
  | inl. (inl. (inl. (inr. _))) ↦ c6sub_t6
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

{` s^k (k < 6) fixes the point of T_c whenever d divides k. `}
def c6sub_pattern_member (c : C6SubIndex) (k : Nat) (hk : Lt k c6half_six) (h : Id Bool (c6sub_pattern c k) true.)
  : C6SubFixes (c6sub_subgroup c) (c6sub_pow k)
  ≔ match c [
  | inr. _ ↦ match k [
    | zero. ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) zero.) (c6sub_pow zero.)
        (inverse (USym c6sub_group) (c6sub_pow zero.) (usym_power c6sub_group (c6sub_pow (suc. zero.)) zero.) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) zero.))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 zero.)
    | suc. zero. ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. zero.)) (c6sub_pow (suc. zero.))
        (inverse (USym c6sub_group) (c6sub_pow (suc. zero.)) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. zero.)) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. zero.)))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 (suc. zero.))
    | suc. (suc. zero.) ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. zero.))) (c6sub_pow (suc. (suc. zero.)))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. zero.))) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. zero.))) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. (suc. zero.))))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 (suc. (suc. zero.)))
    | suc. (suc. (suc. zero.)) ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. zero.)))) (c6sub_pow (suc. (suc. (suc. zero.))))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. (suc. zero.)))) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. zero.)))) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. (suc. (suc. zero.)))))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 (suc. (suc. (suc. zero.))))
    | suc. (suc. (suc. (suc. zero.))) ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. zero.))))) (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. (suc. (suc. zero.))))) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. zero.))))) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. (suc. (suc. (suc. zero.))))))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 (suc. (suc. (suc. (suc. zero.)))))
    | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ c6sub_fixes_path c6sub_t1 (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.)))))) (usym_power c6sub_group (c6sub_pow (suc. zero.)) (suc. (suc. (suc. (suc. (suc. zero.)))))) (usym_power_mul c6sub_group c6sub_gen (suc. zero.) (suc. (suc. (suc. (suc. (suc. zero.)))))))
        (c6sub_cyclic_power_member c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 (suc. (suc. (suc. (suc. (suc. zero.))))))
    | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd (C6SubFixes c6sub_t1 (c6sub_pow (suc. (suc. (suc. (suc. (suc. (suc. n)))))))) hk ]
  | inl. (inr. _) ↦ match k [
    | zero. ↦ c6sub_fixes_path c6sub_t2 (usym_power c6sub_group (c6sub_pow two) zero.) (c6sub_pow zero.)
        (inverse (USym c6sub_group) (c6sub_pow zero.) (usym_power c6sub_group (c6sub_pow two) zero.) (usym_power_mul c6sub_group c6sub_gen (suc. (suc. zero.)) zero.))
        (c6sub_cyclic_power_member (suc. (suc. zero.)) c6sub_group (c6sub_pow two) c6sub_h2 c6sub_hyp2 zero.)
    | suc. zero. ↦ absurd (C6SubFixes c6sub_t2 (c6sub_pow (suc. zero.))) (bool_encode false. true. h)
    | suc. (suc. zero.) ↦ c6sub_fixes_path c6sub_t2 (usym_power c6sub_group (c6sub_pow two) (suc. zero.)) (c6sub_pow (suc. (suc. zero.)))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. zero.))) (usym_power c6sub_group (c6sub_pow two) (suc. zero.)) (usym_power_mul c6sub_group c6sub_gen (suc. (suc. zero.)) (suc. zero.)))
        (c6sub_cyclic_power_member (suc. (suc. zero.)) c6sub_group (c6sub_pow two) c6sub_h2 c6sub_hyp2 (suc. zero.))
    | suc. (suc. (suc. zero.)) ↦ absurd (C6SubFixes c6sub_t2 (c6sub_pow (suc. (suc. (suc. zero.))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. zero.))) ↦ c6sub_fixes_path c6sub_t2 (usym_power c6sub_group (c6sub_pow two) (suc. (suc. zero.))) (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. (suc. (suc. zero.))))) (usym_power c6sub_group (c6sub_pow two) (suc. (suc. zero.))) (usym_power_mul c6sub_group c6sub_gen (suc. (suc. zero.)) (suc. (suc. zero.))))
        (c6sub_cyclic_power_member (suc. (suc. zero.)) c6sub_group (c6sub_pow two) c6sub_h2 c6sub_hyp2 (suc. (suc. zero.)))
    | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ absurd (C6SubFixes c6sub_t2 (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd (C6SubFixes c6sub_t2 (c6sub_pow (suc. (suc. (suc. (suc. (suc. (suc. n)))))))) hk ]
  | inl. (inl. (inr. _)) ↦ match k [
    | zero. ↦ c6sub_fixes_path c6sub_t3 (usym_power c6sub_group (c6sub_pow c6half_three) zero.) (c6sub_pow zero.)
        (inverse (USym c6sub_group) (c6sub_pow zero.) (usym_power c6sub_group (c6sub_pow c6half_three) zero.) (usym_power_mul c6sub_group c6sub_gen (suc. (suc. (suc. zero.))) zero.))
        (c6sub_cyclic_power_member (suc. zero.) c6sub_group (c6sub_pow c6half_three) c6sub_h3 c6sub_hyp3 zero.)
    | suc. zero. ↦ absurd (C6SubFixes c6sub_t3 (c6sub_pow (suc. zero.))) (bool_encode false. true. h)
    | suc. (suc. zero.) ↦ absurd (C6SubFixes c6sub_t3 (c6sub_pow (suc. (suc. zero.)))) (bool_encode false. true. h)
    | suc. (suc. (suc. zero.)) ↦ c6sub_fixes_path c6sub_t3 (usym_power c6sub_group (c6sub_pow c6half_three) (suc. zero.)) (c6sub_pow (suc. (suc. (suc. zero.))))
        (inverse (USym c6sub_group) (c6sub_pow (suc. (suc. (suc. zero.)))) (usym_power c6sub_group (c6sub_pow c6half_three) (suc. zero.)) (usym_power_mul c6sub_group c6sub_gen (suc. (suc. (suc. zero.))) (suc. zero.)))
        (c6sub_cyclic_power_member (suc. zero.) c6sub_group (c6sub_pow c6half_three) c6sub_h3 c6sub_hyp3 (suc. zero.))
    | suc. (suc. (suc. (suc. zero.))) ↦ absurd (C6SubFixes c6sub_t3 (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ absurd (C6SubFixes c6sub_t3 (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd (C6SubFixes c6sub_t3 (c6sub_pow (suc. (suc. (suc. (suc. (suc. (suc. n)))))))) hk ]
  | inl. (inl. (inl. (inr. _))) ↦ match k [
    | zero. ↦ c6sub_cyclic_power_member zero. c6sub_group (usym_unit c6sub_group) c6sub_h6 c6sub_hyp6 zero.
    | suc. zero. ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. zero.))) (bool_encode false. true. h)
    | suc. (suc. zero.) ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. (suc. zero.)))) (bool_encode false. true. h)
    | suc. (suc. (suc. zero.)) ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. (suc. (suc. zero.))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. zero.))) ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. (suc. zero.)))) ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))) (bool_encode false. true. h)
    | suc. (suc. (suc. (suc. (suc. (suc. n))))) ↦ absurd (C6SubFixes c6sub_t6 (c6sub_pow (suc. (suc. (suc. (suc. (suc. (suc. n)))))))) hk ]
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

{` ⟨g⟩ ⊆ S as soon as g fixes the point of S. `}
def c6sub_le_cyclic (b : Nat) (g : USym c6sub_group) (h : Id (USym c6sub_group) (usym_power c6sub_group g (suc. b)) (usym_unit c6sub_group))
  (hyp : (k : Nat) → BookLt zero. k → BookLt k (suc. b) → Id (USym c6sub_group) (usym_power c6sub_group g k) (usym_unit c6sub_group) → Empty)
  (S : Subgroups c6sub_group) (hg : C6SubFixes S g)
  : SubgroupLe c6sub_group (cyclic_subgroup_of_element b c6sub_group g h hyp) S
  ≔ t r ↦ mere_rec (Σ Nat (k ↦ Product (BookLt k (suc. b)) (Id (USym c6sub_group) t (usym_power c6sub_group g k))))
      (C6SubFixes S t) (gset_underlying_set c6sub_group (S .gset) (gset_usym_act c6sub_group (S .gset) t (S .point)) (S .point))
      (w ↦ c6sub_fixes_path S (usym_power c6sub_group g (w .fst)) t
        (inverse (USym c6sub_group) t (usym_power c6sub_group g (w .fst)) (w .snd .snd))
        (c6sub_fix_power c6sub_group (S .gset) (S .point) g hg (w .fst)))
      (c6sub_cyclic_member_power b c6sub_group g h hyp t r)

def c6sub_le_of_pattern (c : C6SubIndex) (S : Subgroups c6sub_group)
  (memb : (k : Nat) → Lt k c6half_six → Id Bool (c6sub_pattern c k) true. → C6SubFixes S (c6sub_pow k))
  : SubgroupLe c6sub_group (c6sub_subgroup c) S
  ≔ match c [
  | inr. _ ↦ c6sub_le_cyclic c6half_five (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1 S (memb (suc. zero.) star. (refl (true. : Bool)))
  | inl. (inr. _) ↦ c6sub_le_cyclic (suc. (suc. zero.)) (c6sub_pow two) c6sub_h2 c6sub_hyp2 S (memb two star. (refl (true. : Bool)))
  | inl. (inl. (inr. _)) ↦ c6sub_le_cyclic (suc. zero.) (c6sub_pow c6half_three) c6sub_h3 c6sub_hyp3 S (memb c6half_three star. (refl (true. : Bool)))
  | inl. (inl. (inl. (inr. _))) ↦ c6sub_le_cyclic zero. (usym_unit c6sub_group) c6sub_h6 c6sub_hyp6 S (gset_act_unit c6sub_group (S .gset) (S .point))
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_le_to_pattern (S : Subgroups c6sub_group) (c : C6SubIndex)
  (memb : (k : Nat) → Lt k c6half_six → C6SubFixes S (c6sub_pow k) → Id Bool (c6sub_pattern c k) true.)
  : SubgroupLe c6sub_group S (c6sub_subgroup c)
  ≔ t r ↦
    let w ≔ cyclic_symmetry_power_index c6half_five t in
    let hk : Lt (w .fst) c6half_six ≔ lt_from_book (w .fst) c6half_six (w .snd .fst) in
    c6sub_fixes_path (c6sub_subgroup c) (c6sub_pow (w .fst)) t (w .snd .snd)
      (c6sub_pattern_member c (w .fst) hk
        (memb (w .fst) hk
          (c6sub_fixes_path S t (c6sub_pow (w .fst)) (inverse (USym c6sub_group) (c6sub_pow (w .fst)) t (w .snd .snd)) r)))

def c6sub_pair_bool (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S) (i j r : Nat)
  (p : Id (USym c6sub_group) (c6sub_pow (add i j)) (c6sub_pow r))
  : Id Bool (c6sub_imp (c6sub_bv S dS i) (c6sub_bv S dS j) (c6sub_bv S dS r)) true.
  ≔ c6sub_bool_imp (C6SubFixes S (c6sub_pow i)) (C6SubFixes S (c6sub_pow j)) (C6SubFixes S (c6sub_pow r))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow i) (S .point)) (S .point))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow j) (S .point)) (S .point))
      (dS (gset_usym_act c6sub_group (S .gset) (c6sub_pow r) (S .point)) (S .point))
      (c6sub_pair S i j r p)

def c6sub_closed_true (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S)
  : Id Bool (c6sub_closedb (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) true.
  ≔ bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))))))))))))
      (c6sub_pair_bool S dS (suc. zero.) (suc. zero.) (suc. (suc. zero.)) (refl (c6sub_pow (suc. (suc. zero.)))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.))))))))))))
      (c6sub_pair_bool S dS (suc. (suc. zero.)) (suc. zero.) (suc. (suc. (suc. zero.))) (refl (c6sub_pow (suc. (suc. (suc. zero.))))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))))))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. zero.))) (suc. zero.) (suc. (suc. (suc. (suc. zero.)))) (refl (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.))))))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. (suc. zero.)))) (suc. zero.) (suc. (suc. (suc. (suc. (suc. zero.))))) (refl (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. (suc. (suc. zero.)))) (c6sub_period (suc. (suc. (suc. (suc. zero.))))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. (suc. zero.))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.))))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. (suc. zero.))) (c6sub_period (suc. (suc. (suc. zero.)))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. zero.)) (c6sub_period (suc. (suc. zero.))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) (c6sub_bv S dS (suc. zero.))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.))))))
      (c6sub_pair_bool S dS (suc. (suc. zero.)) (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. zero.) (c6sub_period (suc. zero.)))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.)))))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))))
      (c6sub_pair_bool S dS (suc. (suc. zero.)) (suc. (suc. zero.)) (suc. (suc. (suc. (suc. zero.)))) (refl (c6sub_pow (suc. (suc. (suc. (suc. zero.)))))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. zero.)))) (bits4_and (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)) (c6sub_period (suc. (suc. zero.))))
      (bits4_and_intro (c6sub_imp (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) (c6sub_imp (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. zero.)))
      (c6sub_pair_bool S dS (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. zero.))))) (refl (c6sub_pow (suc. (suc. (suc. (suc. (suc. zero.))))))))
      (c6sub_pair_bool S dS (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. zero.))) (suc. zero.) (c6sub_period (suc. zero.)))))))))))))

{` The class of a decidable subgroup. `}
def c6sub_class (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S) : C6SubIndex
  ≔ c6sub_dclass (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))

{` Claim at actions.tex 897, classification: every decidable subgroup of
   C_6 is one of the four T_c. `}
def c6sub_classification (S : Subgroups c6sub_group) (dS : IsDecidableSubgroup c6sub_group S)
  : Id (Subgroups c6sub_group) S (c6sub_subgroup (c6sub_class S dS))
  ≔ let f ≔ c6sub_bv S dS in
    let c ≔ c6sub_class S dS in
    let h0 : Id Bool (f zero.) true. ≔ c6sub_bv_complete S dS zero. (gset_act_unit c6sub_group (S .gset) (S .point)) in
    let a ≔ bits4_and (c6sub_bv S dS zero.) (c6sub_closedb (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) in
    let heqv : Id Bool (c6sub_eqv (c6sub_bv S dS zero.) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) c) true.
      ≔ bits4_implies_mp a (c6sub_eqv (c6sub_bv S dS zero.) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))) c)
          (c6sub_check_all (c6sub_bv S dS zero.) (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.)))))))
          (bits4_and_intro (c6sub_bv S dS zero.) (c6sub_closedb (c6sub_bv S dS (suc. zero.)) (c6sub_bv S dS (suc. (suc. zero.))) (c6sub_bv S dS (suc. (suc. (suc. zero.)))) (c6sub_bv S dS (suc. (suc. (suc. (suc. zero.))))) (c6sub_bv S dS (suc. (suc. (suc. (suc. (suc. zero.))))))) h0 (c6sub_closed_true S dS)) in
    let idx : (k : Nat) → Lt k c6half_six → Id Bool (f k) (c6sub_pattern c k) ≔ c6sub_eqv_index f c heqv in
    subgroup_le_antisym c6sub_group S (c6sub_subgroup c)
      (c6sub_le_to_pattern S c
        (k hk x ↦ concat Bool (c6sub_pattern c k) (f k) true. (inverse Bool (f k) (c6sub_pattern c k) (idx k hk))
          (c6sub_bv_complete S dS k x)))
      (c6sub_le_of_pattern c S
        (k hk hp ↦ c6sub_bv_sound S dS k (concat Bool (f k) (c6sub_pattern c k) true. (idx k hk) hp)))

{` The underlying group of T_c is C_k (6 = d·k). `}
def c6sub_subgroup_group_path (c : C6SubIndex)
  : Id Group (subgroup_group c6sub_group (c6sub_subgroup c)) (cyclic_group (c6sub_cofactor c))
  ≔ match c [
  | inr. _ ↦ cyclic_subgroup_group_path c6half_five c6sub_group (c6sub_pow (suc. zero.)) c6sub_h1 c6sub_hyp1
  | inl. (inr. _) ↦ cyclic_subgroup_group_path (suc. (suc. zero.)) c6sub_group (c6sub_pow two) c6sub_h2 c6sub_hyp2
  | inl. (inl. (inr. _)) ↦ cyclic_subgroup_group_path (suc. zero.) c6sub_group (c6sub_pow c6half_three) c6sub_h3 c6sub_hyp3
  | inl. (inl. (inl. (inr. _))) ↦ cyclic_subgroup_group_path zero. c6sub_group (usym_unit c6sub_group) c6sub_h6 c6sub_hyp6
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_cyclic_finite (c : C6SubIndex) : IsFiniteGroup (cyclic_group (c6sub_cofactor c))
  ≔ match c [
  | inr. _ ↦ cyclic_group_finite c6half_five
  | inl. (inr. _) ↦ cyclic_group_finite (suc. (suc. zero.))
  | inl. (inl. (inr. _)) ↦ cyclic_group_finite (suc. zero.)
  | inl. (inl. (inl. (inr. _))) ↦ cyclic_group_finite zero.
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_cyclic_card (c : C6SubIndex)
  : Id Nat (group_card (cyclic_group (c6sub_cofactor c)) (c6sub_cyclic_finite c)) (c6sub_cofactor c)
  ≔ match c [
  | inr. _ ↦ cyclic_group_card c6half_five (cyclic_group_finite c6half_five)
  | inl. (inr. _) ↦ cyclic_group_card (suc. (suc. zero.)) (cyclic_group_finite (suc. (suc. zero.)))
  | inl. (inl. (inr. _)) ↦ cyclic_group_card (suc. zero.) (cyclic_group_finite (suc. zero.))
  | inl. (inl. (inl. (inr. _))) ↦ cyclic_group_card zero. (cyclic_group_finite zero.)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def c6sub_subgroup_finite (c : C6SubIndex) : IsFiniteGroup (subgroup_group c6sub_group (c6sub_subgroup c))
  ≔ group_finite_path (cyclic_group (c6sub_cofactor c)) (subgroup_group c6sub_group (c6sub_subgroup c))
      (inverse Group (subgroup_group c6sub_group (c6sub_subgroup c)) (cyclic_group (c6sub_cofactor c)) (c6sub_subgroup_group_path c))
      (c6sub_cyclic_finite c)

def c6sub_subgroup_card (c : C6SubIndex) (h : IsFiniteGroup (subgroup_group c6sub_group (c6sub_subgroup c)))
  : Id Nat (group_card (subgroup_group c6sub_group (c6sub_subgroup c)) h) (c6sub_cofactor c)
  ≔ concat Nat (group_card (subgroup_group c6sub_group (c6sub_subgroup c)) h)
      (group_card (cyclic_group (c6sub_cofactor c)) (c6sub_cyclic_finite c)) (c6sub_cofactor c)
      (group_card_path (subgroup_group c6sub_group (c6sub_subgroup c)) (cyclic_group (c6sub_cofactor c)) (c6sub_subgroup_group_path c)
        h (c6sub_cyclic_finite c))
      (c6sub_cyclic_card c)

def c6sub_cofactor_injective (c c' : C6SubIndex) (e : Id Nat (c6sub_cofactor c) (c6sub_cofactor c')) : Id C6SubIndex c c'
  ≔ match c [
  | inr. star. ↦ match c' [
    | inr. star. ↦ refl c6sub_c1
    | inl. (inr. star.) ↦ absurd (Id C6SubIndex c6sub_c1 c6sub_c2) (nat_encode (c6sub_cofactor c6sub_c1) (c6sub_cofactor c6sub_c2) e)
    | inl. (inl. (inr. star.)) ↦ absurd (Id C6SubIndex c6sub_c1 c6sub_c3) (nat_encode (c6sub_cofactor c6sub_c1) (c6sub_cofactor c6sub_c3) e)
    | inl. (inl. (inl. (inr. star.))) ↦ absurd (Id C6SubIndex c6sub_c1 c6sub_c6) (nat_encode (c6sub_cofactor c6sub_c1) (c6sub_cofactor c6sub_c6) e)
    | inl. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inr. star.) ↦ match c' [
    | inr. star. ↦ absurd (Id C6SubIndex c6sub_c2 c6sub_c1) (nat_encode (c6sub_cofactor c6sub_c2) (c6sub_cofactor c6sub_c1) e)
    | inl. (inr. star.) ↦ refl c6sub_c2
    | inl. (inl. (inr. star.)) ↦ absurd (Id C6SubIndex c6sub_c2 c6sub_c3) (nat_encode (c6sub_cofactor c6sub_c2) (c6sub_cofactor c6sub_c3) e)
    | inl. (inl. (inl. (inr. star.))) ↦ absurd (Id C6SubIndex c6sub_c2 c6sub_c6) (nat_encode (c6sub_cofactor c6sub_c2) (c6sub_cofactor c6sub_c6) e)
    | inl. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inr. star.)) ↦ match c' [
    | inr. star. ↦ absurd (Id C6SubIndex c6sub_c3 c6sub_c1) (nat_encode (c6sub_cofactor c6sub_c3) (c6sub_cofactor c6sub_c1) e)
    | inl. (inr. star.) ↦ absurd (Id C6SubIndex c6sub_c3 c6sub_c2) (nat_encode (c6sub_cofactor c6sub_c3) (c6sub_cofactor c6sub_c2) e)
    | inl. (inl. (inr. star.)) ↦ refl c6sub_c3
    | inl. (inl. (inl. (inr. star.))) ↦ absurd (Id C6SubIndex c6sub_c3 c6sub_c6) (nat_encode (c6sub_cofactor c6sub_c3) (c6sub_cofactor c6sub_c6) e)
    | inl. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inl. (inr. star.))) ↦ match c' [
    | inr. star. ↦ absurd (Id C6SubIndex c6sub_c6 c6sub_c1) (nat_encode (c6sub_cofactor c6sub_c6) (c6sub_cofactor c6sub_c1) e)
    | inl. (inr. star.) ↦ absurd (Id C6SubIndex c6sub_c6 c6sub_c2) (nat_encode (c6sub_cofactor c6sub_c6) (c6sub_cofactor c6sub_c2) e)
    | inl. (inl. (inr. star.)) ↦ absurd (Id C6SubIndex c6sub_c6 c6sub_c3) (nat_encode (c6sub_cofactor c6sub_c6) (c6sub_cofactor c6sub_c3) e)
    | inl. (inl. (inl. (inr. star.))) ↦ refl c6sub_c6
    | inl. (inl. (inl. (inl. e))) ↦ match e [] ]
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

{` Distinct factorizations give distinct subgroups (the orders k differ). `}
def c6sub_subgroup_injective (c c' : C6SubIndex) (p : Id (Subgroups c6sub_group) (c6sub_subgroup c) (c6sub_subgroup c'))
  : Id C6SubIndex c c'
  ≔ let H ≔ subgroup_group c6sub_group (c6sub_subgroup c) in
    let H' ≔ subgroup_group c6sub_group (c6sub_subgroup c') in
    c6sub_cofactor_injective c c'
      (concat Nat (c6sub_cofactor c) (group_card H (c6sub_subgroup_finite c)) (c6sub_cofactor c')
        (inverse Nat (group_card H (c6sub_subgroup_finite c)) (c6sub_cofactor c) (c6sub_subgroup_card c (c6sub_subgroup_finite c)))
        (concat Nat (group_card H (c6sub_subgroup_finite c)) (group_card H' (c6sub_subgroup_finite c')) (c6sub_cofactor c')
          (group_card_path H H' (refl ((S ↦ subgroup_group c6sub_group S) : Subgroups c6sub_group → Group) p)
            (c6sub_subgroup_finite c) (c6sub_subgroup_finite c'))
          (c6sub_subgroup_card c' (c6sub_subgroup_finite c'))))

def c6sub_subgroup_decidable (c : C6SubIndex) : IsDecidableSubgroup c6sub_group (c6sub_subgroup c)
  ≔ subgroup_gset_decidable_equality c6sub_group (cyclic_group_finite c6half_five) (c6sub_subgroup c) (c6sub_subgroup_finite c)

def c6sub_index_finite (c : C6SubIndex) : IsFiniteGSet c6sub_group (c6sub_subgroup c .gset)
  ≔ subgroup_gset_finite c6sub_group (cyclic_group_finite c6half_five) (c6sub_subgroup c) (c6sub_subgroup_finite c)

{` The underlying set X(sh) of T_c has d elements (Lagrange counting). `}
def c6sub_index_card (c : C6SubIndex)
  : Id Nat (gset_card c6sub_group (c6sub_subgroup c .gset) (c6sub_index_finite c)) (c6sub_divisor c)
  ≔ let G ≔ c6sub_group in
    let hG ≔ cyclic_group_finite c6half_five in
    let T ≔ c6sub_subgroup c in
    let hT ≔ c6sub_subgroup_finite c in
    let i ≔ gset_card G (T .gset) (c6sub_index_finite c) in
    let k ≔ c6sub_cofactor c in
    let d ≔ c6sub_divisor c in
    let n ≔ group_card (subgroup_group G T) hT in
    let e1 : Id Nat (mul i k) c6half_six
      ≔ concat Nat (mul i k) (mul i n) c6half_six
          (refl (mul i) (inverse Nat n k (c6sub_subgroup_card c hT)))
          (concat Nat (mul i n) (group_card G hG) c6half_six
            (inverse Nat (group_card G hG) (mul i n) (lagrange_counting G hG T hT))
            (cyclic_group_card c6half_five hG)) in
    let e2 : Id Nat (mul k i) (mul k d)
      ≔ concat Nat (mul k i) (mul i k) (mul k d) (mul_comm k i)
          (concat Nat (mul i k) c6half_six (mul k d) e1
            (inverse Nat (mul k d) c6half_six
              (concat Nat (mul k d) (mul d k) c6half_six (mul_comm k d) (c6sub_factorization c)))) in
    fingp_mul_cancel_left k i d (c6sub_cofactor_positive c) e2

def c6sub_decidable_prop (S : Subgroups c6sub_group) : isProp (IsDecidableSubgroup c6sub_group S)
  ≔ decidable_equality_prop (gset_underlying c6sub_group (S .gset)) (gset_underlying_set c6sub_group (S .gset))

{` Decidable subgroups of C_6 ≃ factorizations of 6 (Fin 4). `}
def c6sub_decidable_subgroups_equiv : Equiv (Σ (Subgroups c6sub_group) (IsDecidableSubgroup c6sub_group)) C6SubIndex
  ≔ quasi_inverse_equiv (Σ (Subgroups c6sub_group) (IsDecidableSubgroup c6sub_group)) C6SubIndex
      (u ↦ c6sub_class (u .fst) (u .snd))
      (c ↦ (c6sub_subgroup c, c6sub_subgroup_decidable c))
      (u ↦ subtype_equal (Subgroups c6sub_group) (IsDecidableSubgroup c6sub_group) c6sub_decidable_prop
        (c6sub_subgroup (c6sub_class (u .fst) (u .snd)), c6sub_subgroup_decidable (c6sub_class (u .fst) (u .snd))) u
        (inverse (Subgroups c6sub_group) (u .fst) (c6sub_subgroup (c6sub_class (u .fst) (u .snd)))
          (c6sub_classification (u .fst) (u .snd))))
      (c ↦ inverse C6SubIndex c (c6sub_class (c6sub_subgroup c) (c6sub_subgroup_decidable c))
        (c6sub_subgroup_injective c (c6sub_class (c6sub_subgroup c) (c6sub_subgroup_decidable c))
          (c6sub_classification (c6sub_subgroup c) (c6sub_subgroup_decidable c))))

{` The whole classification as one statement about a group H, so that it can
   be transported to the book's C_6 = cyclic_group_fin 5. `}
def C6SubgroupClassification (H : Group) : Type
  ≔ Σ (C6SubIndex → Subgroups H) (T ↦
      Product ((c : C6SubIndex) → IsDecidableSubgroup H (T c))
      (Product ((c : C6SubIndex) → Id Group (subgroup_group H (T c)) (cyclic_group (c6sub_cofactor c)))
      (Product ((S : Subgroups H) → IsDecidableSubgroup H S → Σ C6SubIndex (c ↦ Id (Subgroups H) S (T c)))
      (Product ((c c' : C6SubIndex) → Id (Subgroups H) (T c) (T c') → Id C6SubIndex c c')
        ((c : C6SubIndex) → Σ (IsFiniteGSet H (T c .gset)) (h ↦ Id Nat (gset_card H (T c .gset) h) (c6sub_divisor c)))))))

def c6sub_classification_package : C6SubgroupClassification c6sub_group
  ≔ (c6sub_subgroup,
     (c6sub_subgroup_decidable,
      (c6sub_subgroup_group_path,
       (S dS ↦ (c6sub_class S dS, c6sub_classification S dS),
        (c6sub_subgroup_injective,
         c ↦ (c6sub_index_finite c, c6sub_index_card c))))))

def c6sub_book_path : Id Group c6sub_group c6half_group
  ≔ inverse Group c6half_group c6sub_group (cyclic_group_fin_path c6half_five)

{` The same for the book's C_6 = Aut_Cyc(Fin 6, s). `}
def c6sub_book_classification : C6SubgroupClassification c6half_group
  ≔ transport Group C6SubgroupClassification c6sub_group c6half_group c6sub_book_path c6sub_classification_package

def c6sub_book_equiv : Equiv (Σ (Subgroups c6half_group) (IsDecidableSubgroup c6half_group)) C6SubIndex
  ≔ transport Group (H ↦ Equiv (Σ (Subgroups H) (IsDecidableSubgroup H)) C6SubIndex) c6sub_group c6half_group c6sub_book_path
      c6sub_decidable_subgroups_equiv

{` Litmus: the book's subgroup (X/2, [0]) of exa:C3subC6 (underlying group
   C_3) is the factorization 6 = 2·3. `}
def c6sub_half_group_path : Id Group (cyclic_group c6half_three) (subgroup_group c6half_group c6half_subgroup)
  ≔ group_path_from_pointed_equiv (cyclic_group c6half_three) (subgroup_group c6half_group c6half_subgroup) c6half_pointed_equiv

def c6sub_cyclic_three_index (c : C6SubIndex) (p : Id Group (cyclic_group c6half_three) (cyclic_group (c6sub_cofactor c)))
  : Id C6SubIndex c c6sub_c2
  ≔ let h3 ≔ cyclic_group_finite (suc. (suc. zero.)) in
    let K ≔ cyclic_group (c6sub_cofactor c) in
    c6sub_cofactor_injective c c6sub_c2
      (concat Nat (c6sub_cofactor c) (group_card K (c6sub_cyclic_finite c)) c6half_three
        (inverse Nat (group_card K (c6sub_cyclic_finite c)) (c6sub_cofactor c) (c6sub_cyclic_card c))
        (concat Nat (group_card K (c6sub_cyclic_finite c)) (group_card (cyclic_group c6half_three) h3) c6half_three
          (inverse Nat (group_card (cyclic_group c6half_three) h3) (group_card K (c6sub_cyclic_finite c))
            (group_card_path (cyclic_group c6half_three) K p h3 (c6sub_cyclic_finite c)))
          (cyclic_group_card (suc. (suc. zero.)) h3)))

def c6sub_book_half_index
  : Id C6SubIndex (c6sub_book_classification .snd .snd .snd .fst c6half_subgroup c6half_subgroup_decidable .fst) c6sub_c2
  ≔ let P ≔ c6sub_book_classification in
    let w ≔ P .snd .snd .snd .fst c6half_subgroup c6half_subgroup_decidable in
    c6sub_cyclic_three_index (w .fst)
      (concat Group (cyclic_group c6half_three) (subgroup_group c6half_group c6half_subgroup)
        (cyclic_group (c6sub_cofactor (w .fst)))
        c6sub_half_group_path
        (concat Group (subgroup_group c6half_group c6half_subgroup) (subgroup_group c6half_group (P .fst (w .fst)))
          (cyclic_group (c6sub_cofactor (w .fst)))
          (refl ((S ↦ subgroup_group c6half_group S) : Subgroups c6half_group → Group) (w .snd))
          (P .snd .snd .fst (w .fst))))
