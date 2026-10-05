export "1042-c2-power-abstract-models"

{` Chapter 10, rem:noofsubgps (fingp.tex 35-40), small cases of
   OEIS A006116 (1, 2, 5, 16, 67, ...): C_2^n = power_group (Fin n) C_2 has
   1, 2 and 5 decidable subgroups for n = 0, 1, 2
   (c2_power_decidable_subgroups_count_zero / _one / _two). Each count is
   stated for an arbitrary finiteness proof of
   Σ (S : Sub(C_2^n)) isDecidable(S) (one exists by
   decidable_subgroups_finite, module 1041).

   Proof: decidable subgroups ≃ Bool-valued abstract subgroups of
   abstr(C_2^n) (module 1041) ≃ those of the computational model (module
   1042), and these are enumerated: on Unit only A = true; on (Bool, xor)
   A is determined by A(true) (the subgroups 1 and C_2); on Bool × Bool a
   Bool-valued abstract subgroup is determined by the values (p, q, r) at
   (1,0), (0,1), (1,1) subject to p ∧ q ⇒ r, p ∧ r ⇒ q, q ∧ r ⇒ p, i.e. one
   of 000, 100, 010, 001, 111 (the trivial subgroup, the three subgroups of
   order 2 and the whole group). `}

{` n = 0. `}
def c2abs_unit_closed_equiv : Equiv (ClosedBoolSubsets unit_abstract_group) (Fin (suc. zero.))
  ≔ let AG ≔ unit_abstract_group in
    let full : ClosedBoolSubsets AG
      ≔ (_ ↦ true., (x ↦ bool_set true. true., (refl (true. : Bool), (x y _ _ ↦ refl (true. : Bool), x _ ↦ refl (true. : Bool))))) in
    quasi_inverse_equiv (ClosedBoolSubsets AG) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ full)
      (P ↦ closed_bool_subsets_path AG full P
        (x ↦ match x [ star. ↦ inverse Bool (P .fst star.) true. (P .snd .snd .fst) ]))
      (i ↦ match i [ inl. e ↦ match e [] | inr. u ↦ inr. (unit_prop star. u) ])

{` n = 1. `}
def c2abs_bool_subset (b x : Bool) : Bool ≔ match x [ false. ↦ true. | true. ↦ b ]

def c2abs_bool_subset_mul (b x y : Bool) (hx : Id Bool (c2abs_bool_subset b x) true.)
  (hy : Id Bool (c2abs_bool_subset b y) true.) : Id Bool (c2abs_bool_subset b (bool_xor x y)) true.
  ≔ match x, y [
    | false., false. ↦ refl (true. : Bool)
    | false., true. ↦ hy
    | true., false. ↦ hx
    | true., true. ↦ refl (true. : Bool) ]

def c2abs_bool_closed (b : Bool) : ClosedBoolSubsets c2abs_bool
  ≔ (c2abs_bool_subset b,
     (x ↦ bool_set (c2abs_bool_subset b x) true.,
      (refl (true. : Bool), (x y hx hy ↦ c2abs_bool_subset_mul b x y hx hy, x h ↦ h))))

def c2abs_bool_closed_equiv : Equiv (ClosedBoolSubsets c2abs_bool) Bool
  ≔ quasi_inverse_equiv (ClosedBoolSubsets c2abs_bool) Bool (P ↦ P .fst true.) c2abs_bool_closed
      (P ↦ closed_bool_subsets_path c2abs_bool (c2abs_bool_closed (P .fst true.)) P
        (x ↦ match x [
          | false. ↦ inverse Bool (P .fst false.) true. (P .snd .snd .fst)
          | true. ↦ refl (P .fst true.) ]))
      (b ↦ refl b)

{` n = 2. Codes (p, q, r) of Bool-valued abstract subgroups of Bool × Bool. `}
def c2sq_ok (p q r : Bool) : Bool
  ≔ match p, q, r [
    | false., false., false. ↦ true.
    | true., false., false. ↦ true.
    | false., true., false. ↦ true.
    | false., false., true. ↦ true.
    | true., true., true. ↦ true.
    | true., true., false. ↦ false.
    | true., false., true. ↦ false.
    | false., true., true. ↦ false. ]

def C2sqCode : Type ≔ Σ (Product Bool (Product Bool Bool)) (c ↦ Id Bool (c2sq_ok (c .fst) (c .snd .fst) (c .snd .snd)) true.)

def c2sq_at (p q r a b : Bool) : Bool
  ≔ match a, b [
    | false., false. ↦ true.
    | true., false. ↦ p
    | false., true. ↦ q
    | true., true. ↦ r ]

def c2sq_subset (p q r : Bool) (x : Product Bool Bool) : Bool ≔ c2sq_at p q r (x .fst) (x .snd)

def c2sq_no (A : Type) (e : Id Bool false. true.) : A ≔ absurd A (bool_encode false. true. e)

def c2sq_ok_intro (p q r : Bool) (h1 : Id Bool p true. → Id Bool q true. → Id Bool r true.)
  (h2 : Id Bool p true. → Id Bool r true. → Id Bool q true.)
  (h3 : Id Bool q true. → Id Bool r true. → Id Bool p true.)
  : Id Bool (c2sq_ok p q r) true.
  ≔ let t ≔ refl (true. : Bool) in
    match p, q, r [
    | false., false., false. ↦ t
    | true., false., false. ↦ t
    | false., true., false. ↦ t
    | false., false., true. ↦ t
    | true., true., true. ↦ t
    | true., true., false. ↦ c2sq_no (Id Bool false. true.) (h1 t t)
    | true., false., true. ↦ c2sq_no (Id Bool false. true.) (h2 t t)
    | false., true., true. ↦ c2sq_no (Id Bool false. true.) (h3 t t) ]

{` p ∧ q ⇒ r. `}
def c2sq_ok_imp1 (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) (hp : Id Bool p true.) (hq : Id Bool q true.)
  : Id Bool r true.
  ≔ match p, q, r [
    | false., false., false. ↦ c2sq_no (Id Bool false. true.) hp
    | true., false., false. ↦ c2sq_no (Id Bool false. true.) hq
    | false., true., false. ↦ c2sq_no (Id Bool false. true.) hp
    | false., false., true. ↦ refl (true. : Bool)
    | true., true., true. ↦ refl (true. : Bool)
    | true., true., false. ↦ c2sq_no (Id Bool false. true.) ok
    | true., false., true. ↦ refl (true. : Bool)
    | false., true., true. ↦ refl (true. : Bool) ]

{` p ∧ r ⇒ q. `}
def c2sq_ok_imp2 (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) (hp : Id Bool p true.) (hr : Id Bool r true.)
  : Id Bool q true.
  ≔ match p, q, r [
    | false., false., false. ↦ c2sq_no (Id Bool false. true.) hp
    | true., false., false. ↦ c2sq_no (Id Bool false. true.) hr
    | false., true., false. ↦ refl (true. : Bool)
    | false., false., true. ↦ c2sq_no (Id Bool false. true.) hp
    | true., true., true. ↦ refl (true. : Bool)
    | true., true., false. ↦ refl (true. : Bool)
    | true., false., true. ↦ c2sq_no (Id Bool false. true.) ok
    | false., true., true. ↦ refl (true. : Bool) ]

{` q ∧ r ⇒ p. `}
def c2sq_ok_imp3 (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) (hq : Id Bool q true.) (hr : Id Bool r true.)
  : Id Bool p true.
  ≔ match p, q, r [
    | false., false., false. ↦ c2sq_no (Id Bool false. true.) hq
    | true., false., false. ↦ refl (true. : Bool)
    | false., true., false. ↦ c2sq_no (Id Bool false. true.) hr
    | false., false., true. ↦ c2sq_no (Id Bool false. true.) hq
    | true., true., true. ↦ refl (true. : Bool)
    | true., true., false. ↦ refl (true. : Bool)
    | true., false., true. ↦ refl (true. : Bool)
    | false., true., true. ↦ c2sq_no (Id Bool false. true.) ok ]

def c2sq_mul_closed (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) (a b c d : Bool)
  (hx : Id Bool (c2sq_at p q r a b) true.) (hy : Id Bool (c2sq_at p q r c d) true.)
  : Id Bool (c2sq_at p q r (bool_xor a c) (bool_xor b d)) true.
  ≔ let t ≔ refl (true. : Bool) in
    match a, b, c, d [
    | false., false., false., false. ↦ t
    | false., false., false., true. ↦ hy
    | false., false., true., false. ↦ hy
    | false., false., true., true. ↦ hy
    | false., true., false., false. ↦ hx
    | false., true., false., true. ↦ t
    | false., true., true., false. ↦ c2sq_ok_imp1 p q r ok hy hx
    | false., true., true., true. ↦ c2sq_ok_imp3 p q r ok hx hy
    | true., false., false., false. ↦ hx
    | true., false., false., true. ↦ c2sq_ok_imp1 p q r ok hx hy
    | true., false., true., false. ↦ t
    | true., false., true., true. ↦ c2sq_ok_imp2 p q r ok hx hy
    | true., true., false., false. ↦ hx
    | true., true., false., true. ↦ c2sq_ok_imp3 p q r ok hy hx
    | true., true., true., false. ↦ c2sq_ok_imp2 p q r ok hy hx
    | true., true., true., true. ↦ t ]

def c2sq_code_closed (u : C2sqCode) : ClosedBoolSubsets c2sq_abstract
  ≔ let p ≔ u .fst .fst in let q ≔ u .fst .snd .fst in let r ≔ u .fst .snd .snd in
    (c2sq_subset p q r,
     (x ↦ bool_set (c2sq_subset p q r x) true.,
      (refl (true. : Bool),
       (x y hx hy ↦ c2sq_mul_closed p q r (u .snd) (x .fst) (x .snd) (y .fst) (y .snd) hx hy, x h ↦ h))))

def c2sq_closed_code (P : ClosedBoolSubsets c2sq_abstract) : C2sqCode
  ≔ let A ≔ P .fst in
    let m ≔ P .snd .snd .snd .fst in
    ((A (true., false.), (A (false., true.), A (true., true.))),
     c2sq_ok_intro (A (true., false.)) (A (false., true.)) (A (true., true.))
       (m (true., false.) (false., true.)) (m (true., false.) (true., true.)) (m (false., true.) (true., true.)))

def c2sq_closed_roundtrip_at (P : ClosedBoolSubsets c2sq_abstract) (a b : Bool)
  : Id Bool (c2sq_at (P .fst (true., false.)) (P .fst (false., true.)) (P .fst (true., true.)) a b) (P .fst (a, b))
  ≔ match a, b [
    | false., false. ↦ inverse Bool (P .fst (false., false.)) true. (P .snd .snd .fst)
    | true., false. ↦ refl (P .fst (true., false.))
    | false., true. ↦ refl (P .fst (false., true.))
    | true., true. ↦ refl (P .fst (true., true.)) ]

def c2sq_closed_code_equiv : Equiv (ClosedBoolSubsets c2sq_abstract) C2sqCode
  ≔ quasi_inverse_equiv (ClosedBoolSubsets c2sq_abstract) C2sqCode c2sq_closed_code c2sq_code_closed
      (P ↦ closed_bool_subsets_path c2sq_abstract (c2sq_code_closed (c2sq_closed_code P)) P
        (x ↦ c2sq_closed_roundtrip_at P (x .fst) (x .snd)))
      (u ↦ subtype_equal (Product Bool (Product Bool Bool))
        (c ↦ Id Bool (c2sq_ok (c .fst) (c .snd .fst) (c .snd .snd)) true.)
        (c ↦ bool_set (c2sq_ok (c .fst) (c .snd .fst) (c .snd .snd)) true.)
        (c2sq_closed_code (c2sq_code_closed u)) u (refl (u .fst)))

{` The five codes. `}
def c2sq_five : Nat ≔ suc. (suc. (suc. (suc. (suc. zero.))))

def c2sq_index (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) : Fin c2sq_five
  ≔ match p, q, r [
    | false., false., false. ↦ inr. star.
    | true., false., false. ↦ inl. (inr. star.)
    | false., true., false. ↦ inl. (inl. (inr. star.))
    | false., false., true. ↦ inl. (inl. (inl. (inr. star.)))
    | true., true., true. ↦ inl. (inl. (inl. (inl. (inr. star.))))
    | true., true., false. ↦ c2sq_no (Fin c2sq_five) ok
    | true., false., true. ↦ c2sq_no (Fin c2sq_five) ok
    | false., true., true. ↦ c2sq_no (Fin c2sq_five) ok ]

def c2sq_code_at (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.) : C2sqCode ≔ ((p, (q, r)), ok)

def c2sq_index_code : Fin c2sq_five → C2sqCode ≔ [
  | inr. _ ↦ c2sq_code_at false. false. false. (refl (true. : Bool))
  | inl. (inr. _) ↦ c2sq_code_at true. false. false. (refl (true. : Bool))
  | inl. (inl. (inr. _)) ↦ c2sq_code_at false. true. false. (refl (true. : Bool))
  | inl. (inl. (inl. (inr. _))) ↦ c2sq_code_at false. false. true. (refl (true. : Bool))
  | inl. (inl. (inl. (inl. (inr. _)))) ↦ c2sq_code_at true. true. true. (refl (true. : Bool))
  | inl. (inl. (inl. (inl. (inl. e)))) ↦ match e [] ]

def c2sq_code_ext (p q r : Bool) (ok ok' : Id Bool (c2sq_ok p q r) true.)
  : Id C2sqCode (c2sq_code_at p q r ok) (c2sq_code_at p q r ok')
  ≔ subtype_equal (Product Bool (Product Bool Bool))
      (c ↦ Id Bool (c2sq_ok (c .fst) (c .snd .fst) (c .snd .snd)) true.)
      (c ↦ bool_set (c2sq_ok (c .fst) (c .snd .fst) (c .snd .snd)) true.)
      (c2sq_code_at p q r ok) (c2sq_code_at p q r ok') (refl ((p, (q, r)) : Product Bool (Product Bool Bool)))

def c2sq_code_roundtrip (p q r : Bool) (ok : Id Bool (c2sq_ok p q r) true.)
  : Id C2sqCode (c2sq_index_code (c2sq_index p q r ok)) (c2sq_code_at p q r ok)
  ≔ let t ≔ refl (true. : Bool) in
    match p, q, r [
    | false., false., false. ↦ c2sq_code_ext false. false. false. t ok
    | true., false., false. ↦ c2sq_code_ext true. false. false. t ok
    | false., true., false. ↦ c2sq_code_ext false. true. false. t ok
    | false., false., true. ↦ c2sq_code_ext false. false. true. t ok
    | true., true., true. ↦ c2sq_code_ext true. true. true. t ok
    | true., true., false. ↦ c2sq_no (Id C2sqCode (c2sq_index_code (c2sq_index true. true. false. ok)) (c2sq_code_at true. true. false. ok)) ok
    | true., false., true. ↦ c2sq_no (Id C2sqCode (c2sq_index_code (c2sq_index true. false. true. ok)) (c2sq_code_at true. false. true. ok)) ok
    | false., true., true. ↦ c2sq_no (Id C2sqCode (c2sq_index_code (c2sq_index false. true. true. ok)) (c2sq_code_at false. true. true. ok)) ok ]

def c2sq_code_fin_equiv : Equiv C2sqCode (Fin c2sq_five)
  ≔ quasi_inverse_equiv C2sqCode (Fin c2sq_five)
      (u ↦ c2sq_index (u .fst .fst) (u .fst .snd .fst) (u .fst .snd .snd) (u .snd)) c2sq_index_code
      (u ↦ c2sq_code_roundtrip (u .fst .fst) (u .fst .snd .fst) (u .fst .snd .snd) (u .snd))
      [
      | inr. u ↦ inr. (unit_prop star. u)
      | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
      | inl. (inl. (inr. u)) ↦ inl. (inl. (inr. (unit_prop star. u)))
      | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. (unit_prop star. u))))
      | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inr. (unit_prop star. u)))))
      | inl. (inl. (inl. (inl. (inl. e)))) ↦ match e [] ]

{` The counts. `}
def c2_power_decidable_subgroups_equiv_zero
  : Equiv (Σ (Subgroups (c2pow_group zero.)) (IsDecidableSubgroup (c2pow_group zero.))) (Fin (suc. zero.))
  ≔ let C ≔ c2pow_group zero. in
    compose_equiv (DecidableSubgroups C) (ClosedBoolSubsets (abstr C)) (Fin (suc. zero.))
      (decidable_subgroups_closed_subsets_equiv C)
      (compose_equiv (ClosedBoolSubsets (abstr C)) (ClosedBoolSubsets unit_abstract_group) (Fin (suc. zero.))
        (closed_bool_subsets_iso_equiv (abstr C) unit_abstract_group c2pow_zero_iso) c2abs_unit_closed_equiv)

def c2_power_decidable_subgroups_equiv_one
  : Equiv (Σ (Subgroups (c2pow_group (suc. zero.))) (IsDecidableSubgroup (c2pow_group (suc. zero.)))) (Fin two)
  ≔ let C ≔ c2pow_group (suc. zero.) in
    compose_equiv (DecidableSubgroups C) (ClosedBoolSubsets (abstr C)) (Fin two)
      (decidable_subgroups_closed_subsets_equiv C)
      (compose_equiv (ClosedBoolSubsets (abstr C)) (ClosedBoolSubsets c2abs_bool) (Fin two)
        (closed_bool_subsets_iso_equiv (abstr C) c2abs_bool c2pow_one_iso)
        (compose_equiv (ClosedBoolSubsets c2abs_bool) Bool (Fin two) c2abs_bool_closed_equiv
          (canonical_inverse_equiv (Fin two) Bool fin_two_equiv)))

def c2_power_decidable_subgroups_equiv_two
  : Equiv (Σ (Subgroups (c2pow_group two)) (IsDecidableSubgroup (c2pow_group two))) (Fin c2sq_five)
  ≔ let C ≔ c2pow_group two in
    compose_equiv (DecidableSubgroups C) (ClosedBoolSubsets (abstr C)) (Fin c2sq_five)
      (decidable_subgroups_closed_subsets_equiv C)
      (compose_equiv (ClosedBoolSubsets (abstr C)) (ClosedBoolSubsets c2sq_abstract) (Fin c2sq_five)
        (closed_bool_subsets_iso_equiv (abstr C) c2sq_abstract c2pow_two_iso)
        (compose_equiv (ClosedBoolSubsets c2sq_abstract) C2sqCode (Fin c2sq_five) c2sq_closed_code_equiv
          c2sq_code_fin_equiv))

{` C_2^0 has 1 decidable subgroup. `}
def c2_power_decidable_subgroups_count_zero
  (h : IsFinite (Σ (Subgroups (c2pow_group zero.)) (IsDecidableSubgroup (c2pow_group zero.))))
  : Id Nat (cardinality (Σ (Subgroups (c2pow_group zero.)) (IsDecidableSubgroup (c2pow_group zero.))) h) (suc. zero.)
  ≔ cardinality_from_path (DecidableSubgroups (c2pow_group zero.)) h (suc. zero.)
      (ua (DecidableSubgroups (c2pow_group zero.)) (Fin (suc. zero.)) c2_power_decidable_subgroups_equiv_zero)

{` C_2 = C_2^1 has 2 decidable subgroups. `}
def c2_power_decidable_subgroups_count_one
  (h : IsFinite (Σ (Subgroups (c2pow_group (suc. zero.))) (IsDecidableSubgroup (c2pow_group (suc. zero.)))))
  : Id Nat (cardinality (Σ (Subgroups (c2pow_group (suc. zero.))) (IsDecidableSubgroup (c2pow_group (suc. zero.)))) h) two
  ≔ cardinality_from_path (DecidableSubgroups (c2pow_group (suc. zero.))) h two
      (ua (DecidableSubgroups (c2pow_group (suc. zero.))) (Fin two) c2_power_decidable_subgroups_equiv_one)

{` C_2 × C_2 = C_2^2 has 5 decidable subgroups. `}
def c2_power_decidable_subgroups_count_two
  (h : IsFinite (Σ (Subgroups (c2pow_group two)) (IsDecidableSubgroup (c2pow_group two))))
  : Id Nat (cardinality (Σ (Subgroups (c2pow_group two)) (IsDecidableSubgroup (c2pow_group two))) h) c2sq_five
  ≔ cardinality_from_path (DecidableSubgroups (c2pow_group two)) h c2sq_five
      (ua (DecidableSubgroups (c2pow_group two)) (Fin c2sq_five) c2_power_decidable_subgroups_equiv_two)

{` Litmus: with the finiteness proof of module 1041. `}
def c2_power_decidable_subgroups_count_two_litmus
  : Id Nat (cardinality (Σ (Subgroups (c2pow_group two)) (IsDecidableSubgroup (c2pow_group two)))
      (decidable_subgroups_finite (c2pow_group two) (cyclic_two_power_finite two))) c2sq_five
  ≔ c2_power_decidable_subgroups_count_two (decidable_subgroups_finite (c2pow_group two) (cyclic_two_power_finite two))
