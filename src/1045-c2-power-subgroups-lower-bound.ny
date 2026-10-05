export "1044-c2-power-pointwise-model"

{` Chapter 10, the remark at fingp.tex 105, lower bound: C_2^(m+1)
   has at least 3^m decidable subgroups. Write vectors of
   F_2^(m+1) = (Fin (m+1) → Bool) as (w, b) with w : Fin m → Bool and b the
   last coordinate. For each labelling c : Fin m → C2Tri (kill, free, tie)
   the set
     U_c = { (w, b) | w_i = 0 if c_i = kill, w_i = b if c_i = tie }
   is a Bool-valued abstract subgroup (tri_closed), and c ↦ U_c is injective
   (tri_closed_injective: the vectors (1_free(c), 0) and (1_tie(c), 1) lie in
   U_c and separate it from U_c' for c ≠ c'). Hence 3^m ≤ |decidable
   subgroups of C_2^(m+1)| (c2_power_decidable_subgroups_lower_bound). `}

def C2Tri : Type ≔ data [ kill. | free. | tie. ]

def tri_no (A : Type) (e : Id Bool false. true.) : A ≔ absurd A (bool_encode false. true. e)

def tri_check (t : C2Tri) (x b : Bool) : Bool
  ≔ match t [ kill. ↦ bool_not x | free. ↦ true. | tie. ↦ bool_not (bool_xor x b) ]

def tri_is_free (t : C2Tri) : Bool ≔ match t [ kill. ↦ false. | free. ↦ true. | tie. ↦ false. ]

def tri_is_tie (t : C2Tri) : Bool ≔ match t [ kill. ↦ false. | free. ↦ false. | tie. ↦ true. ]

def tri_check_zero (t : C2Tri) : Id Bool (tri_check t false. false.) true.
  ≔ match t [ kill. ↦ refl (true. : Bool) | free. ↦ refl (true. : Bool) | tie. ↦ refl (true. : Bool) ]

def tri_check_mul (t : C2Tri) (x b y d : Bool) (h1 : Id Bool (tri_check t x b) true.) (h2 : Id Bool (tri_check t y d) true.)
  : Id Bool (tri_check t (bool_xor x y) (bool_xor b d)) true.
  ≔ match t [
    | free. ↦ refl (true. : Bool)
    | kill. ↦ match x, y [
      | false., false. ↦ refl (true. : Bool)
      | true., false. ↦ tri_no (Id Bool (tri_check kill. (bool_xor true. false.) (bool_xor b d)) true.) h1
      | true., true. ↦ tri_no (Id Bool (tri_check kill. (bool_xor true. true.) (bool_xor b d)) true.) h1
      | false., true. ↦ tri_no (Id Bool (tri_check kill. (bool_xor false. true.) (bool_xor b d)) true.) h2 ]
    | tie. ↦ match x, b, y, d [
      | false., false., false., false. ↦ refl (true. : Bool)
      | false., false., false., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. false.) (bool_xor false. true.)) true.) h2
      | false., false., true., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. true.) (bool_xor false. false.)) true.) h2
      | false., false., true., true. ↦ refl (true. : Bool)
      | false., true., false., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. false.) (bool_xor true. false.)) true.) h1
      | false., true., false., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. false.) (bool_xor true. true.)) true.) h1
      | false., true., true., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. true.) (bool_xor true. false.)) true.) h1
      | false., true., true., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor false. true.) (bool_xor true. true.)) true.) h1
      | true., false., false., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. false.) (bool_xor false. false.)) true.) h1
      | true., false., false., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. false.) (bool_xor false. true.)) true.) h1
      | true., false., true., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. true.) (bool_xor false. false.)) true.) h1
      | true., false., true., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. true.) (bool_xor false. true.)) true.) h1
      | true., true., false., false. ↦ refl (true. : Bool)
      | true., true., false., true. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. false.) (bool_xor true. true.)) true.) h2
      | true., true., true., false. ↦ tri_no (Id Bool (tri_check tie. (bool_xor true. true.) (bool_xor true. false.)) true.) h2
      | true., true., true., true. ↦ refl (true. : Bool) ] ]

{` Conjunction over Fin m. `}
def c2tri_and (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def c2tri_and_intro (a b : Bool) (ha : Id Bool a true.) (hb : Id Bool b true.) : Id Bool (c2tri_and a b) true.
  ≔ match a [ false. ↦ tri_no (Id Bool false. true.) ha | true. ↦ hb ]

def c2tri_and_left (a b : Bool) (h : Id Bool (c2tri_and a b) true.) : Id Bool a true.
  ≔ match a [ false. ↦ tri_no (Id Bool false. true.) h | true. ↦ refl (true. : Bool) ]

def c2tri_and_right (a b : Bool) (h : Id Bool (c2tri_and a b) true.) : Id Bool b true.
  ≔ match a [ false. ↦ tri_no (Id Bool b true.) h | true. ↦ h ]

def c2tri_all (m : Nat) (f : Fin m → Bool) : Bool
  ≔ match m [ zero. ↦ true. | suc. k ↦ c2tri_and (c2tri_all k (i ↦ f (inl. i))) (f (inr. star.)) ]

def c2tri_all_intro (m : Nat) (f : Fin m → Bool) (h : (i : Fin m) → Id Bool (f i) true.) : Id Bool (c2tri_all m f) true.
  ≔ match m [
    | zero. ↦ refl (true. : Bool)
    | suc. k ↦ c2tri_and_intro (c2tri_all k (i ↦ f (inl. i))) (f (inr. star.))
        (c2tri_all_intro k (i ↦ f (inl. i)) (i ↦ h (inl. i))) (h (inr. star.)) ]

def c2tri_all_elim (m : Nat) (f : Fin m → Bool) (t : Id Bool (c2tri_all m f) true.) (i : Fin m) : Id Bool (f i) true.
  ≔ match m [
    | zero. ↦ match i [ ]
    | suc. k ↦ match i [
      | inl. j ↦ c2tri_all_elim k (i ↦ f (inl. i)) (c2tri_and_left (c2tri_all k (i ↦ f (inl. i))) (f (inr. star.)) t) j
      | inr. u ↦ match u [ star. ↦ c2tri_and_right (c2tri_all k (i ↦ f (inl. i))) (f (inr. star.)) t ] ] ]

{` The subgroups U_c. `}
def tri_subset (m : Nat) (c : Fin m → C2Tri) (v : Fin (suc. m) → Bool) : Bool
  ≔ c2tri_all m (i ↦ tri_check (c i) (v (inl. i)) (v (inr. star.)))

def tri_closed (m : Nat) (c : Fin m → C2Tri) : ClosedBoolSubsets (c2vec_abstract (suc. m))
  ≔ (tri_subset m c,
     (v ↦ bool_set (tri_subset m c v) true.,
      (c2tri_all_intro m (i ↦ tri_check (c i) false. false.) (i ↦ tri_check_zero (c i)),
       (v w hv hw ↦ c2tri_all_intro m
          (i ↦ tri_check (c i) (bool_xor (v (inl. i)) (w (inl. i))) (bool_xor (v (inr. star.)) (w (inr. star.))))
          (i ↦ tri_check_mul (c i) (v (inl. i)) (v (inr. star.)) (w (inl. i)) (w (inr. star.))
            (c2tri_all_elim m (i ↦ tri_check (c i) (v (inl. i)) (v (inr. star.))) hv i)
            (c2tri_all_elim m (i ↦ tri_check (c i) (w (inl. i)) (w (inr. star.))) hw i)),
        v h ↦ h))))

{` The separating vectors. `}
def tri_free_vector (m : Nat) (c : Fin m → C2Tri) (x : Fin (suc. m)) : Bool
  ≔ match x [ inl. j ↦ tri_is_free (c j) | inr. _ ↦ false. ]

def tri_tie_vector (m : Nat) (c : Fin m → C2Tri) (x : Fin (suc. m)) : Bool
  ≔ match x [ inl. j ↦ tri_is_tie (c j) | inr. _ ↦ true. ]

def tri_free_self (t : C2Tri) : Id Bool (tri_check t (tri_is_free t) false.) true.
  ≔ match t [ kill. ↦ refl (true. : Bool) | free. ↦ refl (true. : Bool) | tie. ↦ refl (true. : Bool) ]

def tri_tie_self (t : C2Tri) : Id Bool (tri_check t (tri_is_tie t) true.) true.
  ≔ match t [ kill. ↦ refl (true. : Bool) | free. ↦ refl (true. : Bool) | tie. ↦ refl (true. : Bool) ]

def tri_free_vector_mem (m : Nat) (c : Fin m → C2Tri) : Id Bool (tri_subset m c (tri_free_vector m c)) true.
  ≔ c2tri_all_intro m (i ↦ tri_check (c i) (tri_is_free (c i)) false.) (i ↦ tri_free_self (c i))

def tri_tie_vector_mem (m : Nat) (c : Fin m → C2Tri) : Id Bool (tri_subset m c (tri_tie_vector m c)) true.
  ≔ c2tri_all_intro m (i ↦ tri_check (c i) (tri_is_tie (c i)) true.) (i ↦ tri_tie_self (c i))

def tri_determined (t t' : C2Tri) (a : Id Bool (tri_check t' (tri_is_free t) false.) true.)
  (b : Id Bool (tri_check t' (tri_is_tie t) true.) true.) (a' : Id Bool (tri_check t (tri_is_free t') false.) true.)
  (b' : Id Bool (tri_check t (tri_is_tie t') true.) true.) : Id C2Tri t t'
  ≔ match t, t' [
    | kill., kill. ↦ refl (kill. : C2Tri)
    | kill., free. ↦ tri_no (Id C2Tri kill. free.) a'
    | kill., tie. ↦ tri_no (Id C2Tri kill. tie.) b
    | free., kill. ↦ tri_no (Id C2Tri free. kill.) a
    | free., free. ↦ refl (free. : C2Tri)
    | free., tie. ↦ tri_no (Id C2Tri free. tie.) a
    | tie., kill. ↦ tri_no (Id C2Tri tie. kill.) b
    | tie., free. ↦ tri_no (Id C2Tri tie. free.) a'
    | tie., tie. ↦ refl (tie. : C2Tri) ]

def tri_member_transfer (m : Nat) (c c' : Fin m → C2Tri)
  (h : (v : Fin (suc. m) → Bool) → Id Bool (tri_subset m c v) (tri_subset m c' v))
  (v : Fin (suc. m) → Bool) (t : Id Bool (tri_subset m c v) true.) : Id Bool (tri_subset m c' v) true.
  ≔ concat Bool (tri_subset m c' v) (tri_subset m c v) true. (inverse Bool (tri_subset m c v) (tri_subset m c' v) (h v)) t

def tri_subset_injective (m : Nat) (c c' : Fin m → C2Tri)
  (h : (v : Fin (suc. m) → Bool) → Id Bool (tri_subset m c v) (tri_subset m c' v)) : Id (Fin m → C2Tri) c c'
  ≔ let h' : (v : Fin (suc. m) → Bool) → Id Bool (tri_subset m c' v) (tri_subset m c v)
      ≔ v ↦ inverse Bool (tri_subset m c v) (tri_subset m c' v) (h v) in
    funext (Fin m) (_ ↦ C2Tri) c c'
      (i ↦ tri_determined (c i) (c' i)
        (c2tri_all_elim m (j ↦ tri_check (c' j) (tri_is_free (c j)) false.)
          (tri_member_transfer m c c' h (tri_free_vector m c) (tri_free_vector_mem m c)) i)
        (c2tri_all_elim m (j ↦ tri_check (c' j) (tri_is_tie (c j)) true.)
          (tri_member_transfer m c c' h (tri_tie_vector m c) (tri_tie_vector_mem m c)) i)
        (c2tri_all_elim m (j ↦ tri_check (c j) (tri_is_free (c' j)) false.)
          (tri_member_transfer m c' c h' (tri_free_vector m c') (tri_free_vector_mem m c')) i)
        (c2tri_all_elim m (j ↦ tri_check (c j) (tri_is_tie (c' j)) true.)
          (tri_member_transfer m c' c h' (tri_tie_vector m c') (tri_tie_vector_mem m c')) i))

def tri_closed_injective (m : Nat) (c c' : Fin m → C2Tri)
  (e : Id (ClosedBoolSubsets (c2vec_abstract (suc. m))) (tri_closed m c) (tri_closed m c')) : Id (Fin m → C2Tri) c c'
  ≔ let V ≔ Fin (suc. m) → Bool in
    tri_subset_injective m c c'
      (happly V (_ ↦ Bool) (tri_subset m c) (tri_subset m c')
        (map_path (ClosedBoolSubsets (c2vec_abstract (suc. m))) (V → Bool) (P ↦ P .fst) (tri_closed m c) (tri_closed m c') e))

{` Cardinalities. `}
def c2tri_three : Nat ≔ suc. (suc. (suc. zero.))

def c2tri_fin_equiv : Equiv C2Tri (Fin c2tri_three)
  ≔ quasi_inverse_equiv C2Tri (Fin c2tri_three)
      [ kill. ↦ inr. star. | free. ↦ inl. (inr. star.) | tie. ↦ inl. (inl. (inr. star.)) ]
      [ inr. _ ↦ kill. | inl. (inr. _) ↦ free. | inl. (inl. (inr. _)) ↦ tie. | inl. (inl. (inl. e)) ↦ match e [ ] ]
      [ kill. ↦ refl (kill. : C2Tri) | free. ↦ refl (free. : C2Tri) | tie. ↦ refl (tie. : C2Tri) ]
      [
      | inr. u ↦ inr. (unit_prop star. u)
      | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
      | inl. (inl. (inr. u)) ↦ inl. (inl. (inr. (unit_prop star. u)))
      | inl. (inl. (inl. e)) ↦ match e [ ] ]

def c2tri_finite : IsFinite C2Tri ≔ finite_from_equiv C2Tri c2tri_three c2tri_fin_equiv

def c2tri_labellings_card (m : Nat) (h : IsFinite (Fin m → C2Tri))
  : Id Nat (cardinality (Fin m → C2Tri) h) (nat_power c2tri_three m)
  ≔ concat Nat (cardinality (Fin m → C2Tri) h) (nat_power (cardinality C2Tri c2tri_finite) m) (nat_power c2tri_three m)
      (fin_functions_card m C2Tri c2tri_finite h)
      (map_path Nat Nat (x ↦ nat_power x m) (cardinality C2Tri c2tri_finite) c2tri_three
        (cardinality_from_path C2Tri c2tri_finite c2tri_three (ua C2Tri (Fin c2tri_three) c2tri_fin_equiv)))

def c2vec_decidable_subgroups_equiv (n : Nat)
  : Equiv (Σ (Subgroups (c2pow_group n)) (IsDecidableSubgroup (c2pow_group n))) (ClosedBoolSubsets (c2vec_abstract n))
  ≔ compose_equiv (DecidableSubgroups (c2pow_group n)) (ClosedBoolSubsets (abstr (c2pow_group n)))
      (ClosedBoolSubsets (c2vec_abstract n))
      (decidable_subgroups_closed_subsets_equiv (c2pow_group n))
      (closed_bool_subsets_iso_equiv (abstr (c2pow_group n)) (c2vec_abstract n) (c2pow_vec_iso n))

{` C_2^(m+1) has at least 3^m decidable subgroups. `}
def c2_power_decidable_subgroups_lower_bound (m : Nat)
  (h : IsFinite (Σ (Subgroups (c2pow_group (suc. m))) (IsDecidableSubgroup (c2pow_group (suc. m)))))
  : Le (nat_power c2tri_three m) (cardinality (Σ (Subgroups (c2pow_group (suc. m))) (IsDecidableSubgroup (c2pow_group (suc. m)))) h)
  ≔ let D ≔ DecidableSubgroups (c2pow_group (suc. m)) in
    let CB ≔ ClosedBoolSubsets (c2vec_abstract (suc. m)) in
    let e ≔ c2vec_decidable_subgroups_equiv (suc. m) in
    let hCB : IsFinite CB ≔ finite_of_equiv CB D (canonical_inverse_equiv D CB e) h in
    let hL : IsFinite (Fin m → C2Tri) ≔ fin_functions_finite m C2Tri c2tri_finite in
    let le : Le (cardinality (Fin m → C2Tri) hL) (cardinality CB hCB)
      ≔ finite_injection_card_le (Fin m → C2Tri) CB hL hCB (tri_closed m) (tri_closed_injective m) in
    let eD : Id Nat (cardinality CB hCB) (cardinality D h)
      ≔ inverse Nat (cardinality D h) (cardinality CB hCB) (cardinality_equiv D CB e h hCB) in
    transport Nat (x ↦ Le (nat_power c2tri_three m) x) (cardinality CB hCB) (cardinality D h) eD
      (transport Nat (x ↦ Le x (cardinality CB hCB)) (cardinality (Fin m → C2Tri) hL) (nat_power c2tri_three m)
        (c2tri_labellings_card m hL) le)
