export "35-finite-sums"

def cardinality_equiv (A B : Type) (e : Equiv A B) (ha : IsFinite A) (hb : IsFinite B)
  : Id Nat (cardinality A ha) (cardinality B hb)
  ≔ mere_rec (Id Type B (Fin (cardinality B hb)))
      (Id Nat (cardinality A ha) (cardinality B hb)) (nat_set (cardinality A ha) (cardinality B hb))
      (p ↦ cardinality_from_path A ha (cardinality B hb)
        (concat Type A B (Fin (cardinality B hb)) (ua A B e) p)) (cardinality_spec B hb)

def cardinality_binary (F : Type → Type → Type) (size : Nat → Nat → Nat)
  (standard : (n m : Nat) → Equiv (F (Fin n) (Fin m)) (Fin (size n m)))
  (A B : Type) (ha : IsFinite A) (hb : IsFinite B) (hab : IsFinite (F A B))
  : Id Nat (cardinality (F A B) hab) (size (cardinality A ha) (cardinality B hb))
  ≔ let n ≔ cardinality A ha in let m ≔ cardinality B hb in
    mere_rec (Id Type A (Fin n)) (Id Nat (cardinality (F A B) hab) (size n m))
      (nat_set (cardinality (F A B) hab) (size n m))
      (p ↦ mere_rec (Id Type B (Fin m)) (Id Nat (cardinality (F A B) hab) (size n m))
        (nat_set (cardinality (F A B) hab) (size n m))
        (q ↦ cardinality_from_path (F A B) hab (size n m)
          (concat Type (F A B) (F (Fin n) (Fin m)) (Fin (size n m))
            (refl F p q) (ua (F (Fin n) (Fin m)) (Fin (size n m)) (standard n m))))
        (cardinality_spec B hb)) (cardinality_spec A ha)

def cardinality_sum (A B : Type) (ha : IsFinite A) (hb : IsFinite B) (hs : IsFinite (Sum A B))
  : Id Nat (cardinality (Sum A B) hs) (add (cardinality A ha) (cardinality B hb))
  ≔ cardinality_binary Sum add fin_sum_equiv A B ha hb hs

def cardinality_product (A B : Type) (ha : IsFinite A) (hb : IsFinite B) (hp : IsFinite (Product A B))
  : Id Nat (cardinality (Product A B) hp) (mul (cardinality A ha) (cardinality B hb))
  ≔ cardinality_binary Product mul fin_product_equiv A B ha hb hp

{` xca:fin-sum-of-finsets, second clause. Every specified fiber equivalence is used. `}
def cardinality_equinumerous_sum (A Y : Type) (P : A → Type)
  (ha : IsFinite A) (hy : IsFinite Y) (e : (a : A) → Equiv (P a) Y)
  (hs : IsFinite (Σ A P))
  : Id Nat (cardinality (Σ A P) hs) (mul (cardinality A ha) (cardinality Y hy))
  ≔ concat Nat (cardinality (Σ A P) hs)
      (cardinality (Product A Y) (finite_product A Y ha hy)) (mul (cardinality A ha) (cardinality Y hy))
      (cardinality_equiv (Σ A P) (Product A Y) (family_equiv A P (_ ↦ Y) e)
        hs (finite_product A Y ha hy))
      (cardinality_product A Y ha hy (finite_product A Y ha hy))

{` Third clause: arithmetic summation without choosing an enumeration of A. `}
def arithmetic_sum (A : Type) (ha : IsFinite A) (f : A → Nat) : Nat
  ≔ cardinality (Σ A (a ↦ Fin (f a)))
      (finite_sigma A ha (a ↦ Fin (f a)) (a ↦ fin_is_finite (f a)))

def arithmetic_sum_constant (A : Type) (ha : IsFinite A) (n : Nat)
  : Id Nat (arithmetic_sum A ha (_ ↦ n)) (mul (cardinality A ha) n)
  ≔ concat Nat (arithmetic_sum A ha (_ ↦ n))
      (mul (cardinality A ha) (cardinality (Fin n) (fin_is_finite n))) (mul (cardinality A ha) n)
      (cardinality_equinumerous_sum A (Fin n) (_ ↦ Fin n) ha (fin_is_finite n)
        (_ ↦ identity_equiv (Fin n))
        (finite_sigma A ha (_ ↦ Fin n) (_ ↦ fin_is_finite n)))
      (map_path Nat Nat (mul (cardinality A ha)) (cardinality (Fin n) (fin_is_finite n)) n
        (standard_cardinality n))

def arithmetic_sum_reindex (A B : Type) (ha : IsFinite A) (hb : IsFinite B)
  (e : Equiv A B) (f : B → Nat)
  : Id Nat (arithmetic_sum A ha (a ↦ f (e .map a))) (arithmetic_sum B hb f)
  ≔ cardinality_equiv (Σ A (a ↦ Fin (f (e .map a)))) (Σ B (b ↦ Fin (f b)))
      (sigma_pullback_equiv A B e (b ↦ Fin (f b)))
      (finite_sigma A ha (a ↦ Fin (f (e .map a))) (a ↦ fin_is_finite (f (e .map a))))
      (finite_sigma B hb (b ↦ Fin (f b)) (b ↦ fin_is_finite (f b)))

def arithmetic_sum_empty (f : Fin zero. → Nat)
  : Id Nat (arithmetic_sum (Fin zero.) (fin_is_finite zero.) f) zero.
  ≔ cardinality_from_path (Σ Empty (i ↦ Fin (f i)))
      (finite_sigma Empty (fin_is_finite zero.) (i ↦ Fin (f i)) (i ↦ fin_is_finite (f i))) zero.
      (ua (Σ Empty (i ↦ Fin (f i))) Empty
        (quasi_inverse_equiv (Σ Empty (i ↦ Fin (f i))) Empty (p ↦ p .fst) (e ↦ match e [])
          (p ↦ match p .fst []) (e ↦ match e [])))

def arithmetic_sum_step (n : Nat) (f : Fin (suc. n) → Nat)
  : Id Nat (arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) f)
      (add (arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ f (inl. i))) (f (inr. star.)))
  ≔ let Tail ≔ Σ (Fin n) (i ↦ Fin (f (inl. i))) in
    let Head ≔ Fin (f (inr. star.)) in
    let ht ≔ finite_sigma (Fin n) (fin_is_finite n) (i ↦ Fin (f (inl. i))) (i ↦ fin_is_finite (f (inl. i))) in
    let hh ≔ fin_is_finite (f (inr. star.)) in
    let hs ≔ finite_sum Tail Head ht hh in
    concat Nat (arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) f)
      (cardinality (Sum Tail Head) hs) (add (cardinality Tail ht) (f (inr. star.)))
      (cardinality_equiv (Σ (Fin (suc. n)) (i ↦ Fin (f i))) (Sum Tail Head)
        (sigma_fin_succ_equiv n (i ↦ Fin (f i)))
        (finite_sigma (Fin (suc. n)) (fin_is_finite (suc. n)) (i ↦ Fin (f i)) (i ↦ fin_is_finite (f i))) hs)
      (concat Nat (cardinality (Sum Tail Head) hs) (add (cardinality Tail ht) (cardinality Head hh))
        (add (cardinality Tail ht) (f (inr. star.)))
        (cardinality_sum Tail Head ht hh hs)
        (map_path Nat Nat (add (cardinality Tail ht)) (cardinality Head hh) (f (inr. star.))
          (standard_cardinality (f (inr. star.)))))

def fin_inhabited_decidable (n : Nat) : Decidable (Fin n)
  ≔ match n [ zero. ↦ inr. (identity Empty) | suc. n ↦ inl. (inr. star.) ]

def finite_inhabited_decidable (A : Type) (ha : IsFinite A) : Decidable (Mere A)
  ≔ finite_ind_prop (X ↦ Decidable (Mere X)) (X ↦ decidability_prop (Mere X) (mere_isprop X))
      (n ↦ decidable_mere (Fin n) (fin_inhabited_decidable n)) A ha

def finite_unit : IsFinite Unit
  ≔ finite_from_equiv Unit (suc. zero.) (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv)

def decidable_prop_finite (P : Type) (hp : isProp P) (d : Decidable P) : IsFinite P
  ≔ match d [
  | inl. p ↦ finite_of_equiv P Unit (iff_equiv P Unit hp unit_prop (_ ↦ star.) (_ ↦ p)) finite_unit
  | inr. no ↦ finite_from_equiv P zero. (iff_equiv P Empty hp empty_prop no (absurd P)) ]

def finite_prop_decidable (P : Type) (hp : isProp P) (h : IsFinite P) : Decidable P
  ≔ match finite_inhabited_decidable P h [
  | inl. t ↦ inl. (mere_rec P P hp (identity P) t)
  | inr. no ↦ inr. (p ↦ no (mere P p)) ]

def finite_prop_iff_decidable (P : Type) (hp : isProp P) : Equiv (IsFinite P) (Decidable P)
  ≔ iff_equiv (IsFinite P) (Decidable P) (isfinite_prop P) (decidability_prop P hp)
      (finite_prop_decidable P hp) (decidable_prop_finite P hp)

def inhabited_prop_cardinality (P : Type) (hp : isProp P) (h : IsFinite P) (p : P)
  : Id Nat (cardinality P h) (suc. zero.)
  ≔ cardinality_from_path P h (suc. zero.)
      (ua P (Fin (suc. zero.))
        (compose_equiv P Unit (Fin (suc. zero.))
          (iff_equiv P Unit hp unit_prop (_ ↦ star.) (_ ↦ p))
          (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv)))

def cardinality_one_inhabited (A : Type) (h : IsFinite A)
  (q : Id Nat (cardinality A h) (suc. zero.)) : Mere A
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) (Mere A) (mere_isprop A)
      (p ↦ mere A (equiv_inverse_map A (Fin (cardinality A h))
        (id_to_equiv A (Fin (cardinality A h)) p)
        (transport Nat Fin (suc. zero.) (cardinality A h)
          (inverse Nat (cardinality A h) (suc. zero.) q) (inr. star.)))) (cardinality_spec A h)

{` rem:subset-of-fin-set: a finite proposition holds exactly when its cardinality is one. `}
def proposition_cardinality_one (P : Type) (hp : isProp P) (h : IsFinite P)
  : Equiv P (Id Nat (cardinality P h) (suc. zero.))
  ≔ iff_equiv P (Id Nat (cardinality P h) (suc. zero.)) hp (nat_set (cardinality P h) (suc. zero.))
      (inhabited_prop_cardinality P hp h)
      (q ↦ mere_rec P P hp (identity P) (cardinality_one_inhabited P h q))

def finite_decidable_subset (A : Type) (ha : IsFinite A) (P : A → Type)
  (hp : (a : A) → isProp (P a)) (d : (a : A) → Decidable (P a)) : IsFinite (Σ A P)
  ≔ finite_sigma A ha P (a ↦ decidable_prop_finite (P a) (hp a) (d a))
