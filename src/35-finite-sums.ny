export "34-finite-logic"

def isfinite_prop (A : Type) : isProp (IsFinite A)
  ≔ mere_isprop (Σ Nat (n ↦ Id Type A (Fin n)))

def finite_from_equiv (A : Type) (n : Nat) (e : Equiv A (Fin n)) : IsFinite A
  ≔ mere (Σ Nat (m ↦ Id Type A (Fin m))) (n, ua A (Fin n) e)

def finite_of_equiv (A B : Type) (e : Equiv A B) (h : IsFinite B) : IsFinite A
  ≔ transport Type IsFinite B A (inverse Type A B (ua A B e)) h

def sum_assoc_equiv (A B C : Type) : Equiv (Sum A (Sum B C)) (Sum (Sum A B) C)
  ≔ quasi_inverse_equiv (Sum A (Sum B C)) (Sum (Sum A B) C)
      [ inl. a ↦ inl. (inl. a)
      | inr. s ↦ match s [ inl. b ↦ inl. (inr. b) | inr. c ↦ inr. c ] ]
      [ inl. s ↦ match s [ inl. a ↦ inl. a | inr. b ↦ inr. (inl. b) ]
      | inr. c ↦ inr. (inr. c) ]
      [ inl. a ↦ refl (inl. a : Sum A (Sum B C))
      | inr. s ↦ match s [ inl. b ↦ refl (inr. (inl. b) : Sum A (Sum B C))
                         | inr. c ↦ refl (inr. (inr. c) : Sum A (Sum B C)) ] ]
      [ inl. s ↦ match s [ inl. a ↦ refl (inl. (inl. a) : Sum (Sum A B) C)
                         | inr. b ↦ refl (inl. (inr. b) : Sum (Sum A B) C) ]
      | inr. c ↦ refl (inr. c : Sum (Sum A B) C) ]

def sum_empty_right_equiv (A : Type) : Equiv (Sum A Empty) A
  ≔ quasi_inverse_equiv (Sum A Empty) A
      [ inl. a ↦ a | inr. e ↦ match e [] ] (a ↦ inl. a)
      [ inl. a ↦ refl (inl. a : Sum A Empty) | inr. e ↦ match e [] ] (a ↦ refl a)

def fin_sum_equiv (n m : Nat) : Equiv (Sum (Fin n) (Fin m)) (Fin (add n m))
  ≔ match m [
  | zero. ↦ sum_empty_right_equiv (Fin n)
  | suc. m ↦ compose_equiv (Sum (Fin n) (Fin (suc. m)))
      (Sum (Sum (Fin n) (Fin m)) Unit) (Fin (add n (suc. m)))
      (sum_assoc_equiv (Fin n) (Fin m) Unit)
      (sum_equiv (Sum (Fin n) (Fin m)) Unit (Fin (add n m)) Unit
        (fin_sum_equiv n m) (identity_equiv Unit)) ]

def product_sum_unit_to (A B : Type) (a : A) (s : Sum B Unit) : Sum (Product A B) A
  ≔ match s [ inl. b ↦ inl. (a, b) | inr. u ↦ inr. a ]

def product_sum_unit_from (A B : Type) : Sum (Product A B) A → Product A (Sum B Unit)
  ≔ [ inl. p ↦ (p .fst, inl. (p .snd)) | inr. a ↦ (a, inr. star.) ]

def product_sum_unit_eta (A B : Type) (a : A) (s : Sum B Unit)
  : Id (Product A (Sum B Unit))
      (product_sum_unit_from A B (product_sum_unit_to A B a s)) (a, s)
  ≔ match s [ inl. b ↦ refl (a, inl. b)
             | inr. u ↦ (refl a, inr. (unit_prop star. u)) ]

def product_sum_unit_equiv (A B : Type)
  : Equiv (Product A (Sum B Unit)) (Sum (Product A B) A)
  ≔ quasi_inverse_equiv (Product A (Sum B Unit)) (Sum (Product A B) A)
      (p ↦ product_sum_unit_to A B (p .fst) (p .snd)) (product_sum_unit_from A B)
      (p ↦ product_sum_unit_eta A B (p .fst) (p .snd))
      [ inl. p ↦ refl (inl. p : Sum (Product A B) A) | inr. a ↦ refl (inr. a : Sum (Product A B) A) ]

def fin_product_equiv (n m : Nat) : Equiv (Product (Fin n) (Fin m)) (Fin (mul n m))
  ≔ match m [
  | zero. ↦ quasi_inverse_equiv (Product (Fin n) Empty) Empty (p ↦ p .snd)
      (e ↦ match e []) (p ↦ match p .snd []) (e ↦ match e [])
  | suc. m ↦ compose_equiv (Product (Fin n) (Fin (suc. m)))
      (Sum (Product (Fin n) (Fin m)) (Fin n)) (Fin (mul n (suc. m)))
      (product_sum_unit_equiv (Fin n) (Fin m))
      (compose_equiv (Sum (Product (Fin n) (Fin m)) (Fin n))
        (Sum (Fin (mul n m)) (Fin n)) (Fin (mul n (suc. m)))
        (sum_equiv (Product (Fin n) (Fin m)) (Fin n) (Fin (mul n m)) (Fin n)
          (fin_product_equiv n m) (identity_equiv (Fin n)))
        (fin_sum_equiv (mul n m) n)) ]

def finite_binary_closure (F : Type → Type → Type)
  (standard : (n m : Nat) → IsFinite (F (Fin n) (Fin m)))
  (A B : Type) (ha : IsFinite A) (hb : IsFinite B) : IsFinite (F A B)
  ≔ finite_ind_prop (X ↦ IsFinite (F X B)) (X ↦ isfinite_prop (F X B))
      (n ↦ finite_ind_prop (Y ↦ IsFinite (F (Fin n) Y)) (Y ↦ isfinite_prop (F (Fin n) Y))
        (standard n) B hb) A ha

def finite_sum (A B : Type) (ha : IsFinite A) (hb : IsFinite B) : IsFinite (Sum A B)
  ≔ finite_binary_closure Sum
      (n m ↦ finite_from_equiv (Sum (Fin n) (Fin m)) (add n m) (fin_sum_equiv n m)) A B ha hb

def finite_product (A B : Type) (ha : IsFinite A) (hb : IsFinite B) : IsFinite (Product A B)
  ≔ finite_binary_closure Product
      (n m ↦ finite_from_equiv (Product (Fin n) (Fin m)) (mul n m) (fin_product_equiv n m)) A B ha hb

def sigma_fin_succ_to (n : Nat) (P : Fin (suc. n) → Type)
  (i : Fin (suc. n)) (p : P i) : Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.))
  ≔ match i [ inl. j ↦ inl. (j, p) | inr. u ↦ match u [ star. ↦ inr. p ] ]

def sigma_fin_succ_from (n : Nat) (P : Fin (suc. n) → Type)
  : Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.)) → Σ (Fin (suc. n)) P
  ≔ [ inl. p ↦ (inl. (p .fst), p .snd) | inr. p ↦ (inr. star., p) ]

def sigma_fin_succ_eta (n : Nat) (P : Fin (suc. n) → Type) (i : Fin (suc. n)) (p : P i)
  : Id (Σ (Fin (suc. n)) P) (sigma_fin_succ_from n P (sigma_fin_succ_to n P i p)) (i, p)
  ≔ match i [ inl. j ↦ refl (inl. j, p) | inr. u ↦ match u [ star. ↦ refl (inr. star., p) ] ]

def sigma_fin_succ_equiv (n : Nat) (P : Fin (suc. n) → Type)
  : Equiv (Σ (Fin (suc. n)) P) (Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.)))
  ≔ quasi_inverse_equiv (Σ (Fin (suc. n)) P) (Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.)))
      (p ↦ sigma_fin_succ_to n P (p .fst) (p .snd)) (sigma_fin_succ_from n P)
      (p ↦ sigma_fin_succ_eta n P (p .fst) (p .snd))
      [ inl. p ↦ refl (inl. p : Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.)))
      | inr. p ↦ refl (inr. p : Sum (Σ (Fin n) (j ↦ P (inl. j))) (P (inr. star.))) ]

def fin_sigma_finite (n : Nat) (P : Fin n → Type) (hp : (i : Fin n) → IsFinite (P i))
  : IsFinite (Σ (Fin n) P)
  ≔ match n [
  | zero. ↦ finite_from_equiv (Σ Empty P) zero.
      (quasi_inverse_equiv (Σ Empty P) Empty (p ↦ p .fst) (e ↦ match e [])
        (p ↦ match p .fst []) (e ↦ match e []))
  | suc. n ↦ finite_of_equiv (Σ (Fin (suc. n)) P)
      (Sum (Σ (Fin n) (i ↦ P (inl. i))) (P (inr. star.))) (sigma_fin_succ_equiv n P)
      (finite_sum (Σ (Fin n) (i ↦ P (inl. i))) (P (inr. star.))
        (fin_sigma_finite n (i ↦ P (inl. i)) (i ↦ hp (inl. i))) (hp (inr. star.))) ]

def FiniteSums (A : Type) : Type
  ≔ (P : A → Type) → ((a : A) → IsFinite (P a)) → IsFinite (Σ A P)

def finite_sums_prop (A : Type) : isProp (FiniteSums A)
  ≔ pi_prop (A → Type) (P ↦ ((a : A) → IsFinite (P a)) → IsFinite (Σ A P))
      (P ↦ pi_prop ((a : A) → IsFinite (P a)) (_ ↦ IsFinite (Σ A P)) (_ ↦ isfinite_prop (Σ A P)))

{` xca:fin-sum-of-finsets, first clause. `}
def finite_sigma (A : Type) (ha : IsFinite A) : FiniteSums A
  ≔ finite_ind_prop FiniteSums finite_sums_prop fin_sigma_finite A ha
