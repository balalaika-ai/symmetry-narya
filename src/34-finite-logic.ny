export "33-list-tabulation"

{` Induction on a merely finite type, with a proposition-valued conclusion. `}
def finite_ind_prop (P : Type → Type) (hP : (A : Type) → isProp (P A))
  (standard : (n : Nat) → P (Fin n)) (A : Type) (h : IsFinite A) : P A
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (P A) (hP A)
      (w ↦ transport Type P (Fin (w .fst)) A
        (inverse Type A (Fin (w .fst)) (w .snd)) (standard (w .fst))) h

def fin_pi_cons (n : Nat) (P : Fin (suc. n) → Type)
  (tail : (i : Fin n) → P (inl. i)) (head : P (inr. star.))
  : (i : Fin (suc. n)) → P i
  ≔ [ inl. i ↦ tail i | inr. u ↦ match u [ star. ↦ head ] ]

def fin_choice (n : Nat) (P : Fin n → Type)
  (h : (i : Fin n) → Mere (P i)) : Mere ((i : Fin n) → P i)
  ≔ match n [
  | zero. ↦ mere ((i : Empty) → P i) (i ↦ match i [])
  | suc. n ↦ mere_rec ((i : Fin n) → P (inl. i)) (Mere ((i : Fin (suc. n)) → P i))
      (mere_isprop ((i : Fin (suc. n)) → P i))
      (tail ↦ mere_rec (P (inr. star.)) (Mere ((i : Fin (suc. n)) → P i))
        (mere_isprop ((i : Fin (suc. n)) → P i))
        (head ↦ mere ((i : Fin (suc. n)) → P i) (fin_pi_cons n P tail head)) (h (inr. star.)))
      (fin_choice n (i ↦ P (inl. i)) (i ↦ h (inl. i))) ]

def FiniteChoice (A : Type) : Type
  ≔ (P : A → Type) → ((a : A) → Mere (P a)) → Mere ((a : A) → P a)

def finite_choice_prop (A : Type) : isProp (FiniteChoice A)
  ≔ pi_prop (A → Type) (P ↦ ((a : A) → Mere (P a)) → Mere ((a : A) → P a))
      (P ↦ pi_prop ((a : A) → Mere (P a)) (_ ↦ Mere ((a : A) → P a))
        (_ ↦ mere_isprop ((a : A) → P a)))

def finite_choice (A : Type) (h : IsFinite A) : FiniteChoice A
  ≔ finite_ind_prop FiniteChoice finite_choice_prop fin_choice A h

def fin_forall_decidable (n : Nat) (P : Fin n → Type)
  (d : (i : Fin n) → Decidable (P i)) : Decidable ((i : Fin n) → P i)
  ≔ match n [
  | zero. ↦ inl. (i ↦ match i [])
  | suc. n ↦ match d (inr. star.) [
    | inr. no ↦ inr. (f ↦ no (f (inr. star.)))
    | inl. head ↦ match fin_forall_decidable n (i ↦ P (inl. i)) (i ↦ d (inl. i)) [
      | inl. tail ↦ inl. (fin_pi_cons n P tail head)
      | inr. no ↦ inr. (f ↦ no (i ↦ f (inl. i))) ] ] ]

def fin_sigma_no (n : Nat) (P : Fin (suc. n) → Type)
  (nt : Σ (Fin n) (i ↦ P (inl. i)) → Empty) (nh : P (inr. star.) → Empty)
  (i : Fin (suc. n)) (p : P i) : Empty
  ≔ match i [ inl. j ↦ nt (j, p) | inr. u ↦ match u [ star. ↦ nh p ] ]

def fin_sigma_decidable (n : Nat) (P : Fin n → Type)
  (d : (i : Fin n) → Decidable (P i)) : Decidable (Σ (Fin n) P)
  ≔ match n [
  | zero. ↦ inr. (p ↦ match p .fst [])
  | suc. n ↦ match d (inr. star.) [
    | inl. head ↦ inl. (inr. star., head)
    | inr. nh ↦ match fin_sigma_decidable n (i ↦ P (inl. i)) (i ↦ d (inl. i)) [
      | inl. tail ↦ inl. (inl. (tail .fst), tail .snd)
      | inr. nt ↦ inr. (p ↦ fin_sigma_no n P nt nh (p .fst) (p .snd)) ] ] ]

def decidable_mere (A : Type) (d : Decidable A) : Decidable (Mere A)
  ≔ match d [ inl. a ↦ inl. (mere A a)
            | inr. no ↦ inr. (mere_rec A Empty empty_prop no) ]

def FiniteQuantifiers (A : Type) : Type
  ≔ (P : A → Type) → ((a : A) → isProp (P a)) → ((a : A) → Decidable (P a)) →
      Product (Decidable ((a : A) → P a)) (Decidable (Mere (Σ A P)))

def finite_quantifiers_prop (A : Type) : isProp (FiniteQuantifiers A)
  ≔ pi_prop (A → Type)
      (P ↦ ((a : A) → isProp (P a)) → ((a : A) → Decidable (P a)) →
        Product (Decidable ((a : A) → P a)) (Decidable (Mere (Σ A P))))
      (P ↦ pi_prop ((a : A) → isProp (P a))
        (hp ↦ ((a : A) → Decidable (P a)) →
          Product (Decidable ((a : A) → P a)) (Decidable (Mere (Σ A P))))
        (hp ↦ pi_prop ((a : A) → Decidable (P a))
          (_ ↦ Product (Decidable ((a : A) → P a)) (Decidable (Mere (Σ A P))))
          (_ ↦ product_prop (Decidable ((a : A) → P a)) (Decidable (Mere (Σ A P)))
            (decidability_prop ((a : A) → P a) (pi_prop A P hp))
            (decidability_prop (Mere (Σ A P)) (mere_isprop (Σ A P))))))

{` xca:dec-quant-finset, both universal and existential quantifiers. `}
def finite_quantifiers (A : Type) (h : IsFinite A) : FiniteQuantifiers A
  ≔ finite_ind_prop FiniteQuantifiers finite_quantifiers_prop
      (n P hp d ↦ (fin_forall_decidable n P d, decidable_mere (Σ (Fin n) P) (fin_sigma_decidable n P d))) A h
