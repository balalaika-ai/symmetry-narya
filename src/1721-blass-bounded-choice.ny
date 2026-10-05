export "1720-blass-counting"

{` Choice for families of non-empty finite sets of varying size at most n
   (sizes recorded by CardBound). It is the induction hypothesis of the proof
   of Blass's Theorem 6; it follows from AC(1), …, AC(n), and it gives AC(k)
   for every k ≤ n. `}
def ChoiceUpTo (n : Nat) : Type
  ≔ (X : SetTypes) (P : X .fst → Type) → ((x : X .fst) → CardBound n (P x))
    → ((x : X .fst) → Mere (P x)) → Mere ((x : X .fst) → P x)

def bsix_fin_path_set (k : Nat) (T : Type) (p : Mere (Id Type (Fin k) T)) : isSet T
  ≔ mere_rec (Id Type (Fin k) T) (isSet T) (isset_isprop T)
      (q ↦ transport Type isSet (Fin k) T q (fin_set k)) p

def bsix_fin_zero_empty (k : Nat) (le : Le k zero.) (T : Type) (p : Mere (Id Type (Fin k) T)) (t : T) : Empty
  ≔ match k [
  | zero. ↦ mere_rec (Id Type Empty T) Empty empty_prop
      (q ↦ transport Type (Y ↦ Y) T Empty (inverse Type Empty T q) t) p
  | suc. j ↦ match le [] ]

def choice_up_to_zero : ChoiceUpTo zero.
  ≔ X P cb inh ↦ mere ((x : X .fst) → P x)
      (x ↦ absurd (P x) (mere_rec (P x) Empty empty_prop
        (t ↦ bsix_fin_zero_empty (cb x .fst) (cb x .snd .fst) (P x) (cb x .snd .snd) t) (inh x)))

def bsix_low_part (n : Nat) (X : SetTypes) (k : X .fst → Nat) : SetTypes
  ≔ (Σ (X .fst) (x ↦ Le (k x) n),
      sigma_set (X .fst) (x ↦ Le (k x) n) (X .snd) (x ↦ prop_is_set (Le (k x) n) (le_prop (k x) n)))

def bsix_top_part (n : Nat) (X : SetTypes) (k : X .fst → Nat) : SetTypes
  ≔ (Σ (X .fst) (x ↦ Id Nat (k x) n),
      sigma_set (X .fst) (x ↦ Id Nat (k x) n) (X .snd) (x ↦ prop_is_set (Id Nat (k x) n) (nat_set (k x) n)))

def bsix_glue (n : Nat) (X : SetTypes) (P : X .fst → Type) (k : X .fst → Nat) (hk : (x : X .fst) → Le (k x) (suc. n))
  (t1 : (z : bsix_low_part n X k .fst) → P (z .fst)) (t2 : (z : bsix_top_part (suc. n) X k .fst) → P (z .fst))
  (x : X .fst) : P x
  ≔ match le_split (k x) (suc. n) (hk x) [ inl. lt ↦ t1 (x, lt) | inr. e ↦ t2 (x, e) ]

{` ChoiceUpTo n and AC(n+1) give ChoiceUpTo (n+1): split the index set into
   the part with sizes ≤ n and the part with size n+1. `}
def choice_up_to_succ (n : Nat) (cws : ChoiceUpTo n) (ac : ChoiceOfSize (suc. n)) : ChoiceUpTo (suc. n)
  ≔ X P cb inh ↦
    let k : X .fst → Nat ≔ x ↦ cb x .fst in
    let X1 ≔ bsix_low_part n X k in
    let X2 ≔ bsix_top_part (suc. n) X k in
    mere_rec ((z : X1 .fst) → P (z .fst)) (Mere ((x : X .fst) → P x)) (mere_isprop ((x : X .fst) → P x))
      (t1 ↦ mere_rec ((z : X2 .fst) → P (z .fst)) (Mere ((x : X .fst) → P x)) (mere_isprop ((x : X .fst) → P x))
        (t2 ↦ mere ((x : X .fst) → P x) (bsix_glue n X P k (x ↦ cb x .snd .fst) t1 t2))
        (ac X2 (z ↦ ((P (z .fst), bsix_fin_path_set (k (z .fst)) (P (z .fst)) (cb (z .fst) .snd .snd)),
                     transport Nat (j ↦ Mere (Id Type (Fin j) (P (z .fst)))) (k (z .fst)) (suc. n) (z .snd)
                       (cb (z .fst) .snd .snd)))
          (z ↦ inh (z .fst))))
      (cws X1 (z ↦ P (z .fst)) (z ↦ (k (z .fst), (z .snd, cb (z .fst) .snd .snd))) (z ↦ inh (z .fst)))

def choice_up_to_size (n : Nat) (cws : ChoiceUpTo n) : ChoiceOfSize n
  ≔ X P inh ↦ cws X (x ↦ P x .fst .fst) (x ↦ (n, (le_refl n, P x .snd))) inh

{` Removing a point from an (m+1)-element set leaves an m-element set. `}
def BsixWithoutPaths (m : Nat) (B : Type) : Type ≔ (y : B) → Id Type (Fin m) (Without B y)

def bsix_without_path (m : Nat) (A : Type) (p : Id Type (Fin (suc. m)) A) (y : A) : Id Type (Fin m) (Without A y)
  ≔ transport Type (BsixWithoutPaths m) (Fin (suc. m)) A p
      (z ↦ inverse Type (Without (Fin (suc. m)) z) (Fin m)
        (ua (Without (Fin (suc. m)) z) (Fin m) (without_fin_equiv m z))) y

def bsix_without_bound (m : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. m)) A)) (y : A)
  : CardBound m (Without A y)
  ≔ (m, (le_refl m, trunc_map native_truncation (Id Type (Fin (suc. m)) A) (Id Type (Fin m) (Without A y))
      (q ↦ bsix_without_path m A q y) p))

def bsix_without_inhabited (m : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. (suc. m))) A)) (y : A)
  : Mere (Without A y)
  ≔ trunc_map native_truncation (Id Type (Fin (suc. (suc. m))) A) (Without A y)
      (q ↦ transport Type (Y ↦ Y) (Fin (suc. m)) (Without A y) (bsix_without_path (suc. m) A q y) (inr. star.)) p

{` Litmus: ChoiceUpTo 1 holds (from AC(1)), and gives AC(1) back. `}
def choice_up_to_one : ChoiceUpTo (suc. zero.)
  ≔ choice_up_to_succ zero. choice_up_to_zero choice_of_size_one
