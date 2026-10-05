export "1520-field-hom-injective"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms:
   preliminaries for the counterexample k(X), X ↦ X² (module 1532). The
   field of fractions of an integral domain with decidable equality
   (DecidableDomain: a non-trivial commutative ring without zero divisors
   whose equality is decidable). Elements are classes of pairs (p, q) with
   q ≠ 0 under (p, q) ~ (p', q') :⇔ p q' = p' q, in the set quotient of
   module 41 (Quotient). The operations
     (p, q) + (r, s) = (p s + r q, q s),  (p, q)(r, s) = (p r, q s),
     −(p, q) = (−p, q),  0 = (0, 1),  1 = (1, 1)
   respect ~ and compute on classes by definition (quotient_rec computes on
   quotient_class); the ring laws are proved on representatives. The result
   is a field in the book's sense (frac_field): a non-invertible class has
   numerator 0 (decided by the decidable equality; otherwise (q, p) is an
   inverse). d ↦ (d, 1) is a ring homomorphism (frac_inclusion). `}

def DecidableDomain : Type ≔ sig (
  ring : AbstractRing,
  comm : IsCommutativeRing ring,
  nontrivial : IsNonTrivialRing ring,
  no_zero_divisors : (x y : ring .carrier) → Not (Id (ring .carrier) x (ring .zero))
    → Not (Id (ring .carrier) y (ring .zero)) → Not (Id (ring .carrier) (ring .mul x y) (ring .zero)),
  dec : DecidableEquality (ring .carrier))

{` Identities of commutative rings. `}
def cring_mul_swap_right (R : AbstractRing) (hc : IsCommutativeRing R) (x y z : R .carrier)
  : Id (R .carrier) (R .mul (R .mul x y) z) (R .mul (R .mul x z) y)
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    calc
      m (m x y) z = m x (m y z) by inverse S (m x (m y z)) (m (m x y) z) (ring_mul_assoc R x y z)
      = m x (m z y) by refl (m x) (hc y z)
      = m (m x z) y by ring_mul_assoc R x z y ∎

def cring_mul_interchange4 (R : AbstractRing) (hc : IsCommutativeRing R) (x y z w : R .carrier)
  : Id (R .carrier) (R .mul (R .mul x y) (R .mul z w)) (R .mul (R .mul x z) (R .mul y w))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    calc
      m (m x y) (m z w) = m (m (m x y) z) w by ring_mul_assoc R (m x y) z w
      = m (m (m x z) y) w by refl ((u ↦ m u w) : S → S) (cring_mul_swap_right R hc x y z)
      = m (m x z) (m y w) by inverse S (m (m x z) (m y w)) (m (m (m x z) y) w) (ring_mul_assoc R (m x z) y w) ∎

{` (x (y z)) w = (x y)(w z). `}
def cring_frac_term (R : AbstractRing) (hc : IsCommutativeRing R) (x y z w : R .carrier)
  : Id (R .carrier) (R .mul (R .mul x (R .mul y z)) w) (R .mul (R .mul x y) (R .mul w z))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    calc
      m (m x (m y z)) w = m (m (m x y) z) w by refl ((u ↦ m u w) : S → S) (ring_mul_assoc R x y z)
      = m (m (m x y) w) z by cring_mul_swap_right R hc (m x y) z w
      = m (m x y) (m w z) by inverse S (m (m x y) (m w z)) (m (m (m x y) w) z) (ring_mul_assoc R (m x y) w z) ∎

{` a c = b c with c ≠ 0 implies a = b. `}
def domain_cancel_right (D : DecidableDomain) (a b c : D .ring .carrier)
  (nc : Not (Id (D .ring .carrier) c (D .ring .zero)))
  (e : Id (D .ring .carrier) (D .ring .mul a c) (D .ring .mul b c)) : Id (D .ring .carrier) a b
  ≔ let R ≔ D .ring in let S ≔ R .carrier in
    match D .dec a b [
    | inl. y ↦ y
    | inr. ne ↦ match D .no_zero_divisors (R .add a (R .neg b)) c (field_sub_nonzero R a b ne) nc
        (calc
           R .mul (R .add a (R .neg b)) c = R .add (R .mul a c) (R .neg (R .mul b c)) by ring_sub_rdistr R a b c
           = R .add (R .mul b c) (R .neg (R .mul b c))
             by refl ((u ↦ R .add u (R .neg (R .mul b c))) : S → S) e
           = R .zero by R .add_laws .inv_right (R .mul b c) ∎) [ ] ]

def domain_one_nonzero (D : DecidableDomain) : Not (Id (D .ring .carrier) (D .ring .one) (D .ring .zero))
  ≔ e ↦ D .nontrivial (inverse (D .ring .carrier) (D .ring .one) (D .ring .zero) e)

{` Pairs (p, q) with q ≠ 0 and the relation p q' = p' q. `}
def FracPair (D : DecidableDomain) : Type
  ≔ Product (D .ring .carrier) (Σ (D .ring .carrier) (q ↦ Not (Id (D .ring .carrier) q (D .ring .zero))))

def frac_num (D : DecidableDomain) (a : FracPair D) : D .ring .carrier ≔ a .fst

def frac_den (D : DecidableDomain) (a : FracPair D) : D .ring .carrier ≔ a .snd .fst

def FracRel (D : DecidableDomain) (a b : FracPair D) : Type
  ≔ Id (D .ring .carrier) (D .ring .mul (a .fst) (b .snd .fst)) (D .ring .mul (b .fst) (a .snd .fst))

def frac_rel_trans (D : DecidableDomain) (a b c : FracPair D) (r1 : FracRel D a b) (r2 : FracRel D b c) : FracRel D a c
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let hc ≔ D .comm in
    let p ≔ a .fst in let q ≔ a .snd .fst in let p' ≔ b .fst in let q' ≔ b .snd .fst in
    let p'' ≔ c .fst in let q'' ≔ c .snd .fst in
    domain_cancel_right D (m p q'') (m p'' q) q' (b .snd .snd)
      (calc
         m (m p q'') q' = m (m p q') q'' by cring_mul_swap_right R hc p q'' q'
         = m (m p' q) q'' by refl ((u ↦ m u q'') : S → S) r1
         = m (m p' q'') q by cring_mul_swap_right R hc p' q q''
         = m (m p'' q') q by refl ((u ↦ m u q) : S → S) r2
         = m (m p'' q) q' by cring_mul_swap_right R hc p'' q' q ∎)

def frac_equiv (D : DecidableDomain) : EquivalenceRelation (FracPair D)
  ≔ (a b ↦ (FracRel D a b, ring_set (D .ring) (D .ring .mul (a .fst) (b .snd .fst)) (D .ring .mul (b .fst) (a .snd .fst))),
     a ↦ refl (D .ring .mul (a .fst) (a .snd .fst)),
     a b r ↦ inverse (D .ring .carrier) (D .ring .mul (a .fst) (b .snd .fst)) (D .ring .mul (b .fst) (a .snd .fst)) r,
     a b c r1 r2 ↦ frac_rel_trans D a b c r1 r2)

def FracQ (D : DecidableDomain) : Type ≔ Quotient (FracPair D) (frac_equiv D)

def frac_class (D : DecidableDomain) (a : FracPair D) : FracQ D ≔ quotient_class (FracPair D) (frac_equiv D) a

def frac_set (D : DecidableDomain) : isSet (FracQ D) ≔ quotient_set (FracPair D) (frac_equiv D)

def frac_encode (D : DecidableDomain) (a b : FracPair D) (r : FracRel D a b) : Id (FracQ D) (frac_class D a) (frac_class D b)
  ≔ quotient_encode (FracPair D) (frac_equiv D) a b r

def frac_effective (D : DecidableDomain) (a b : FracPair D) (e : Id (FracQ D) (frac_class D a) (frac_class D b))
  : FracRel D a b
  ≔ quotient_effective (FracPair D) (frac_equiv D) a b .map e

{` Equal numerators and denominators give related pairs. `}
def frac_rel_of_eq (D : DecidableDomain) (a b : FracPair D)
  (eN : Id (D .ring .carrier) (a .fst) (b .fst)) (eD : Id (D .ring .carrier) (a .snd .fst) (b .snd .fst)) : FracRel D a b
  ≔ let S ≔ D .ring .carrier in let m ≔ D .ring .mul in
    concat S (m (a .fst) (b .snd .fst)) (m (b .fst) (b .snd .fst)) (m (b .fst) (a .snd .fst))
      (refl ((x ↦ m x (b .snd .fst)) : S → S) eN) (refl (m (b .fst)) (inverse S (a .snd .fst) (b .snd .fst) eD))

{` Induction on classes into propositions. `}
def frac_ind (D : DecidableDomain) (P : FracQ D → Type) (hP : (z : FracQ D) → isProp (P z))
  (b : (a : FracPair D) → P (frac_class D a)) (z : FracQ D) : P z
  ≔ mere_rec (BookFiber (FracPair D) (FracQ D) (frac_class D) z) (P z) (hP z)
      (w ↦ transport (FracQ D) P (frac_class D (w .fst)) z
             (inverse (FracQ D) z (frac_class D (w .fst)) (w .snd)) (b (w .fst)))
      (quotient_surjective (FracPair D) (frac_equiv D) z)

def frac_ind_eq1 (D : DecidableDomain) (l r : FracQ D → FracQ D)
  (b : (a : FracPair D) → Id (FracQ D) (l (frac_class D a)) (r (frac_class D a))) (z : FracQ D) : Id (FracQ D) (l z) (r z)
  ≔ frac_ind D (z ↦ Id (FracQ D) (l z) (r z)) (z ↦ frac_set D (l z) (r z)) b z

def frac_ind_eq2 (D : DecidableDomain) (l r : FracQ D → FracQ D → FracQ D)
  (b : (a c : FracPair D) → Id (FracQ D) (l (frac_class D a) (frac_class D c)) (r (frac_class D a) (frac_class D c)))
  (z w : FracQ D) : Id (FracQ D) (l z w) (r z w)
  ≔ frac_ind D (z ↦ Id (FracQ D) (l z w) (r z w)) (z ↦ frac_set D (l z w) (r z w))
      (a ↦ frac_ind_eq1 D (l (frac_class D a)) (r (frac_class D a)) (c ↦ b a c) w) z

def frac_ind_eq3 (D : DecidableDomain) (l r : FracQ D → FracQ D → FracQ D → FracQ D)
  (b : (a c e : FracPair D) → Id (FracQ D) (l (frac_class D a) (frac_class D c) (frac_class D e))
                                           (r (frac_class D a) (frac_class D c) (frac_class D e)))
  (z w v : FracQ D) : Id (FracQ D) (l z w v) (r z w v)
  ≔ frac_ind D (z ↦ Id (FracQ D) (l z w v) (r z w v)) (z ↦ frac_set D (l z w v) (r z w v))
      (a ↦ frac_ind_eq2 D (l (frac_class D a)) (r (frac_class D a)) (c e ↦ b a c e) w v) z

{` Lifting a binary operation on pairs that respects ~ in each argument. `}
def frac_lift2 (D : DecidableDomain) (op : FracPair D → FracPair D → FracPair D)
  (rl : (a a' b : FracPair D) → FracRel D a a' → FracRel D (op a b) (op a' b))
  (rr : (a b b' : FracPair D) → FracRel D b b' → FracRel D (op a b) (op a b'))
  : FracQ D → FracQ D → FracQ D
  ≔ let P ≔ FracPair D in let Q ≔ FracQ D in let E ≔ frac_equiv D in
    let inner : P → Q → Q
      ≔ a ↦ quotient_rec P Q E (frac_set D) (b ↦ frac_class D (op a b))
               (b b' r ↦ frac_encode D (op a b) (op a b') (rr a b b' r)) in
    quotient_rec P (Q → Q) E (pi_set Q (_ ↦ Q) (_ ↦ frac_set D)) inner
      (a a' r ↦ funext Q (_ ↦ Q) (inner a) (inner a')
         (z ↦ frac_ind_eq1 D (inner a) (inner a') (b ↦ frac_encode D (op a b) (op a' b) (rl a a' b r)) z))

def frac_lift1 (D : DecidableDomain) (op : FracPair D → FracPair D)
  (rl : (a a' : FracPair D) → FracRel D a a' → FracRel D (op a) (op a')) : FracQ D → FracQ D
  ≔ quotient_rec (FracPair D) (FracQ D) (frac_equiv D) (frac_set D) (a ↦ frac_class D (op a))
      (a a' r ↦ frac_encode D (op a) (op a') (rl a a' r))

{` Operations on pairs. `}
def frac_pair_add (D : DecidableDomain) (a b : FracPair D) : FracPair D
  ≔ let R ≔ D .ring in
    (R .add (R .mul (a .fst) (b .snd .fst)) (R .mul (b .fst) (a .snd .fst)),
     (R .mul (a .snd .fst) (b .snd .fst), D .no_zero_divisors (a .snd .fst) (b .snd .fst) (a .snd .snd) (b .snd .snd)))

def frac_pair_mul (D : DecidableDomain) (a b : FracPair D) : FracPair D
  ≔ let R ≔ D .ring in
    (R .mul (a .fst) (b .fst),
     (R .mul (a .snd .fst) (b .snd .fst), D .no_zero_divisors (a .snd .fst) (b .snd .fst) (a .snd .snd) (b .snd .snd)))

def frac_pair_neg (D : DecidableDomain) (a : FracPair D) : FracPair D ≔ (D .ring .neg (a .fst), a .snd)

def frac_pair_of (D : DecidableDomain) (d : D .ring .carrier) : FracPair D ≔ (d, (D .ring .one, domain_one_nonzero D))

def frac_pair_zero (D : DecidableDomain) : FracPair D ≔ frac_pair_of D (D .ring .zero)

def frac_pair_one (D : DecidableDomain) : FracPair D ≔ frac_pair_of D (D .ring .one)

{` Respect of ~. `}
def frac_add_resp_left (D : DecidableDomain) (a a' b : FracPair D) (r : FracRel D a a')
  : FracRel D (frac_pair_add D a b) (frac_pair_add D a' b)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let ad ≔ R .add in let hc ≔ D .comm in
    let p ≔ a .fst in let q ≔ a .snd .fst in let p' ≔ a' .fst in let q' ≔ a' .snd .fst in
    let x ≔ b .fst in let s ≔ b .snd .fst in
    calc
      m (ad (m p s) (m x q)) (m q' s) = ad (m (m p s) (m q' s)) (m (m x q) (m q' s))
        by ring_rdistr R (m p s) (m x q) (m q' s)
      = ad (m (m p' s) (m q s)) (m (m x q') (m q s))
        by refl ad
          (calc
             m (m p s) (m q' s) = m (m p q') (m s s) by cring_mul_interchange4 R hc p s q' s
             = m (m p' q) (m s s) by refl ((u ↦ m u (m s s)) : S → S) r
             = m (m p' s) (m q s)
               by inverse S (m (m p' s) (m q s)) (m (m p' q) (m s s)) (cring_mul_interchange4 R hc p' s q s) ∎)
          (cring_mul_interchange4 R hc x q q' s)
      = m (ad (m p' s) (m x q')) (m q s)
        by inverse S (m (ad (m p' s) (m x q')) (m q s)) (ad (m (m p' s) (m q s)) (m (m x q') (m q s)))
          (ring_rdistr R (m p' s) (m x q') (m q s)) ∎

def frac_mul_resp_left (D : DecidableDomain) (a a' b : FracPair D) (r : FracRel D a a')
  : FracRel D (frac_pair_mul D a b) (frac_pair_mul D a' b)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let hc ≔ D .comm in
    let p ≔ a .fst in let q ≔ a .snd .fst in let p' ≔ a' .fst in let q' ≔ a' .snd .fst in
    let x ≔ b .fst in let s ≔ b .snd .fst in
    calc
      m (m p x) (m q' s) = m (m p q') (m x s) by cring_mul_interchange4 R hc p x q' s
      = m (m p' q) (m x s) by refl ((u ↦ m u (m x s)) : S → S) r
      = m (m p' x) (m q s) by inverse S (m (m p' x) (m q s)) (m (m p' q) (m x s)) (cring_mul_interchange4 R hc p' x q s) ∎

def frac_neg_resp (D : DecidableDomain) (a a' : FracPair D) (r : FracRel D a a')
  : FracRel D (frac_pair_neg D a) (frac_pair_neg D a')
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in
    let p ≔ a .fst in let q ≔ a .snd .fst in let p' ≔ a' .fst in let q' ≔ a' .snd .fst in
    calc
      m (R .neg p) q' = R .neg (m p q') by ring_mul_neg_left R p q'
      = R .neg (m p' q) by refl (R .neg) r
      = m (R .neg p') q by inverse S (m (R .neg p') q) (R .neg (m p' q)) (ring_mul_neg_left R p' q) ∎

def frac_add_comm_rel (D : DecidableDomain) (a b : FracPair D) : FracRel D (frac_pair_add D a b) (frac_pair_add D b a)
  ≔ let R ≔ D .ring in
    frac_rel_of_eq D (frac_pair_add D a b) (frac_pair_add D b a)
      (ring_add_comm R (R .mul (a .fst) (b .snd .fst)) (R .mul (b .fst) (a .snd .fst)))
      (D .comm (a .snd .fst) (b .snd .fst))

def frac_mul_comm_rel (D : DecidableDomain) (a b : FracPair D) : FracRel D (frac_pair_mul D a b) (frac_pair_mul D b a)
  ≔ frac_rel_of_eq D (frac_pair_mul D a b) (frac_pair_mul D b a) (D .comm (a .fst) (b .fst)) (D .comm (a .snd .fst) (b .snd .fst))

def frac_add_resp_right (D : DecidableDomain) (a b b' : FracPair D) (r : FracRel D b b')
  : FracRel D (frac_pair_add D a b) (frac_pair_add D a b')
  ≔ frac_rel_trans D (frac_pair_add D a b) (frac_pair_add D b a) (frac_pair_add D a b') (frac_add_comm_rel D a b)
      (frac_rel_trans D (frac_pair_add D b a) (frac_pair_add D b' a) (frac_pair_add D a b')
        (frac_add_resp_left D b b' a r) (frac_add_comm_rel D b' a))

def frac_mul_resp_right (D : DecidableDomain) (a b b' : FracPair D) (r : FracRel D b b')
  : FracRel D (frac_pair_mul D a b) (frac_pair_mul D a b')
  ≔ frac_rel_trans D (frac_pair_mul D a b) (frac_pair_mul D b a) (frac_pair_mul D a b') (frac_mul_comm_rel D a b)
      (frac_rel_trans D (frac_pair_mul D b a) (frac_pair_mul D b' a) (frac_pair_mul D a b')
        (frac_mul_resp_left D b b' a r) (frac_mul_comm_rel D b' a))

{` The operations on classes. `}
def frac_add (D : DecidableDomain) : FracQ D → FracQ D → FracQ D
  ≔ frac_lift2 D (frac_pair_add D) (frac_add_resp_left D) (frac_add_resp_right D)

def frac_mul (D : DecidableDomain) : FracQ D → FracQ D → FracQ D
  ≔ frac_lift2 D (frac_pair_mul D) (frac_mul_resp_left D) (frac_mul_resp_right D)

def frac_neg (D : DecidableDomain) : FracQ D → FracQ D ≔ frac_lift1 D (frac_pair_neg D) (frac_neg_resp D)

def frac_zero (D : DecidableDomain) : FracQ D ≔ frac_class D (frac_pair_zero D)

def frac_one (D : DecidableDomain) : FracQ D ≔ frac_class D (frac_pair_one D)

{` Laws on representatives. `}
def frac_add_assoc_rel (D : DecidableDomain) (a b c : FracPair D)
  : FracRel D (frac_pair_add D a (frac_pair_add D b c)) (frac_pair_add D (frac_pair_add D a b) c)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let ad ≔ R .add in let hc ≔ D .comm in
    let p ≔ a .fst in let q ≔ a .snd .fst in let x ≔ b .fst in let s ≔ b .snd .fst in
    let u ≔ c .fst in let v ≔ c .snd .fst in
    frac_rel_of_eq D (frac_pair_add D a (frac_pair_add D b c)) (frac_pair_add D (frac_pair_add D a b) c)
      (calc
         ad (m p (m s v)) (m (ad (m x v) (m u s)) q) = ad (m p (m s v)) (ad (m (m x v) q) (m (m u s) q))
           by refl (ad (m p (m s v))) (ring_rdistr R (m x v) (m u s) q)
         = ad (ad (m p (m s v)) (m (m x v) q)) (m (m u s) q)
           by R .add_laws .assoc (m p (m s v)) (m (m x v) q) (m (m u s) q)
         = ad (ad (m (m p s) v) (m (m x q) v)) (m u (m q s))
           by refl ad (refl ad (ring_mul_assoc R p s v) (cring_mul_swap_right R hc x v q))
             (concat S (m (m u s) q) (m u (m s q)) (m u (m q s))
               (inverse S (m u (m s q)) (m (m u s) q) (ring_mul_assoc R u s q)) (refl (m u) (hc s q)))
         = ad (m (ad (m p s) (m x q)) v) (m u (m q s))
           by refl ((t ↦ ad t (m u (m q s))) : S → S)
             (inverse S (m (ad (m p s) (m x q)) v) (ad (m (m p s) v) (m (m x q) v)) (ring_rdistr R (m p s) (m x q) v)) ∎)
      (ring_mul_assoc R q s v)

def frac_add_unit_right_rel (D : DecidableDomain) (a : FracPair D) : FracRel D (frac_pair_add D a (frac_pair_zero D)) a
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let p ≔ a .fst in let q ≔ a .snd .fst in
    frac_rel_of_eq D (frac_pair_add D a (frac_pair_zero D)) a
      (concat S (R .add (R .mul p (R .one)) (R .mul (R .zero) q)) (R .add p (R .zero)) p
        (refl (R .add) (ring_mul_one_right R p) (ring_mul_zero_left R q)) (R .add_laws .unit_right p))
      (ring_mul_one_right R q)

def frac_add_unit_left_rel (D : DecidableDomain) (a : FracPair D) : FracRel D (frac_pair_add D (frac_pair_zero D) a) a
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let p ≔ a .fst in let q ≔ a .snd .fst in
    frac_rel_of_eq D (frac_pair_add D (frac_pair_zero D) a) a
      (concat S (R .add (R .mul (R .zero) q) (R .mul p (R .one))) (R .add (R .zero) p) p
        (refl (R .add) (ring_mul_zero_left R q) (ring_mul_one_right R p)) (R .add_laws .unit_left p))
      (ring_mul_one_left R q)

def frac_add_inv_right_rel (D : DecidableDomain) (a : FracPair D)
  : FracRel D (frac_pair_add D a (frac_pair_neg D a)) (frac_pair_zero D)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let p ≔ a .fst in let q ≔ a .snd .fst in
    concat S (m (R .add (m p q) (m (R .neg p) q)) (R .one)) (R .zero) (m (R .zero) (m q q))
      (calc
         m (R .add (m p q) (m (R .neg p) q)) (R .one) = R .add (m p q) (m (R .neg p) q)
           by ring_mul_one_right R (R .add (m p q) (m (R .neg p) q))
         = m (R .add p (R .neg p)) q
           by inverse S (m (R .add p (R .neg p)) q) (R .add (m p q) (m (R .neg p) q)) (ring_rdistr R p (R .neg p) q)
         = R .zero by ring_sub_self_mul R p q ∎)
      (inverse S (m (R .zero) (m q q)) (R .zero) (ring_mul_zero_left R (m q q)))

def frac_mul_one_right_rel (D : DecidableDomain) (a : FracPair D) : FracRel D (frac_pair_mul D a (frac_pair_one D)) a
  ≔ frac_rel_of_eq D (frac_pair_mul D a (frac_pair_one D)) a (ring_mul_one_right (D .ring) (a .fst))
      (ring_mul_one_right (D .ring) (a .snd .fst))

def frac_mul_one_left_rel (D : DecidableDomain) (a : FracPair D) : FracRel D (frac_pair_mul D (frac_pair_one D) a) a
  ≔ frac_rel_of_eq D (frac_pair_mul D (frac_pair_one D) a) a (ring_mul_one_left (D .ring) (a .fst))
      (ring_mul_one_left (D .ring) (a .snd .fst))

def frac_mul_assoc_rel (D : DecidableDomain) (a b c : FracPair D)
  : FracRel D (frac_pair_mul D a (frac_pair_mul D b c)) (frac_pair_mul D (frac_pair_mul D a b) c)
  ≔ frac_rel_of_eq D (frac_pair_mul D a (frac_pair_mul D b c)) (frac_pair_mul D (frac_pair_mul D a b) c)
      (ring_mul_assoc (D .ring) (a .fst) (b .fst) (c .fst))
      (ring_mul_assoc (D .ring) (a .snd .fst) (b .snd .fst) (c .snd .fst))

{` (n, d) ~ (n c, d c) for c ≠ 0. `}
def frac_scale (D : DecidableDomain) (a : FracPair D) (c : D .ring .carrier) (nc : Not (Id (D .ring .carrier) c (D .ring .zero)))
  : FracPair D
  ≔ (D .ring .mul (a .fst) c, (D .ring .mul (a .snd .fst) c, D .no_zero_divisors (a .snd .fst) c (a .snd .snd) nc))

def frac_scale_rel (D : DecidableDomain) (a : FracPair D) (c : D .ring .carrier) (nc : Not (Id (D .ring .carrier) c (D .ring .zero)))
  : FracRel D a (frac_scale D a c nc)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let n ≔ a .fst in let d ≔ a .snd .fst in
    concat S (m n (m d c)) (m (m n d) c) (m (m n c) d) (ring_mul_assoc R n d c) (cring_mul_swap_right R (D .comm) n d c)

def frac_ldistr_rel (D : DecidableDomain) (a b c : FracPair D)
  : FracRel D (frac_pair_mul D a (frac_pair_add D b c)) (frac_pair_add D (frac_pair_mul D a b) (frac_pair_mul D a c))
  ≔ let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let ad ≔ R .add in let hc ≔ D .comm in
    let p ≔ a .fst in let q ≔ a .snd .fst in let x ≔ b .fst in let s ≔ b .snd .fst in
    let u ≔ c .fst in let v ≔ c .snd .fst in
    let l ≔ frac_pair_mul D a (frac_pair_add D b c) in
    let sc ≔ frac_scale D l q (a .snd .snd) in
    let rhs ≔ frac_pair_add D (frac_pair_mul D a b) (frac_pair_mul D a c) in
    frac_rel_trans D l sc rhs (frac_scale_rel D l q (a .snd .snd))
      (frac_rel_of_eq D sc rhs
        (calc
           m (m p (ad (m x v) (m u s))) q = m (ad (m p (m x v)) (m p (m u s))) q
             by refl ((t ↦ m t q) : S → S) (ring_ldistr R p (m x v) (m u s))
           = ad (m (m p (m x v)) q) (m (m p (m u s)) q) by ring_rdistr R (m p (m x v)) (m p (m u s)) q
           = ad (m (m p x) (m q v)) (m (m p u) (m q s))
             by refl ad (cring_frac_term R hc p x v q) (cring_frac_term R hc p u s q) ∎)
        (cring_frac_term R hc q s v q))

{` The ring of fractions. `}
def frac_add_assoc (D : DecidableDomain) (z w v : FracQ D)
  : Id (FracQ D) (frac_add D z (frac_add D w v)) (frac_add D (frac_add D z w) v)
  ≔ frac_ind_eq3 D (z w v ↦ frac_add D z (frac_add D w v)) (z w v ↦ frac_add D (frac_add D z w) v)
      (a b c ↦ frac_encode D (frac_pair_add D a (frac_pair_add D b c)) (frac_pair_add D (frac_pair_add D a b) c)
         (frac_add_assoc_rel D a b c)) z w v

def frac_mul_assoc (D : DecidableDomain) (z w v : FracQ D)
  : Id (FracQ D) (frac_mul D z (frac_mul D w v)) (frac_mul D (frac_mul D z w) v)
  ≔ frac_ind_eq3 D (z w v ↦ frac_mul D z (frac_mul D w v)) (z w v ↦ frac_mul D (frac_mul D z w) v)
      (a b c ↦ frac_encode D (frac_pair_mul D a (frac_pair_mul D b c)) (frac_pair_mul D (frac_pair_mul D a b) c)
         (frac_mul_assoc_rel D a b c)) z w v

def frac_mul_comm (D : DecidableDomain) (z w : FracQ D) : Id (FracQ D) (frac_mul D z w) (frac_mul D w z)
  ≔ frac_ind_eq2 D (z w ↦ frac_mul D z w) (z w ↦ frac_mul D w z)
      (a b ↦ frac_encode D (frac_pair_mul D a b) (frac_pair_mul D b a) (frac_mul_comm_rel D a b)) z w

def frac_ldistr (D : DecidableDomain) (z w v : FracQ D)
  : Id (FracQ D) (frac_mul D z (frac_add D w v)) (frac_add D (frac_mul D z w) (frac_mul D z v))
  ≔ frac_ind_eq3 D (z w v ↦ frac_mul D z (frac_add D w v)) (z w v ↦ frac_add D (frac_mul D z w) (frac_mul D z v))
      (a b c ↦ frac_encode D (frac_pair_mul D a (frac_pair_add D b c))
         (frac_pair_add D (frac_pair_mul D a b) (frac_pair_mul D a c)) (frac_ldistr_rel D a b c)) z w v

def frac_rdistr (D : DecidableDomain) (z w v : FracQ D)
  : Id (FracQ D) (frac_mul D (frac_add D z w) v) (frac_add D (frac_mul D z v) (frac_mul D w v))
  ≔ let Q ≔ FracQ D in
    calc
      frac_mul D (frac_add D z w) v = frac_mul D v (frac_add D z w) by frac_mul_comm D (frac_add D z w) v
      = frac_add D (frac_mul D v z) (frac_mul D v w) by frac_ldistr D v z w
      = frac_add D (frac_mul D z v) (frac_mul D w v) by refl (frac_add D) (frac_mul_comm D v z) (frac_mul_comm D v w) ∎

def frac_ring (D : DecidableDomain) : AbstractRing
  ≔ let Q ≔ FracQ D in
    (Q, frac_zero D, frac_add D, frac_neg D,
     (frac_set D,
      frac_ind_eq1 D (z ↦ frac_add D z (frac_zero D)) (z ↦ z)
        (a ↦ frac_encode D (frac_pair_add D a (frac_pair_zero D)) a (frac_add_unit_right_rel D a)),
      frac_ind_eq1 D (z ↦ frac_add D (frac_zero D) z) (z ↦ z)
        (a ↦ frac_encode D (frac_pair_add D (frac_pair_zero D) a) a (frac_add_unit_left_rel D a)),
      frac_add_assoc D,
      frac_ind_eq1 D (z ↦ frac_add D z (frac_neg D z)) (_ ↦ frac_zero D)
        (a ↦ frac_encode D (frac_pair_add D a (frac_pair_neg D a)) (frac_pair_zero D) (frac_add_inv_right_rel D a))),
     frac_one D, frac_mul D,
     (frac_set D,
      (z ↦ (frac_ind_eq1 D (z ↦ frac_mul D z (frac_one D)) (z ↦ z)
              (a ↦ frac_encode D (frac_pair_mul D a (frac_pair_one D)) a (frac_mul_one_right_rel D a)) z,
            frac_ind_eq1 D (z ↦ frac_mul D (frac_one D) z) (z ↦ z)
              (a ↦ frac_encode D (frac_pair_mul D (frac_pair_one D) a) a (frac_mul_one_left_rel D a)) z),
       frac_mul_assoc D)),
     (frac_ldistr D, frac_rdistr D))

def frac_non_trivial (D : DecidableDomain) : IsNonTrivialRing (frac_ring D)
  ≔ e ↦
    let R ≔ D .ring in let S ≔ R .carrier in
    let r ≔ frac_effective D (frac_pair_zero D) (frac_pair_one D) e in
    D .nontrivial
      (calc
         R .zero = R .mul (R .zero) (R .one) by inverse S (R .mul (R .zero) (R .one)) (R .zero) (ring_mul_one_right R (R .zero))
         = R .mul (R .one) (R .one) by r
         = R .one by ring_mul_one_right R (R .one) ∎)

def frac_non_invertibles_zero (D : DecidableDomain) : NonInvertiblesAreZero (frac_ring D)
  ≔ let Q ≔ FracQ D in let FR ≔ frac_ring D in
    frac_ind D (z ↦ Not (IsInvertible FR z) → Id Q z (frac_zero D))
      (z ↦ pi_prop (Not (IsInvertible FR z)) (_ ↦ Id Q z (frac_zero D)) (_ ↦ frac_set D z (frac_zero D)))
      (a ni ↦
        let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in
        let p ≔ a .fst in let q ≔ a .snd .fst in
        match D .dec p (R .zero) [
        | inl. e ↦ frac_encode D a (frac_pair_zero D)
            (calc
               m p (R .one) = p by ring_mul_one_right R p
               = R .zero by e
               = m (R .zero) q by inverse S (m (R .zero) q) (R .zero) (ring_mul_zero_left R q) ∎)
        | inr. ne ↦
          let b : FracPair D ≔ (q, (p, ne)) in
          match ni (invertible_intro FR (frac_class D a) (frac_class D b)
              (frac_encode D (frac_pair_mul D a b) (frac_pair_one D)
                (calc
                   m (m p q) (R .one) = m p q by ring_mul_one_right R (m p q)
                   = m q p by D .comm p q
                   = m (R .one) (m q p) by inverse S (m (R .one) (m q p)) (m q p) (ring_mul_one_left R (m q p)) ∎))
              (frac_encode D (frac_pair_mul D b a) (frac_pair_one D)
                (calc
                   m (m q p) (R .one) = m q p by ring_mul_one_right R (m q p)
                   = m p q by D .comm q p
                   = m (R .one) (m p q) by inverse S (m (R .one) (m p q)) (m p q) (ring_mul_one_left R (m p q)) ∎))) [ ] ])

{` The field of fractions. `}
def frac_field (D : DecidableDomain) : Field
  ≔ (frac_ring D,
     field_from_non_invertible_zero (frac_ring D) (frac_mul_comm D, frac_non_trivial D) (frac_non_invertibles_zero D))

{` d ↦ d/1 is a ring homomorphism D → Frac(D). `}
def frac_inclusion (D : DecidableDomain) : RingHom (D .ring) (frac_ring D)
  ≔ let R ≔ D .ring in let S ≔ R .carrier in
    ((d ↦ frac_class D (frac_pair_of D d),
      d e ↦ frac_encode D (frac_pair_of D (R .add d e)) (frac_pair_add D (frac_pair_of D d) (frac_pair_of D e))
        (frac_rel_of_eq D (frac_pair_of D (R .add d e)) (frac_pair_add D (frac_pair_of D d) (frac_pair_of D e))
          (refl (R .add) (inverse S (R .mul d (R .one)) d (ring_mul_one_right R d))
             (inverse S (R .mul e (R .one)) e (ring_mul_one_right R e)))
          (inverse S (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_right R (R .one))))),
     (refl (frac_one D),
      d e ↦ frac_encode D (frac_pair_of D (R .mul d e)) (frac_pair_mul D (frac_pair_of D d) (frac_pair_of D e))
        (frac_rel_of_eq D (frac_pair_of D (R .mul d e)) (frac_pair_mul D (frac_pair_of D d) (frac_pair_of D e))
          (refl (R .mul d e)) (inverse S (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_right R (R .one))))))
