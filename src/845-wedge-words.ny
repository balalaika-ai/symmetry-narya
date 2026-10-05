export "841-wedge-signatures"

{` Chapter 8 (congp.tex), lem:wedgeofgpoidisgpoid (congp.tex:627), the
   combinatorial part: the strings (p_0, n, p_1, ..., p_n) and the map C_12.

   The book's C_1(a_1) consists of strings (p_0, n, p_1, ..., p_n) with
   p_0 : a_1 = a_1 arbitrary and p_1, p_2, ... alternating between
   non-reflexivity symmetries of a_2 and of a_1.  Here the tail
   (n, p_1, ..., p_n) is an element of the inductive type WsumAlt X Y of
   alternating lists x_1 y_2 x_3 ... (x_j : X for odd j, y_j : Y for even j);
   n is its length (wsum_alt_length).  WsumString L1 L2 r1 r2 is the type of
   strings for loop types L_i with reflexivities r_i: a symmetry p_0 : L1
   followed by an alternating tail of letters of L2 \ {r2}, L1 \ {r1}, ...

   wsum_shift is the book's C_12 : C_1(a_1) → C_2(a_2), by its printed case
   distinction (wsum_shift_trivial_head: p_0 = refl; wsum_shift_nontrivial_head:
   p_0 ≠ refl, so (p_0, n, p_1, ...) ↦ (refl, n+1, p_0, p_1, ...)); the
   printed table for n < 3 consists of instances of these two laws.  The
   inverse of C_12 is the same construction with the roles of the two loop
   types exchanged, so wsum_shift_equiv shows that C_12 is an equivalence.
   Everything is generic: no wedge is involved in this module. `}

{` Alternating lists x_1 y_2 x_3 y_4 ... `}
def WsumAlt (X Y : Type) : Type ≔ data [ nil. | cons. (x : X) (t : WsumAlt Y X) ]

def wsum_alt_length (X Y : Type) (t : WsumAlt X Y) : Nat
  ≔ match t [ nil. ↦ zero. | cons. _ t' ↦ suc. (wsum_alt_length Y X t') ]

def WsumAltCode (X Y : Type) (s t : WsumAlt X Y) : Type ≔ match s, t [
  | nil., nil. ↦ Unit
  | nil., cons. _ _ ↦ Empty
  | cons. _ _, nil. ↦ Empty
  | cons. x s', cons. y t' ↦ Product (Id X x y) (Id (WsumAlt Y X) s' t') ]

def wsum_alt_encode (X Y : Type) (s t : WsumAlt X Y) (p : Id (WsumAlt X Y) s t) : WsumAltCode X Y s t
  ≔ match p [ nil. ⤇ star. | cons. x t ⤇ (x.2, t.2) ]

def wsum_alt_decide_cons (X Y : Type) (x y : X) (s t : WsumAlt Y X)
  (d : Decidable (Id X x y)) (e : Decidable (Id (WsumAlt Y X) s t))
  : Decidable (Id (WsumAlt X Y) (cons. x s) (cons. y t))
  ≔ match d [
  | inr. n ↦ inr. (p ↦ n (wsum_alt_encode X Y (cons. x s) (cons. y t) p .fst))
  | inl. q ↦ match e [
    | inl. r ↦ inl. (cons. q r)
    | inr. n ↦ inr. (p ↦ n (wsum_alt_encode X Y (cons. x s) (cons. y t) p .snd)) ] ]

def wsum_alt_decidable_equality (X Y : Type) (dX : DecidableEquality X) (dY : DecidableEquality Y)
  (s t : WsumAlt X Y) : Decidable (Id (WsumAlt X Y) s t)
  ≔ match s, t [
  | nil., nil. ↦ inl. (refl (nil. : WsumAlt X Y))
  | nil., cons. y t' ↦ inr. (p ↦ wsum_alt_encode X Y nil. (cons. y t') p)
  | cons. x s', nil. ↦ inr. (p ↦ wsum_alt_encode X Y (cons. x s') nil. p)
  | cons. x s', cons. y t' ↦
      wsum_alt_decide_cons X Y x y s' t' (dX x y) (wsum_alt_decidable_equality Y X dY dX s' t') ]

{` Letters: symmetries that are not reflexivity (p ≠ refl). `}
def WsumNontrivial (L : Type) (r : L) : Type ≔ Σ L (p ↦ Not (Id L p r))

def wsum_nontrivial_path (L : Type) (r : L) (u v : WsumNontrivial L r) (p : Id L (u .fst) (v .fst))
  : Id (WsumNontrivial L r) u v
  ≔ subtype_equal L (p ↦ Not (Id L p r)) (p ↦ negation_prop (Id L p r)) u v p

def wsum_nontrivial_decidable_equality (L : Type) (r : L) (d : DecidableEquality L) (u v : WsumNontrivial L r)
  : Decidable (Id (WsumNontrivial L r) u v)
  ≔ match d (u .fst) (v .fst) [
  | inl. p ↦ inl. (wsum_nontrivial_path L r u v p)
  | inr. n ↦ inr. (q ↦ n (refl ((z ↦ z .fst) : WsumNontrivial L r → L) q)) ]

{` Tails (n, p_1, ..., p_n) with p_1 ∈ L2, p_2 ∈ L1, ..., and strings. `}
def WsumTail (L1 L2 : Type) (r1 : L1) (r2 : L2) : Type
  ≔ WsumAlt (WsumNontrivial L2 r2) (WsumNontrivial L1 r1)

def WsumString (L1 L2 : Type) (r1 : L1) (r2 : L2) : Type ≔ Product L1 (WsumTail L1 L2 r1 r2)

def wsum_product_decidable_equality (A B : Type) (dA : DecidableEquality A) (dB : DecidableEquality B)
  (u v : Product A B) : Decidable (Id (Product A B) u v)
  ≔ match dA (u .fst) (v .fst) [
  | inr. n ↦ inr. (q ↦ n (q .fst))
  | inl. p ↦ match dB (u .snd) (v .snd) [
    | inr. n ↦ inr. (q ↦ n (q .snd))
    | inl. s ↦ inl. (p, s) ] ]

def wsum_string_decidable_equality (L1 L2 : Type) (r1 : L1) (r2 : L2)
  (d1 : DecidableEquality L1) (d2 : DecidableEquality L2) : DecidableEquality (WsumString L1 L2 r1 r2)
  ≔ wsum_product_decidable_equality L1 (WsumTail L1 L2 r1 r2) d1
      (wsum_alt_decidable_equality (WsumNontrivial L2 r2) (WsumNontrivial L1 r1)
        (wsum_nontrivial_decidable_equality L2 r2 d2) (wsum_nontrivial_decidable_equality L1 r1 d1))

{` The string (p_1, n-1, p_2, ..., p_n) obtained from a tail whose first
   letter p_1 is promoted to the head, or (refl, 0) for the empty tail. `}
def wsum_head (L1 L2 : Type) (r1 : L1) (r2 : L2) (t : WsumTail L2 L1 r2 r1) : WsumString L1 L2 r1 r2
  ≔ match t [ nil. ↦ (r1, nil.) | cons. p t' ↦ (p .fst, t') ]

{` C_12, with the decision whether p_0 = refl as an argument. `}
def wsum_shift_aux (L1 L2 : Type) (r1 : L1) (r2 : L2) (p0 : L1) (dp : Decidable (Id L1 p0 r1))
  (t : WsumTail L1 L2 r1 r2) : WsumString L2 L1 r2 r1
  ≔ match dp [ inl. _ ↦ wsum_head L2 L1 r2 r1 t | inr. n ↦ (r2, cons. (p0, n) t) ]

def wsum_shift (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1) (c : WsumString L1 L2 r1 r2)
  : WsumString L2 L1 r2 r1
  ≔ wsum_shift_aux L1 L2 r1 r2 (c .fst) (d1 (c .fst) r1) (c .snd)

def wsum_shift_aux_refl (L1 L2 : Type) (r1 : L1) (r2 : L2) (dp : Decidable (Id L1 r1 r1))
  (t : WsumTail L1 L2 r1 r2)
  : Id (WsumString L2 L1 r2 r1) (wsum_shift_aux L1 L2 r1 r2 r1 dp t) (wsum_head L2 L1 r2 r1 t)
  ≔ match dp [
  | inl. _ ↦ refl (wsum_head L2 L1 r2 r1 t)
  | inr. n ↦ absurd (Id (WsumString L2 L1 r2 r1) (wsum_shift_aux L1 L2 r1 r2 r1 (inr. n) t)
      (wsum_head L2 L1 r2 r1 t)) (n (refl r1)) ]

def wsum_shift_aux_nontrivial (L1 L2 : Type) (r1 : L1) (r2 : L2) (p : WsumNontrivial L1 r1)
  (dp : Decidable (Id L1 (p .fst) r1)) (t : WsumTail L1 L2 r1 r2)
  : Id (WsumString L2 L1 r2 r1) (wsum_shift_aux L1 L2 r1 r2 (p .fst) dp t) (r2, cons. p t)
  ≔ match dp [
  | inl. e ↦ absurd (Id (WsumString L2 L1 r2 r1) (wsum_shift_aux L1 L2 r1 r2 (p .fst) (inl. e) t)
      (r2, cons. p t)) (p .snd e)
  | inr. n ↦ refl ((u ↦ (r2, cons. u t)) : WsumNontrivial L1 r1 → WsumString L2 L1 r2 r1)
      (wsum_nontrivial_path L1 r1 (p .fst, n) p (refl (p .fst))) ]

{` The two cases of the book's formula for C_12. `}
def wsum_shift_trivial_head (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (t : WsumTail L1 L2 r1 r2)
  : Id (WsumString L2 L1 r2 r1) (wsum_shift L1 L2 r1 r2 d1 (r1, t)) (wsum_head L2 L1 r2 r1 t)
  ≔ wsum_shift_aux_refl L1 L2 r1 r2 (d1 r1 r1) t

def wsum_shift_nontrivial_head (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (p : WsumNontrivial L1 r1) (t : WsumTail L1 L2 r1 r2)
  : Id (WsumString L2 L1 r2 r1) (wsum_shift L1 L2 r1 r2 d1 (p .fst, t)) (r2, cons. p t)
  ≔ wsum_shift_aux_nontrivial L1 L2 r1 r2 p (d1 (p .fst) r1) t

{` C_12 sends the head of a tail t to (refl, t). `}
def wsum_shift_head (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (t : WsumTail L2 L1 r2 r1)
  : Id (WsumString L2 L1 r2 r1) (wsum_shift L1 L2 r1 r2 d1 (wsum_head L1 L2 r1 r2 t)) (r2, t)
  ≔ match t [
  | nil. ↦ wsum_shift_aux_refl L1 L2 r1 r2 (d1 r1 r1) nil.
  | cons. p t'' ↦ wsum_shift_aux_nontrivial L1 L2 r1 r2 p (d1 (p .fst) r1) t'' ]

def wsum_shift_inverse_aux (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (d2 : DecidableEquality L2) (p0 : L1) (dp : Decidable (Id L1 p0 r1)) (t : WsumTail L1 L2 r1 r2)
  : Id (WsumString L1 L2 r1 r2) (wsum_shift L2 L1 r2 r1 d2 (wsum_shift_aux L1 L2 r1 r2 p0 dp t)) (p0, t)
  ≔ match dp [
  | inl. e ↦ concat (WsumString L1 L2 r1 r2)
      (wsum_shift L2 L1 r2 r1 d2 (wsum_head L2 L1 r2 r1 t)) (r1, t) (p0, t)
      (wsum_shift_head L2 L1 r2 r1 d2 t)
      (refl ((z ↦ (z, t)) : L1 → WsumString L1 L2 r1 r2) (inverse L1 p0 r1 e))
  | inr. n ↦ wsum_shift_aux_refl L2 L1 r2 r1 (d2 r2 r2) (cons. (p0, n) t) ]

def wsum_shift_inverse (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (d2 : DecidableEquality L2) (c : WsumString L1 L2 r1 r2)
  : Id (WsumString L1 L2 r1 r2) (wsum_shift L2 L1 r2 r1 d2 (wsum_shift L1 L2 r1 r2 d1 c)) c
  ≔ wsum_shift_inverse_aux L1 L2 r1 r2 d1 d2 (c .fst) (d1 (c .fst) r1) (c .snd)

{` C_12 is an equivalence; its inverse is C_12 with the roles exchanged. `}
def wsum_shift_equiv (L1 L2 : Type) (r1 : L1) (r2 : L2) (d1 : DecidableEquality L1)
  (d2 : DecidableEquality L2) : Equiv (WsumString L1 L2 r1 r2) (WsumString L2 L1 r2 r1)
  ≔ quasi_inverse_equiv (WsumString L1 L2 r1 r2) (WsumString L2 L1 r2 r1)
      (wsum_shift L1 L2 r1 r2 d1) (wsum_shift L2 L1 r2 r1 d2)
      (wsum_shift_inverse L1 L2 r1 r2 d1 d2) (wsum_shift_inverse L2 L1 r2 r1 d2 d1)

{` Composing and acting along alternating words (generic). `}
def wsum_alt_loop (X Y Z : Type) (z : Z) (fX : X → Id Z z z) (fY : Y → Id Z z z) (t : WsumAlt X Y)
  : Id Z z z
  ≔ match t [ nil. ↦ refl z | cons. x t' ↦ concat Z z z z (wsum_alt_loop Y X Z z fY fX t') (fX x) ]

def wsum_alt_act (X Y U : Type) (aX : X → U → U) (aY : Y → U → U) (t : WsumAlt X Y) (u : U) : U
  ≔ match t [ nil. ↦ u | cons. x t' ↦ aX x (wsum_alt_act Y X U aY aX t' u) ]

def wsum_alt_transport (X Y Z : Type) (Q : Z → Type) (z : Z) (fX : X → Id Z z z) (fY : Y → Id Z z z)
  (aX : X → Q z → Q z) (aY : Y → Q z → Q z)
  (hX : (x : X) (u : Q z) → Id (Q z) (transport Z Q z z (fX x) u) (aX x u))
  (hY : (y : Y) (u : Q z) → Id (Q z) (transport Z Q z z (fY y) u) (aY y u))
  (t : WsumAlt X Y) (u : Q z)
  : Id (Q z) (transport Z Q z z (wsum_alt_loop X Y Z z fX fY t) u) (wsum_alt_act X Y (Q z) aX aY t u)
  ≔ match t [
  | nil. ↦ transport_refl Z Q z u
  | cons. x t' ↦
      let l ≔ wsum_alt_loop Y X Z z fY fX t' in
      let v ≔ wsum_alt_act Y X (Q z) aY aX t' u in
      concat (Q z) (transport Z Q z z (concat Z z z z l (fX x)) u)
        (transport Z Q z z (fX x) (transport Z Q z z l u)) (aX x v)
        (transport_concat Z Q z z z l (fX x) u)
        (concat (Q z) (transport Z Q z z (fX x) (transport Z Q z z l u)) (transport Z Q z z (fX x) v) (aX x v)
          (refl (transport Z Q z z (fX x)) (wsum_alt_transport Y X Z Q z fY fX aY aX hY hX t' u))
          (hX x v)) ]
