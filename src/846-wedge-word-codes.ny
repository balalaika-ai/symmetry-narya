export "845-wedge-words"

{` Chapter 8 (congp.tex), lem:wedgeofgpoidisgpoid (congp.tex:627): the
   families C_1, C_2, the cocone (C_1, C_2, ua C_12) and the explicit data
   of the encode-decode argument for this cocone.

   For pointed types (A_1, a_1), (A_2, a_2) whose loop types have decidable
   equality, wedge_code1 A1 A2 x ≔ (a_1 = x) × tails (the book's C_1(x)) and
   wedge_code2 likewise; wedge_code1 A1 A2 a_1 ≡ WedgeWords A1 A2.  The book's
   family C over the wedge is defined in module 847 by wedge_rec from
   wedge_code_cocone; since the computation rules of the signature are only
   identifications, everything the proof needs about C is phrased in terms
   of an arbitrary cocone D of types (WedgeWordPackage), proved here for the
   cocone (C_1, C_2, ua C_12) and transported in module 847 along the
   computation law of wedge_rec.

   wedge_word_path1 a (p_0, n, p_1, ..., p_n) is the book's
   β(i_1 a)(p_0, ..., p_n) = i_1(p_0) i_2^g(p_1) i_1^g(p_2) ... (book order:
   the last letter is traversed first), and wedge_word_path2 is
   β(i_2 a)(p_0, ..., p_n) = i_2(p_0) g i_1^g(p_1) i_2^g(p_2) ....  The
   compatibility with the glue (wedge_word_glue_std) is the case analysis of
   C_12; the identity "α(β(c)) = c" at the base point is
   wedge_code_tail1_act (transport along the word of a tail t applied to
   (refl, 0) gives (refl, t)), the book's induction step. `}

def WedgeWords (A1 A2 : Pointed) : Type
  ≔ WsumString (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point))

def wedge_word_tail1 (A1 A2 : Pointed) : Type
  ≔ WsumTail (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point))

def wedge_word_tail2 (A1 A2 : Pointed) : Type
  ≔ WsumTail (Loop A2) (Loop A1) (refl (A2 .point)) (refl (A1 .point))

def WedgeLetter1 (A1 : Pointed) : Type ≔ WsumNontrivial (Loop A1) (refl (A1 .point))

{` The book's C_1, C_2 and C_12. `}
def wedge_code1 (A1 A2 : Pointed) (x : A1 .carrier) : Type
  ≔ Product (Id (A1 .carrier) (A1 .point) x) (wedge_word_tail1 A1 A2)

def wedge_code2 (A1 A2 : Pointed) (x : A2 .carrier) : Type
  ≔ Product (Id (A2 .carrier) (A2 .point) x) (wedge_word_tail2 A1 A2)

def wedge_code12 (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : Equiv (wedge_code1 A1 A2 (A1 .point)) (wedge_code2 A1 A2 (A2 .point))
  ≔ wsum_shift_equiv (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point)) d1 d2

def wedge_code_cocone (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : WedgeCocone A1 A2 Type
  ≔ (wedge_code1 A1 A2, (wedge_code2 A1 A2,
      ua (wedge_code1 A1 A2 (A1 .point)) (wedge_code2 A1 A2 (A2 .point)) (wedge_code12 A1 A2 d1 d2)))

{` Words as paths in the wedge. `}
def wedge_letter1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p : WedgeLetter1 A1)
  : Loop (wedge_pointed A1 A2 W)
  ≔ wedge_loop1 A1 A2 W (p .fst)

def wedge_letter2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (q : WedgeLetter1 A2)
  : Loop (wedge_pointed A1 A2 W)
  ≔ wedge_loop2 A1 A2 W (q .fst)

def wedge_tail1_loop (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (t : wedge_word_tail1 A1 A2)
  : Loop (wedge_pointed A1 A2 W)
  ≔ wsum_alt_loop (WedgeLetter1 A2) (WedgeLetter1 A1) (W .carrier) (wedge_point A1 A2 W)
      (wedge_letter2 A1 A2 W) (wedge_letter1 A1 A2 W) t

def wedge_tail2_loop (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (t : wedge_word_tail2 A1 A2)
  : Loop (wedge_pointed A1 A2 W)
  ≔ wsum_alt_loop (WedgeLetter1 A1) (WedgeLetter1 A2) (W .carrier) (wedge_point A1 A2 W)
      (wedge_letter1 A1 A2 W) (wedge_letter2 A1 A2 W) t

def wedge_based_paths (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (x : W .carrier) : Type
  ≔ Id (W .carrier) (wedge_point A1 A2 W) x

def wedge_word_path1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (a : A1 .carrier) (c : wedge_code1 A1 A2 a)
  : wedge_based_paths A1 A2 W (W .incl1 a)
  ≔ concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl1 a)
      (wedge_tail1_loop A1 A2 W (c .snd)) (refl (W .incl1) (c .fst))

def wedge_word_path2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (a : A2 .carrier) (c : wedge_code2 A1 A2 a)
  : wedge_based_paths A1 A2 W (W .incl2 a)
  ≔ concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl2 a)
      (wedge_tail2_loop A1 A2 W (c .snd))
      (concat (W .carrier) (wedge_point A1 A2 W) (W .incl2 (A2 .point)) (W .incl2 a) (W .glue) (refl (W .incl2) (c .fst)))

{` The book's β : C_1(a_1) → (a_12 = a_12) of the statement. `}
def wedge_words_compose (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (c : WedgeWords A1 A2)
  : Loop (wedge_pointed A1 A2 W)
  ≔ wedge_word_path1 A1 A2 W (A1 .point) c

{` Letter actions and evaluation for an arbitrary cocone D of types. `}
def wedge_cocone_act1 (A1 A2 : Pointed) (D : WedgeCocone A1 A2 Type) (p : Loop A1) (u : D .fst (A1 .point))
  : D .fst (A1 .point)
  ≔ transport (A1 .carrier) (D .fst) (A1 .point) (A1 .point) p u

def wedge_cocone_act2 (A1 A2 : Pointed) (D : WedgeCocone A1 A2 Type) (q : Loop A2) (u : D .fst (A1 .point))
  : D .fst (A1 .point)
  ≔ D .snd .snd .trl (transport (A2 .carrier) (D .snd .fst) (A2 .point) (A2 .point) q (D .snd .snd .trr u))

def wedge_cocone_tail1_act (A1 A2 : Pointed) (D : WedgeCocone A1 A2 Type) (t : wedge_word_tail1 A1 A2)
  (u : D .fst (A1 .point)) : D .fst (A1 .point)
  ≔ wsum_alt_act (WedgeLetter1 A2) (WedgeLetter1 A1) (D .fst (A1 .point))
      (q ↦ wedge_cocone_act2 A1 A2 D (q .fst)) (p ↦ wedge_cocone_act1 A1 A2 D (p .fst)) t u

def wedge_cocone_tail2_act (A1 A2 : Pointed) (D : WedgeCocone A1 A2 Type) (t : wedge_word_tail2 A1 A2)
  (u : D .fst (A1 .point)) : D .fst (A1 .point)
  ≔ wsum_alt_act (WedgeLetter1 A1) (WedgeLetter1 A2) (D .fst (A1 .point))
      (p ↦ wedge_cocone_act1 A1 A2 D (p .fst)) (q ↦ wedge_cocone_act2 A1 A2 D (q .fst)) t u

def wedge_cocone_eval (A1 A2 : Pointed) (D : WedgeCocone A1 A2 Type) (u0 : D .fst (A1 .point))
  (c : wedge_code1 A1 A2 (A1 .point)) : D .fst (A1 .point)
  ≔ transport (A1 .carrier) (D .fst) (A1 .point) (A1 .point) (c .fst) (wedge_cocone_tail1_act A1 A2 D (c .snd) u0)

{` What the encode-decode argument needs from a cocone D (module 847):
   a base point, maps to the explicit families (charts), compatibility of
   the word paths with the glue, β(chart(point)) = refl, and the section
   law chart(eval(c)) = c at a_1. `}
def WedgeWordPackage (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (D : WedgeCocone A1 A2 Type) : Type ≔ sig (
  point : D .fst (A1 .point),
  chart1 : (a : A1 .carrier) → D .fst a → wedge_code1 A1 A2 a,
  chart2 : (a : A2 .carrier) → D .snd .fst a → wedge_code2 A1 A2 a,
  glue : (u : D .fst (A1 .point)) (v : D .snd .fst (A2 .point)) (w : D .snd .snd u v)
    → Id (wedge_based_paths A1 A2 W) (W .glue)
        (wedge_word_path1 A1 A2 W (A1 .point) (chart1 (A1 .point) u))
        (wedge_word_path2 A1 A2 W (A2 .point) (chart2 (A2 .point) v)),
  base : Id (Loop (wedge_pointed A1 A2 W))
    (wedge_word_path1 A1 A2 W (A1 .point) (chart1 (A1 .point) point)) (refl (wedge_point A1 A2 W)),
  roundtrip : (c : wedge_code1 A1 A2 (A1 .point))
    → Id (wedge_code1 A1 A2 (A1 .point)) (chart1 (A1 .point) (wedge_cocone_eval A1 A2 D point c)) c)

{` Transport in (z ↦ (a = z) × T). `}
def wsum_transport_code (A : Type) (a : A) (T : Type) (y x : A) (p : Id A y x) (u : Id A a y) (t : T)
  : Id (Product (Id A a x) T) (transport A (z ↦ Product (Id A a z) T) y x p (u, t)) (concat A a y x u p, t)
  ≔ J A y (x p ↦ Id (Product (Id A a x) T) (transport A (z ↦ Product (Id A a z) T) y x p (u, t))
        (concat A a y x u p, t))
      (concat (Product (Id A a y) T) (transport A (z ↦ Product (Id A a z) T) y y (refl y) (u, t)) (u, t)
        (concat A a y y u (refl y), t)
        (transport_refl A (z ↦ Product (Id A a z) T) y (u, t))
        (refl ((v ↦ (v, t)) : Id A a y → Product (Id A a y) T)
          (inverse (Id A a y) (concat A a y y u (refl y)) u (concat_p1 A a y u))))
      x p

def wedge_code1_transport (A1 A2 : Pointed) (p : Loop A1) (t : wedge_word_tail1 A1 A2)
  : Id (wedge_code1 A1 A2 (A1 .point))
      (transport (A1 .carrier) (wedge_code1 A1 A2) (A1 .point) (A1 .point) p (refl (A1 .point), t)) (p, t)
  ≔ concat (wedge_code1 A1 A2 (A1 .point))
      (transport (A1 .carrier) (wedge_code1 A1 A2) (A1 .point) (A1 .point) p (refl (A1 .point), t))
      (concat (A1 .carrier) (A1 .point) (A1 .point) (A1 .point) (refl (A1 .point)) p, t) (p, t)
      (wsum_transport_code (A1 .carrier) (A1 .point) (wedge_word_tail1 A1 A2) (A1 .point) (A1 .point) p
        (refl (A1 .point)) t)
      (refl ((v ↦ (v, t)) : Loop A1 → wedge_code1 A1 A2 (A1 .point)) (concat_1p (A1 .carrier) (A1 .point) (A1 .point) p))

def wedge_code2_transport (A1 A2 : Pointed) (q : Loop A2) (t : wedge_word_tail2 A1 A2)
  : Id (wedge_code2 A1 A2 (A2 .point))
      (transport (A2 .carrier) (wedge_code2 A1 A2) (A2 .point) (A2 .point) q (refl (A2 .point), t)) (q, t)
  ≔ concat (wedge_code2 A1 A2 (A2 .point))
      (transport (A2 .carrier) (wedge_code2 A1 A2) (A2 .point) (A2 .point) q (refl (A2 .point), t))
      (concat (A2 .carrier) (A2 .point) (A2 .point) (A2 .point) (refl (A2 .point)) q, t) (q, t)
      (wsum_transport_code (A2 .carrier) (A2 .point) (wedge_word_tail2 A1 A2) (A2 .point) (A2 .point) q
        (refl (A2 .point)) t)
      (refl ((v ↦ (v, t)) : Loop A2 → wedge_code2 A1 A2 (A2 .point)) (concat_1p (A2 .carrier) (A2 .point) (A2 .point) q))

{` The induction step of the book (αβ = id): acting with the word of a tail
   t on (refl, 0) in the cocone (C_1, C_2, ua C_12) gives (refl, t). `}
def wedge_code_tail1_act_cons (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (q : WedgeLetter1 A2) (t' : wedge_word_tail2 A1 A2)
  (ih : Id (wedge_code1 A1 A2 (A1 .point))
    (wedge_cocone_tail2_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t' (refl (A1 .point), nil.))
    (wsum_head (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point)) t'))
  : Id (wedge_code1 A1 A2 (A1 .point))
      (wedge_cocone_act2 A1 A2 (wedge_code_cocone A1 A2 d1 d2) (q .fst)
        (wedge_cocone_tail2_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t' (refl (A1 .point), nil.)))
      (refl (A1 .point), cons. q t')
  ≔ let e ≔ wedge_code12 A1 A2 d1 d2 in
    let C1 ≔ wedge_code1 A1 A2 (A1 .point) in let C2 ≔ wedge_code2 A1 A2 (A2 .point) in
    let r1 ≔ refl (A1 .point) in let r2 ≔ refl (A2 .point) in
    let inv ≔ equiv_inverse_map C1 C2 e in
    let tr2 ≔ transport (A2 .carrier) (wedge_code2 A1 A2) (A2 .point) (A2 .point) (q .fst) in
    let sh ≔ wsum_shift (Loop A1) (Loop A2) r1 r2 d1 in
    calc
      inv (tr2 (sh (wedge_cocone_tail2_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t' (r1, nil.))))
      = inv (tr2 (sh (wsum_head (Loop A1) (Loop A2) r1 r2 t')))
        by refl ((u ↦ inv (tr2 (sh u))) : C1 → C1) ih
      = inv (tr2 (r2, t'))
        by refl ((v ↦ inv (tr2 v)) : C2 → C1) (wsum_shift_head (Loop A1) (Loop A2) r1 r2 d1 t')
      = inv (q .fst, t')
        by refl inv (wedge_code2_transport A1 A2 (q .fst) t')
      = inv (sh (r1, cons. q t'))
        by refl inv (inverse C2 (sh (r1, cons. q t')) (q .fst, t')
          (wsum_shift_trivial_head (Loop A1) (Loop A2) r1 r2 d1 (cons. q t')))
      = (r1, cons. q t')
        by equiv_retraction C1 C2 e (r1, cons. q t') ∎

def wedge_code_tail2_act_cons (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (p : WedgeLetter1 A1) (t'' : wedge_word_tail1 A1 A2)
  (ih : Id (wedge_code1 A1 A2 (A1 .point))
    (wedge_cocone_tail1_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t'' (refl (A1 .point), nil.))
    (refl (A1 .point), t''))
  : Id (wedge_code1 A1 A2 (A1 .point))
      (wedge_cocone_tail2_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) (cons. p t'') (refl (A1 .point), nil.))
      (p .fst, t'')
  ≔ let tr ≔ transport (A1 .carrier) (wedge_code1 A1 A2) (A1 .point) (A1 .point) (p .fst) in
    concat (wedge_code1 A1 A2 (A1 .point))
      (tr (wedge_cocone_tail1_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t'' (refl (A1 .point), nil.)))
      (tr (refl (A1 .point), t'')) (p .fst, t'')
      (refl tr ih) (wedge_code1_transport A1 A2 (p .fst) t'')

def wedge_code_tail1_act (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (t : wedge_word_tail1 A1 A2)
  : Id (wedge_code1 A1 A2 (A1 .point))
      (wedge_cocone_tail1_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) t (refl (A1 .point), nil.))
      (refl (A1 .point), t)
  ≔ match t [
  | nil. ↦ refl ((refl (A1 .point), nil.) : wedge_code1 A1 A2 (A1 .point))
  | cons. q t' ↦ match t' [
    | nil. ↦ wedge_code_tail1_act_cons A1 A2 d1 d2 q nil.
        (refl ((refl (A1 .point), nil.) : wedge_code1 A1 A2 (A1 .point)))
    | cons. p t'' ↦ wedge_code_tail1_act_cons A1 A2 d1 d2 q (cons. p t'')
        (wedge_code_tail2_act_cons A1 A2 d1 d2 p t'' (wedge_code_tail1_act A1 A2 d1 d2 t'')) ] ]

{` Path algebra for the glue. `}
def wedge_conj_glue_base (X : Type) (x : X) (m : Id X x x)
  : Id (Id X x x) (concat X x x x (concat X x x x (refl x) (concat X x x x m (inverse X x x (refl x)))) (refl x))
      (concat X x x x (refl x) m)
  ≔ calc
      concat X x x x (concat X x x x (refl x) (concat X x x x m (inverse X x x (refl x)))) (refl x)
      = concat X x x x (refl x) (concat X x x x m (inverse X x x (refl x)))
        by concat_p1 X x x (concat X x x x (refl x) (concat X x x x m (inverse X x x (refl x))))
      = concat X x x x m (inverse X x x (refl x))
        by concat_1p X x x (concat X x x x m (inverse X x x (refl x)))
      = concat X x x x m (refl x)
        by refl (concat X x x x m) (inverse_refl X x)
      = m by concat_p1 X x x m
      = concat X x x x (refl x) m by inverse (Id X x x) (concat X x x x (refl x) m) m (concat_1p X x x m) ∎

def wedge_conj_glue (X : Type) (x y : X) (g : Id X x y) (m : Id X y y)
  : Id (Id X x y) (concat X x x y (concat X x y x g (concat X y y x m (inverse X x y g))) g)
      (concat X x y y g m)
  ≔ J X x (y g ↦ (m : Id X y y) → Id (Id X x y) (concat X x x y (concat X x y x g (concat X y y x m (inverse X x y g))) g)
        (concat X x y y g m))
      (wedge_conj_glue_base X x) y g m

def wedge_conj_glue_algebra (X : Type) (z x y : X) (w : Id X z x) (g : Id X x y) (m : Id X y y)
  : Id (Id X z y) (concat X z x y (concat X z x x w (concat X x y x g (concat X y y x m (inverse X x y g)))) g)
      (concat X z x y w (concat X x y y g m))
  ≔ concat (Id X z y)
      (concat X z x y (concat X z x x w (concat X x y x g (concat X y y x m (inverse X x y g)))) g)
      (concat X z x y w (concat X x x y (concat X x y x g (concat X y y x m (inverse X x y g))) g))
      (concat X z x y w (concat X x y y g m))
      (concat_assoc X z x x y w (concat X x y x g (concat X y y x m (inverse X x y g))) g)
      (refl (concat X z x y w) (wedge_conj_glue X x y g m))

{` Compatibility of the word paths with the glue, by the cases of C_12. `}
def wedge_glue_head (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (t : wedge_word_tail1 A1 A2)
  : Id (wedge_based_paths A1 A2 W (W .incl2 (A2 .point)))
      (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl2 (A2 .point))
        (wedge_tail1_loop A1 A2 W t) (W .glue))
      (wedge_word_path2 A1 A2 W (A2 .point)
        (wsum_head (Loop A2) (Loop A1) (refl (A2 .point)) (refl (A1 .point)) t))
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in let y ≔ W .incl2 (A2 .point) in
    match t [
  | nil. ↦ refl (concat X x x y (refl x)) (inverse (Id X x y) (concat X x y y (W .glue) (refl y)) (W .glue)
      (concat_p1 X x y (W .glue)))
  | cons. q t' ↦ wedge_conj_glue_algebra X x x y (wedge_tail2_loop A1 A2 W t') (W .glue) (refl (W .incl2) (q .fst)) ]

def wedge_glue_trivial (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p0 : Loop A1)
  (e : Id (Loop A1) p0 (refl (A1 .point))) (m : Loop (wedge_pointed A1 A2 W))
  : Id (wedge_based_paths A1 A2 W (W .incl2 (A2 .point)))
      (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl2 (A2 .point))
        (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (wedge_point A1 A2 W) m (refl (W .incl1) p0))
        (W .glue))
      (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl2 (A2 .point)) m (W .glue))
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in let y ≔ W .incl2 (A2 .point) in
    concat (Id X x y) (concat X x x y (concat X x x x m (refl (W .incl1) p0)) (W .glue))
      (concat X x x y (concat X x x x m (refl x)) (W .glue))
      (concat X x x y m (W .glue))
      (refl ((z ↦ concat X x x y (concat X x x x m (refl (W .incl1) z)) (W .glue)) : Loop A1 → Id X x y) e)
      (refl ((z ↦ concat X x x y z (W .glue)) : Id X x x → Id X x y) (concat_p1 X x x m))

def wedge_glue_eq_aux (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (p0 : Loop A1)
  (dp : Decidable (Id (Loop A1) p0 (refl (A1 .point)))) (t : wedge_word_tail1 A1 A2)
  : Id (wedge_based_paths A1 A2 W (W .incl2 (A2 .point)))
      (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (W .incl2 (A2 .point))
        (wedge_word_path1 A1 A2 W (A1 .point) (p0, t)) (W .glue))
      (wedge_word_path2 A1 A2 W (A2 .point)
        (wsum_shift_aux (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point)) p0 dp t))
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in let y ≔ W .incl2 (A2 .point) in
    match dp [
  | inl. e ↦ concat (Id X x y)
      (concat X x x y (wedge_word_path1 A1 A2 W (A1 .point) (p0, t)) (W .glue))
      (concat X x x y (wedge_tail1_loop A1 A2 W t) (W .glue))
      (wedge_word_path2 A1 A2 W (A2 .point) (wsum_head (Loop A2) (Loop A1) (refl (A2 .point)) (refl (A1 .point)) t))
      (wedge_glue_trivial A1 A2 W p0 e (wedge_tail1_loop A1 A2 W t))
      (wedge_glue_head A1 A2 W t)
  | inr. n ↦ refl (concat X x x y (wedge_word_path1 A1 A2 W (A1 .point) (p0, t)))
      (inverse (Id X x y) (concat X x y y (W .glue) (refl y)) (W .glue) (concat_p1 X x y (W .glue))) ]

def wedge_word_glue_std (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (u : wedge_code1 A1 A2 (A1 .point)) (v : wedge_code2 A1 A2 (A2 .point))
  (w : wedge_code_cocone A1 A2 d1 d2 .snd .snd u v)
  : Id (wedge_based_paths A1 A2 W) (W .glue) (wedge_word_path1 A1 A2 W (A1 .point) u)
      (wedge_word_path2 A1 A2 W (A2 .point) v)
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in let y ≔ W .incl2 (A2 .point) in
    pathover_of_eq X (wedge_based_paths A1 A2 W) x y (W .glue)
      (wedge_word_path1 A1 A2 W (A1 .point) u) (wedge_word_path2 A1 A2 W (A2 .point) v)
      (concat (Id X x y) (concat X x x y (wedge_word_path1 A1 A2 W (A1 .point) u) (W .glue))
        (wedge_word_path2 A1 A2 W (A2 .point) (wedge_code12 A1 A2 d1 d2 .map u))
        (wedge_word_path2 A1 A2 W (A2 .point) v)
        (wedge_glue_eq_aux A1 A2 W (u .fst) (d1 (u .fst) (refl (A1 .point))) (u .snd))
        (refl (wedge_word_path2 A1 A2 W (A2 .point)) (w .unglue)))

def wedge_word_section_std (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (c : wedge_code1 A1 A2 (A1 .point))
  : Id (wedge_code1 A1 A2 (A1 .point))
      (wedge_cocone_eval A1 A2 (wedge_code_cocone A1 A2 d1 d2) (refl (A1 .point), nil.) c) c
  ≔ let tr ≔ transport (A1 .carrier) (wedge_code1 A1 A2) (A1 .point) (A1 .point) (c .fst) in
    concat (wedge_code1 A1 A2 (A1 .point))
      (tr (wedge_cocone_tail1_act A1 A2 (wedge_code_cocone A1 A2 d1 d2) (c .snd) (refl (A1 .point), nil.)))
      (tr (refl (A1 .point), c .snd)) c
      (refl tr (wedge_code_tail1_act A1 A2 d1 d2 (c .snd)))
      (wedge_code1_transport A1 A2 (c .fst) (c .snd))

def wedge_word_package_std (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : WedgeWordPackage A1 A2 W (wedge_code_cocone A1 A2 d1 d2)
  ≔ (point ≔ (refl (A1 .point), nil.),
     chart1 ≔ a c ↦ c,
     chart2 ≔ a c ↦ c,
     glue ≔ u v w ↦ wedge_word_glue_std A1 A2 W d1 d2 u v w,
     base ≔ concat_p1 (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (refl (wedge_point A1 A2 W)),
     roundtrip ≔ c ↦ wedge_word_section_std A1 A2 d1 d2 c)
