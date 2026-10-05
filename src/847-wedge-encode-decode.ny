export "846-wedge-word-codes"

{` Chapter 8 (congp.tex), lem:wedgeofgpoidisgpoid (congp.tex:627): the
   encode-decode argument and its consequences for an arbitrary wedge
   signature W of pointed types (A_1, a_1), (A_2, a_2) whose loop types have
   decidable equality.

   wedge_word_code is the book's family C : A_1 ∨ A_2 → U, defined by
   wedge_rec from (C_1, C_2, ua C_12).  Its computation rules are
   identifications (wedge_rec_beta), so the explicit data of module 846 are
   transported along wedge_rec_beta (wedge_word_package): C(i_1 x) is
   related to C_1(x) by the transported charts instead of being equal by
   definition.  α (wedge_word_encode) is transport of the point (refl, 0),
   β (wedge_word_decode) is defined by wedge induction from the word paths
   (the glue datum is the compatibility with C_12), and βα = id by path
   induction (wedge_word_decode_encode).  For the base point the book's
   αβ = id becomes wedge_words_roundtrip, proved from the transport
   computation of module 846 (the book's induction step), so that the
   displayed β : C_1(a_1) → (a_12 = a_12) is an equivalence
   (wedge_words_equiv; its map is wedge_words_compose by definition).
   The fiberwise statement C(x) ≃ (a_12 = x) for all x is not needed for the
   lemma's conclusions and is not formalized.

   Consequences: the symmetries of a_12 have decidable equality and form a
   set (wedge_loops_decidable_equality, wedge_loops_set), and if A_1, A_2
   are connected, A_1 ∨ A_2 is a groupoid (wedge_decidable_groupoid); the
   groupoid hypotheses on A_1, A_2 are not needed for this. `}

def wedge_word_code (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) : W .carrier → Type
  ≔ wedge_rec A1 A2 W Type (wedge_code_cocone A1 A2 d1 d2)

def wedge_word_package (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : WedgeWordPackage A1 A2 W (wedge_cocone A1 A2 W Type (wedge_word_code A1 A2 W d1 d2))
  ≔ refl (WedgeWordPackage A1 A2 W) (wedge_rec_beta A1 A2 W Type (wedge_code_cocone A1 A2 d1 d2))
      .trl (wedge_word_package_std A1 A2 W d1 d2)

{` α: transport of (refl, 0) along a path from a_12. `}
def wedge_word_encode (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (x : W .carrier) (p : wedge_based_paths A1 A2 W x) : wedge_word_code A1 A2 W d1 d2 x
  ≔ transport (W .carrier) (wedge_word_code A1 A2 W d1 d2) (wedge_point A1 A2 W) x p
      (wedge_word_package A1 A2 W d1 d2 .point)

def wedge_word_decode_boundary (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : wedge_boundary A1 A2 W (x ↦ wedge_word_code A1 A2 W d1 d2 x → wedge_based_paths A1 A2 W x)
  ≔ let K ≔ wedge_word_package A1 A2 W d1 d2 in
    (a u ↦ wedge_word_path1 A1 A2 W a (K .chart1 a u),
     (a v ↦ wedge_word_path2 A1 A2 W a (K .chart2 a v),
      u ⤇ K .glue u.0 u.1 u.2))

{` β: composition of the letters of a string, by wedge induction. `}
def wedge_word_decode (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : (x : W .carrier) → wedge_word_code A1 A2 W d1 d2 x → wedge_based_paths A1 A2 W x
  ≔ wedge_ind A1 A2 W (x ↦ wedge_word_code A1 A2 W d1 d2 x → wedge_based_paths A1 A2 W x)
      (wedge_word_decode_boundary A1 A2 W d1 d2)

def wedge_word_decode_incl1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (a : A1 .carrier) (u : wedge_word_code A1 A2 W d1 d2 (W .incl1 a))
  : Id (wedge_based_paths A1 A2 W (W .incl1 a)) (wedge_word_decode A1 A2 W d1 d2 (W .incl1 a) u)
      (wedge_word_path1 A1 A2 W a (wedge_word_package A1 A2 W d1 d2 .chart1 a u))
  ≔ wedge_ind_incl1 A1 A2 W (x ↦ wedge_word_code A1 A2 W d1 d2 x → wedge_based_paths A1 A2 W x)
      (wedge_word_decode_boundary A1 A2 W d1 d2) a (refl u)

{` βα = id, by path induction. `}
def wedge_word_decode_encode (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (x : W .carrier) (p : wedge_based_paths A1 A2 W x)
  : Id (wedge_based_paths A1 A2 W x) (wedge_word_decode A1 A2 W d1 d2 x (wedge_word_encode A1 A2 W d1 d2 x p)) p
  ≔ let X ≔ W .carrier in let a12 ≔ wedge_point A1 A2 W in
    let Q ≔ wedge_word_code A1 A2 W d1 d2 in let K ≔ wedge_word_package A1 A2 W d1 d2 in
    let dec ≔ wedge_word_decode A1 A2 W d1 d2 in
    J X a12 (x p ↦ Id (wedge_based_paths A1 A2 W x) (dec x (wedge_word_encode A1 A2 W d1 d2 x p)) p)
      (calc
        dec a12 (transport X Q a12 a12 (refl a12) (K .point))
        = dec a12 (K .point) by refl (dec a12) (transport_refl X Q a12 (K .point))
        = wedge_word_path1 A1 A2 W (A1 .point) (K .chart1 (A1 .point) (K .point))
          by wedge_word_decode_incl1 A1 A2 W d1 d2 (A1 .point) (K .point)
        = refl a12 by K .base ∎)
      x p

{` Transport along the word of a tail is the cocone action (any family). `}
def wedge_transport_inverse (Z : Type) (Q : Z → Type) (x y : Z) (g : Id Z x y) (v : Q y)
  : Id (Q x) (transport Z Q y x (inverse Z x y g) v) (refl Q g .trl v)
  ≔ J Z x (y g ↦ (v : Q y) → Id (Q x) (transport Z Q y x (inverse Z x y g) v) (refl Q g .trl v))
      (v ↦ calc
        transport Z Q x x (inverse Z x x (refl x)) v
        = transport Z Q x x (refl x) v by transport2 Z Q x x (inverse Z x x (refl x)) (refl x) (inverse_refl Z x) v
        = v by transport_refl Z Q x v
        = refl Q (refl x) .trl v by inverse (Q x) (refl Q (refl x) .trl v) v (refl Q (refl x) .liftl v) ∎)
      y g v

def wedge_letter2_transport (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (Q : W .carrier → Type)
  (q : WedgeLetter1 A2) (u : Q (wedge_point A1 A2 W))
  : Id (Q (wedge_point A1 A2 W))
      (transport (W .carrier) Q (wedge_point A1 A2 W) (wedge_point A1 A2 W) (wedge_letter2 A1 A2 W q) u)
      (wedge_cocone_act2 A1 A2 (wedge_cocone A1 A2 W Type Q) (q .fst) u)
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in let y ≔ W .incl2 (A2 .point) in
    let g ≔ W .glue in let m ≔ refl (W .incl2) (q .fst) in
    calc
      transport X Q x x (concat X x y x g (concat X y y x m (inverse X x y g))) u
      = transport X Q y x (concat X y y x m (inverse X x y g)) (transport X Q x y g u)
        by transport_concat X Q x y x g (concat X y y x m (inverse X x y g)) u
      = transport X Q y x (inverse X x y g) (transport X Q y y m (transport X Q x y g u))
        by transport_concat X Q y y x m (inverse X x y g) (transport X Q x y g u)
      = refl Q g .trl (transport X Q y y m (transport X Q x y g u))
        by wedge_transport_inverse X Q x y g (transport X Q y y m (transport X Q x y g u)) ∎

def wedge_tail1_transport (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (Q : W .carrier → Type)
  (t : wedge_word_tail1 A1 A2) (u : Q (wedge_point A1 A2 W))
  : Id (Q (wedge_point A1 A2 W))
      (transport (W .carrier) Q (wedge_point A1 A2 W) (wedge_point A1 A2 W) (wedge_tail1_loop A1 A2 W t) u)
      (wedge_cocone_tail1_act A1 A2 (wedge_cocone A1 A2 W Type Q) t u)
  ≔ let D ≔ wedge_cocone A1 A2 W Type Q in
    wsum_alt_transport (WedgeLetter1 A2) (WedgeLetter1 A1) (W .carrier) Q (wedge_point A1 A2 W)
      (wedge_letter2 A1 A2 W) (wedge_letter1 A1 A2 W)
      (q ↦ wedge_cocone_act2 A1 A2 D (q .fst)) (p ↦ wedge_cocone_act1 A1 A2 D (p .fst))
      (q v ↦ wedge_letter2_transport A1 A2 W Q q v)
      (p v ↦ refl (wedge_cocone_act1 A1 A2 D (p .fst) v))
      t u

{` The book's αβ = id at the base point, with α followed by the chart. `}
def wedge_words_decompose (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (p : Loop (wedge_pointed A1 A2 W)) : WedgeWords A1 A2
  ≔ wedge_word_package A1 A2 W d1 d2 .chart1 (A1 .point) (wedge_word_encode A1 A2 W d1 d2 (wedge_point A1 A2 W) p)

def wedge_words_roundtrip (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) (c : WedgeWords A1 A2)
  : Id (WedgeWords A1 A2) (wedge_words_decompose A1 A2 W d1 d2 (wedge_words_compose A1 A2 W c)) c
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in
    let Q ≔ wedge_word_code A1 A2 W d1 d2 in let K ≔ wedge_word_package A1 A2 W d1 d2 in
    let D ≔ wedge_cocone A1 A2 W Type Q in
    let ch ≔ K .chart1 (A1 .point) in
    let tr1 ≔ transport (A1 .carrier) (D .fst) (A1 .point) (A1 .point) (c .fst) in
    calc
      ch (transport X Q x x (concat X x x x (wedge_tail1_loop A1 A2 W (c .snd)) (refl (W .incl1) (c .fst))) (K .point))
      = ch (tr1 (transport X Q x x (wedge_tail1_loop A1 A2 W (c .snd)) (K .point)))
        by refl ch (transport_concat X Q x x x (wedge_tail1_loop A1 A2 W (c .snd)) (refl (W .incl1) (c .fst)) (K .point))
      = ch (tr1 (wedge_cocone_tail1_act A1 A2 D (c .snd) (K .point)))
        by refl ((v ↦ ch (tr1 v)) : Q x → WedgeWords A1 A2) (wedge_tail1_transport A1 A2 W Q (c .snd) (K .point))
      = c by K .roundtrip c ∎

def wedge_words_compose_decompose (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) (p : Loop (wedge_pointed A1 A2 W))
  : Id (Loop (wedge_pointed A1 A2 W)) (wedge_words_compose A1 A2 W (wedge_words_decompose A1 A2 W d1 d2 p)) p
  ≔ let x ≔ wedge_point A1 A2 W in
    let u ≔ wedge_word_encode A1 A2 W d1 d2 x p in
    concat (Loop (wedge_pointed A1 A2 W)) (wedge_words_compose A1 A2 W (wedge_words_decompose A1 A2 W d1 d2 p))
      (wedge_word_decode A1 A2 W d1 d2 x u) p
      (inverse (Loop (wedge_pointed A1 A2 W)) (wedge_word_decode A1 A2 W d1 d2 x u)
        (wedge_words_compose A1 A2 W (wedge_words_decompose A1 A2 W d1 d2 p))
        (wedge_word_decode_incl1 A1 A2 W d1 d2 (A1 .point) u))
      (wedge_word_decode_encode A1 A2 W d1 d2 x p)

{` lem:wedgeofgpoidisgpoid, last sentence: β : C_1 → (a_12 = a_12),
   β(p_0, n, p_1, ..., p_n) = i_1^g p_0 i_2^g p_1 ..., is an equivalence. `}
def wedge_words_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : Equiv (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W))
  ≔ quasi_inverse_equiv (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W))
      (wedge_words_compose A1 A2 W) (wedge_words_decompose A1 A2 W d1 d2)
      (wedge_words_roundtrip A1 A2 W d1 d2) (wedge_words_compose_decompose A1 A2 W d1 d2)

def wedge_words_book_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : BookIsEquiv (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W)) (wedge_words_compose A1 A2 W)
  ≔ book_equivalence (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W)) (wedge_words_equiv A1 A2 W d1 d2) .equiv

{` Consequences. `}
def wsum_transfer_decidable_equality (A B : Type) (e : Equiv A B) (d : DecidableEquality A) (x y : B)
  : Decidable (Id B x y)
  ≔ let inv ≔ equiv_inverse_map A B e in
    match d (inv x) (inv y) [
  | inl. p ↦ inl. (concat B x (e .map (inv x)) y (inverse B (e .map (inv x)) x (equiv_counit A B e x))
      (concat B (e .map (inv x)) (e .map (inv y)) y (refl (e .map) p) (equiv_counit A B e y)))
  | inr. n ↦ inr. (q ↦ n (refl inv q)) ]

def wedge_loops_decidable_equality (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : DecidableEquality (Loop (wedge_pointed A1 A2 W))
  ≔ wsum_transfer_decidable_equality (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W))
      (wedge_words_equiv A1 A2 W d1 d2)
      (wsum_string_decidable_equality (Loop A1) (Loop A2) (refl (A1 .point)) (refl (A2 .point)) d1 d2)

def wedge_loops_set (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : isSet (Loop (wedge_pointed A1 A2 W))
  ≔ decidable_set_is_set (Loop (wedge_pointed A1 A2 W))
      (hedberg (Loop (wedge_pointed A1 A2 W)) (wedge_loops_decidable_equality A1 A2 W d1 d2))

def wsum_groupoid_from_based_loops (X : Type) (x0 : X) (m : (x : X) → Mere (Id X x0 x))
  (h : isSet (Id X x0 x0)) : isGroupoid X
  ≔ x y ↦ mere_rec (Id X x0 x) (isSet (Id X x y)) (isset_isprop (Id X x y))
      (p ↦ J X x0 (x p ↦ isSet (Id X x y))
        (mere_rec (Id X x0 y) (isSet (Id X x0 y)) (isset_isprop (Id X x0 y))
          (q ↦ J X x0 (y q ↦ isSet (Id X x0 y)) h y q) (m y))
        x p)
      (m x)

{` The wedge of pointed connected types with decidable loop types is a
   groupoid (all its identity types are sets). `}
def wedge_decidable_groupoid (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier)) : isGroupoid (W .carrier)
  ≔ wsum_groupoid_from_based_loops (W .carrier) (wedge_point A1 A2 W) (wedge_merely_based A1 A2 W h1 h2)
      (wedge_loops_set A1 A2 W d1 d2)
