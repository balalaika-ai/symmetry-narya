export "851-sums-of-groups-claims"

{` Chapter 8 (congp.tex), margin note at line 567 and the proof of
   lem:wedgeofgpoidisgpoid: the family C of strings is equivalent to the
   family P(x) ≔ (a_12 = x) FIBERWISE, for every x of the wedge, and C is a
   family of sets; plus the margin remarks at lines 513 and 568 (no relation
   between the symmetries, the order of the letters matters).

   Hypotheses as in the lemma: (A_1, a_1), (A_2, a_2) pointed connected types
   whose loop types have decidable equality (the classifying types of
   decidable groups; the groupoid hypotheses are not needed).

   α_x = wedge_word_encode x, β_x = wedge_word_decode x (module 847), with
   β_x α_x = id (wedge_word_decode_encode). At the base point β is the word
   composition through the chart C(a_12) → C_1(a_1) of the transported
   package; the chart is an equivalence (wwf_charts: transport of the
   identity charts along the computation path of wedge_rec), so β_{a12} is an
   equivalence and α_{a12} is its inverse. Being an equivalence is a
   proposition and the wedge is connected, so α_x is an equivalence for every
   x (path induction from a_12), hence also α_x β_x = id. `}

{` The chart C(i_1 a) → C_1(a) of a package is an equivalence. `}
def WwfCharts (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (D : WedgeCocone A1 A2 Type)
  (K : WedgeWordPackage A1 A2 W D) : Type
  ≔ (a : A1 .carrier) → isEquiv (D .fst a) (wedge_code1 A1 A2 a) (K .chart1 a)

def wwf_charts_transport (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (D : WedgeCocone A1 A2 Type)
  (K : WedgeWordPackage A1 A2 W D) (h : WwfCharts A1 A2 W D K) (D' : WedgeCocone A1 A2 Type)
  (p : Id (WedgeCocone A1 A2 Type) D D')
  : WwfCharts A1 A2 W D' (transport (WedgeCocone A1 A2 Type) (WedgeWordPackage A1 A2 W) D D' p K)
  ≔ let Co ≔ WedgeCocone A1 A2 Type in let Pk ≔ WedgeWordPackage A1 A2 W in
    J Co D (E q ↦ WwfCharts A1 A2 W E (transport Co Pk D E q K))
      (transport (Pk D) (WwfCharts A1 A2 W D) K (transport Co Pk D D (refl D) K)
        (inverse (Pk D) (transport Co Pk D D (refl D) K) K (transport_refl Co Pk D K)) h)
      D' p

def wwf_charts (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : WwfCharts A1 A2 W (wedge_cocone A1 A2 W Type (wedge_word_code A1 A2 W d1 d2)) (wedge_word_package A1 A2 W d1 d2)
  ≔ let Co ≔ WedgeCocone A1 A2 Type in let Pk ≔ WedgeWordPackage A1 A2 W in
    let D ≔ wedge_cocone A1 A2 W Type (wedge_word_code A1 A2 W d1 d2) in
    let D0 ≔ wedge_code_cocone A1 A2 d1 d2 in
    let q ≔ wedge_rec_beta A1 A2 W Type D0 in
    let std ≔ wedge_word_package_std A1 A2 W d1 d2 in
    transport (Pk D) (WwfCharts A1 A2 W D) (transport Co Pk D0 D (inverse Co D D0 q) std)
      (wedge_word_package A1 A2 W d1 d2) (wedge_transport_inverse Co Pk D D0 q std)
      (wwf_charts_transport A1 A2 W D0 std (a ↦ identity_equiv (wedge_code1 A1 A2 a) .equiv) D (inverse Co D D0 q))

{` β at the base point is an equivalence, and α at the base point. `}
def wwf_beta_base (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : Equiv (wedge_word_code A1 A2 W d1 d2 (wedge_point A1 A2 W)) (Loop (wedge_pointed A1 A2 W))
  ≔ compose_equiv (wedge_word_code A1 A2 W d1 d2 (wedge_point A1 A2 W)) (WedgeWords A1 A2) (Loop (wedge_pointed A1 A2 W))
      (wedge_word_package A1 A2 W d1 d2 .chart1 (A1 .point), wwf_charts A1 A2 W d1 d2 (A1 .point))
      (wedge_words_equiv A1 A2 W d1 d2)

def wwf_alpha_base (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : Equiv (Loop (wedge_pointed A1 A2 W)) (wedge_word_code A1 A2 W d1 d2 (wedge_point A1 A2 W))
  ≔ let a12 ≔ wedge_point A1 A2 W in
    let Q ≔ wedge_word_code A1 A2 W d1 d2 in
    let L ≔ Loop (wedge_pointed A1 A2 W) in
    let E ≔ wwf_beta_base A1 A2 W d1 d2 in
    let inv ≔ equiv_inverse_map (Q a12) L E in
    let enc ≔ wedge_word_encode A1 A2 W d1 d2 a12 in
    let dec ≔ wedge_word_decode A1 A2 W d1 d2 a12 in
    equiv_change_map L (Q a12) (canonical_inverse_equiv (Q a12) L E) enc
      (p ↦ concat (Q a12) (inv p) (inv (dec (enc p))) (enc p)
        (refl inv (inverse L (dec (enc p)) p (wedge_word_decode_encode A1 A2 W d1 d2 a12 p)))
        (concat (Q a12) (inv (dec (enc p))) (inv (E .map (enc p))) (enc p)
          (refl inv (wedge_word_decode_incl1 A1 A2 W d1 d2 (A1 .point) (enc p)))
          (inverse (Q a12) (enc p) (inv (E .map (enc p))) (equiv_unit (Q a12) L E (enc p)))))

{` Margin note at line 567: P(x) ≃ C(x) for every x, by α (inverse β). `}
def wedge_word_encode_is_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier)) (x : W .carrier)
  : isEquiv (wedge_based_paths A1 A2 W x) (wedge_word_code A1 A2 W d1 d2 x) (wedge_word_encode A1 A2 W d1 d2 x)
  ≔ let X ≔ W .carrier in let a12 ≔ wedge_point A1 A2 W in
    let Pf ≔ (y ↦ isEquiv (wedge_based_paths A1 A2 W y) (wedge_word_code A1 A2 W d1 d2 y) (wedge_word_encode A1 A2 W d1 d2 y))
      : X → Type in
    mere_rec (Id X a12 x) (Pf x)
      (isequiv_isprop (wedge_based_paths A1 A2 W x) (wedge_word_code A1 A2 W d1 d2 x) (wedge_word_encode A1 A2 W d1 d2 x))
      (p ↦ J X a12 (y _ ↦ Pf y) (wwf_alpha_base A1 A2 W d1 d2 .equiv) x p)
      (wedge_merely_based A1 A2 W h1 h2 x)

def wedge_word_paths_code_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier)) (x : W .carrier)
  : Equiv (wedge_based_paths A1 A2 W x) (wedge_word_code A1 A2 W d1 d2 x)
  ≔ (wedge_word_encode A1 A2 W d1 d2 x, wedge_word_encode_is_equiv A1 A2 W d1 d2 h1 h2 x)

{` αβ = id for every x (the book's "αβ(p_0, n, p_1, ..., p_n) = (p_0, ...)"). `}
def wedge_word_encode_decode (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier)) (x : W .carrier)
  (c : wedge_word_code A1 A2 W d1 d2 x)
  : Id (wedge_word_code A1 A2 W d1 d2 x) (wedge_word_encode A1 A2 W d1 d2 x (wedge_word_decode A1 A2 W d1 d2 x c)) c
  ≔ let Q ≔ wedge_word_code A1 A2 W d1 d2 x in
    let P ≔ wedge_based_paths A1 A2 W x in
    let E ≔ wedge_word_paths_code_equiv A1 A2 W d1 d2 h1 h2 x in
    let enc ≔ wedge_word_encode A1 A2 W d1 d2 x in
    let dec ≔ wedge_word_decode A1 A2 W d1 d2 x in
    let s ≔ equiv_inverse_map P Q E c in
    concat Q (enc (dec c)) (enc (dec (enc s))) c
      (refl ((y ↦ enc (dec y)) : Q → Q) (inverse Q (enc s) c (equiv_counit P Q E c)))
      (concat Q (enc (dec (enc s))) (enc s) c
        (refl enc (wedge_word_decode_encode A1 A2 W d1 d2 x s)) (equiv_counit P Q E c))

{` C is a family of sets (and P is, the wedge being a groupoid). `}
def wedge_word_code_set (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (h1 : Connected (A1 .carrier)) (h2 : Connected (A2 .carrier)) (x : W .carrier)
  : isSet (wedge_word_code A1 A2 W d1 d2 x)
  ≔ hlevel_two_to_set (wedge_word_code A1 A2 W d1 d2 x)
      (hlevel_equiv (suc. (suc. zero.)) (wedge_based_paths A1 A2 W x) (wedge_word_code A1 A2 W d1 d2 x)
        (wedge_word_paths_code_equiv A1 A2 W d1 d2 h1 h2 x)
        (set_to_hlevel_two (wedge_based_paths A1 A2 W x)
          (wedge_decidable_groupoid A1 A2 W d1 d2 h1 h2 (wedge_point A1 A2 W) x)))

{` Margin note at line 568: different strings give different symmetries
   (in particular a shuffle of the letters that is again a string, but a
   different one, gives a different symmetry). `}
def wedge_words_distinct (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) (c c' : WedgeWords A1 A2)
  (n : Not (Id (WedgeWords A1 A2) c c'))
  : Not (Id (Loop (wedge_pointed A1 A2 W)) (wedge_words_compose A1 A2 W c) (wedge_words_compose A1 A2 W c'))
  ≔ e ↦ n (concat (WedgeWords A1 A2) c (wedge_words_decompose A1 A2 W d1 d2 (wedge_words_compose A1 A2 W c)) c'
      (inverse (WedgeWords A1 A2) (wedge_words_decompose A1 A2 W d1 d2 (wedge_words_compose A1 A2 W c)) c
        (wedge_words_roundtrip A1 A2 W d1 d2 c))
      (concat (WedgeWords A1 A2) (wedge_words_decompose A1 A2 W d1 d2 (wedge_words_compose A1 A2 W c))
        (wedge_words_decompose A1 A2 W d1 d2 (wedge_words_compose A1 A2 W c')) c'
        (refl (wedge_words_decompose A1 A2 W d1 d2) e) (wedge_words_roundtrip A1 A2 W d1 d2 c')))

{` Margin remark at line 513: the symmetries of Z ∨ Z satisfy no relation:
   the words in the two generators (alternating, nontrivial letters) give
   pairwise different symmetries, and every symmetry is such a word. `}
def circle_sum_words_equiv (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Equiv (WedgeWords (circle_pointed C) (circle_pointed C)) (USym (circle_decidable_sum_group C W))
  ≔ decidable_sum_words_equiv (circle_group C) (circle_group C) W (circle_group_decidable C) (circle_group_decidable C)

def circle_sum_no_relations (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (c c' : WedgeWords (circle_pointed C) (circle_pointed C))
  (e : Id (USym (circle_decidable_sum_group C W))
         (wedge_words_compose (circle_pointed C) (circle_pointed C) W c)
         (wedge_words_compose (circle_pointed C) (circle_pointed C) W c'))
  : Id (WedgeWords (circle_pointed C) (circle_pointed C)) c c'
  ≔ let D ≔ wedge_words_decompose (circle_pointed C) (circle_pointed C) W (circle_group_decidable C) (circle_group_decidable C) in
    let R ≔ wedge_words_roundtrip (circle_pointed C) (circle_pointed C) W (circle_group_decidable C) (circle_group_decidable C) in
    let WW ≔ WedgeWords (circle_pointed C) (circle_pointed C) in
    concat WW c (D (wedge_words_compose (circle_pointed C) (circle_pointed C) W c)) c'
      (inverse WW (D (wedge_words_compose (circle_pointed C) (circle_pointed C) W c)) c (R c))
      (concat WW (D (wedge_words_compose (circle_pointed C) (circle_pointed C) W c))
        (D (wedge_words_compose (circle_pointed C) (circle_pointed C) W c')) c' (refl D e) (R c'))
