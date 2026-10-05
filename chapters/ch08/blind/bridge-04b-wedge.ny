export "bridge-04a-wedge"
export "../../../src/848-decidable-sums-of-groups"
export "../../../src/850-wedge-fold-abelian"

{` Bridges for congp.tex, xca:whatAREabeliangroups and
   lem:wedgeofgpoidisgpoid.

   lem:wedgeofgpoidisgpoid: the blind strings (p0, n, p1, ..., pn) with the
   tail as a length-indexed nested Σ correspond to our alternating lists
   WsumAlt (bw_tail_to / bw_tail_from, inverse), and the blind β (book
   products u · v = concat v u) has literally the same nesting as our
   wedge_words_compose, so β_blind = β_ours ∘ (that bijection).

   xca:whatAREabeliangroups: the blind fold and i are arbitrary pointed maps
   with the prescribed restrictions; i^* is injective (lem:univvee), so they
   equal our wedge_fold_book / wedge_incl_book, and the extension types are
   identified. The aside follows from our unpointed_extension_abelian plus
   Ω fold ∘ i1^g = id, Ω fold ∘ i2^g = id. `}

{` Tails: length-indexed nested Σ versus alternating lists. `}
def bw_tail_to (G1 G2 : Group) (n : Nat)
  : BlindAltTail G1 G2 n → WsumAlt (BlindNonRefl G2) (BlindNonRefl G1)
  ≔ match n [
    | zero. ↦ _ ↦ nil.
    | suc. m ↦ t ↦ cons. (t .fst) (bw_tail_to G2 G1 m (t .snd)) ]

def bw_tail_from (G1 G2 : Group) (w : WsumAlt (BlindNonRefl G2) (BlindNonRefl G1))
  : Σ Nat (n ↦ BlindAltTail G1 G2 n)
  ≔ match w [
    | nil. ↦ (zero., star.)
    | cons. x w' ↦ (suc. (bw_tail_from G2 G1 w' .fst), (x, bw_tail_from G2 G1 w' .snd)) ]

def bw_tail_to_from (G1 G2 : Group) (w : WsumAlt (BlindNonRefl G2) (BlindNonRefl G1))
  : Id (WsumAlt (BlindNonRefl G2) (BlindNonRefl G1))
      (bw_tail_to G1 G2 (bw_tail_from G1 G2 w .fst) (bw_tail_from G1 G2 w .snd)) w
  ≔ match w [
    | nil. ↦ refl (nil. : WsumAlt (BlindNonRefl G2) (BlindNonRefl G1))
    | cons. x w' ↦ refl ((u ↦ cons. x u) : WsumAlt (BlindNonRefl G1) (BlindNonRefl G2) → WsumAlt (BlindNonRefl G2) (BlindNonRefl G1))
        (bw_tail_to_from G2 G1 w') ]

def bw_tail_from_to (G1 G2 : Group) (n : Nat)
  : (t : BlindAltTail G1 G2 n)
    → Id (Σ Nat (k ↦ BlindAltTail G1 G2 k)) (bw_tail_from G1 G2 (bw_tail_to G1 G2 n t)) (n, t)
  ≔ match n [
    | zero. ↦ t ↦ match t [ star. ↦ refl ((zero., star.) : Σ Nat (k ↦ BlindAltTail G1 G2 k)) ]
    | suc. m ↦ t ↦
        refl ((u ↦ (suc. (u .fst), (t .fst, u .snd))) : Σ Nat (k ↦ BlindAltTail G2 G1 k) → Σ Nat (k ↦ BlindAltTail G1 G2 k))
          (bw_tail_from_to G2 G1 m (t .snd)) ]

def bw_strings_equiv (G1 G2 : Group) : Equiv (WedgeWords (BG G1) (BG G2)) (BlindAltStrings G1 G2)
  ≔ quasi_inverse_equiv (WedgeWords (BG G1) (BG G2)) (BlindAltStrings G1 G2)
      (c ↦ (c .fst, bw_tail_from G1 G2 (c .snd)))
      (c ↦ (c .fst, bw_tail_to G1 G2 (c .snd .fst) (c .snd .snd)))
      (c ↦ (refl (c .fst), bw_tail_to_from G1 G2 (c .snd)))
      (c ↦ (refl (c .fst), bw_tail_from_to G1 G2 (c .snd .fst) (c .snd .snd)))

{` The blind evaluation of tails is our wsum_alt_loop. `}
def bw_alt_eval_eq (G1 G2 : Group) (Z : Type) (z : Z) (j1 : USym G1 → Id Z z z) (j2 : USym G2 → Id Z z z) (n : Nat)
  : (t : BlindAltTail G1 G2 n)
    → Id (Id Z z z) (blind_alt_eval G1 G2 (Id Z z z) (blind_loop_mul Z z) (refl z) j1 j2 n t)
        (wsum_alt_loop (BlindNonRefl G2) (BlindNonRefl G1) Z z (q ↦ j2 (q .fst)) (p ↦ j1 (p .fst)) (bw_tail_to G1 G2 n t))
  ≔ match n [
    | zero. ↦ _ ↦ refl (refl z)
    | suc. m ↦ t ↦
        refl ((u ↦ concat Z z z z u (j2 (t .fst .fst))) : Id Z z z → Id Z z z)
          (bw_alt_eval_eq G2 G1 Z z j2 j1 m (t .snd)) ]

def bw_beta_compat (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (c : WedgeWords (BG G1) (BG G2))
  : Id (Loop (blind_wedge_pointed (BG G1) (BG G2) W))
      (blind_wedge_beta G1 G2 W (bw_strings_equiv G1 G2 .map c))
      (wedge_words_compose (BG G1) (BG G2) (bridge_wedge_signature (BG G1) (BG G2) W) c)
  ≔ let W' ≔ bridge_wedge_signature (BG G1) (BG G2) W in
    let X ≔ W .fst in let a12 ≔ W .snd .i1 (shape G1) in
    let F ≔ bw_tail_from G1 G2 (c .snd) in
    concat (Id X a12 a12)
      (blind_wedge_beta G1 G2 W (c .fst, F))
      (concat X a12 a12 a12 (wsum_alt_loop (BlindNonRefl G2) (BlindNonRefl G1) X a12
          (q ↦ wedge_loop2 (BG G1) (BG G2) W' (q .fst)) (p ↦ wedge_loop1 (BG G1) (BG G2) W' (p .fst))
          (bw_tail_to G1 G2 (F .fst) (F .snd)))
        (wedge_loop1 (BG G1) (BG G2) W' (c .fst)))
      (wedge_words_compose (BG G1) (BG G2) W' c)
      (refl ((u ↦ concat X a12 a12 a12 u (wedge_loop1 (BG G1) (BG G2) W' (c .fst))) : Id X a12 a12 → Id X a12 a12)
        (bw_alt_eval_eq G1 G2 X a12 (wedge_loop1 (BG G1) (BG G2) W') (wedge_loop2 (BG G1) (BG G2) W') (F .fst) (F .snd)))
      (refl ((u ↦ concat X a12 a12 a12
                 (wedge_tail1_loop (BG G1) (BG G2) W' u) (wedge_loop1 (BG G1) (BG G2) W' (c .fst)))
              : WsumAlt (BlindNonRefl G2) (BlindNonRefl G1) → Id X a12 a12)
        (bw_tail_to_from G1 G2 (c .snd)))

{` lem:wedgeofgpoidisgpoid. `}
def bridge_lem_wedgeofgpoidisgpoid : blind_lem_wedgeofgpoidisgpoid
  ≔ G1 G2 d1 d2 W ↦
    let W' ≔ bridge_wedge_signature (BG G1) (BG G2) W in
    ((wedge_connected (BG G1) (BG G2) W' (bg_connected G1) (bg_connected G2),
      (wedge_decidable_groupoid (BG G1) (BG G2) W' d1 d2 (bg_connected G1) (bg_connected G2),
       wedge_loops_decidable_equality (BG G1) (BG G2) W' d1 d2)),
     b8_two_of_three (WedgeWords (BG G1) (BG G2)) (BlindAltStrings G1 G2) (Loop (blind_wedge_pointed (BG G1) (BG G2) W))
       (bw_strings_equiv G1 G2) (wedge_words_equiv (BG G1) (BG G2) W' d1 d2)
       (blind_wedge_beta G1 G2 W) (bw_beta_compat G1 G2 W))

{` xca:whatAREabeliangroups. i^* is injective. `}
def bw_restrict_injective (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f f' : BookPointedMap (wedge_pointed A1 A2 W) B)
  (e : Id (Product (BookPointedMap A1 B) (BookPointedMap A2 B)) (wedge_restrict A1 A2 W B f) (wedge_restrict A1 A2 W B f'))
  : Id (BookPointedMap (wedge_pointed A1 A2 W) B) f f'
  ≔ equivalence_injective (BookPointedMap (wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
      (wedge_pointed_universal_property A1 A2 W B) f f' e

def bw_fold_eq (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
  : Id (BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG G))
      (D .fst) (wedge_fold_book G (bridge_wedge_signature (BG G) (BG G) W))
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let P ≔ Product (BookPointedMap (BG G) (BG G)) (BookPointedMap (BG G) (BG G)) in
    let ip ≔ hom_B G G (group_hom_id G) in
    bw_restrict_injective (BG G) (BG G) W' (BG G) (D .fst) (wedge_fold_book G W')
      (concat P (wedge_restrict (BG G) (BG G) W' (BG G) (D .fst)) (ip, ip)
        (wedge_restrict (BG G) (BG G) W' (BG G) (wedge_fold_book G W'))
        (D .snd .fst)
        (inverse P (wedge_restrict (BG G) (BG G) W' (BG G) (wedge_fold_book G W')) (ip, ip)
          (wedge_restrict_extend (BG G) (BG G) W' (BG G) ip ip)))

def bw_incl_eq (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
  : Id (BookPointedMap (blind_wedge_pointed (BG G) (BG G) W) (BG (product_group G G)))
      (D .snd .snd .fst) (wedge_incl_book G (bridge_wedge_signature (BG G) (BG G) W))
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let GG ≔ product_group G G in
    let P ≔ Product (BookPointedMap (BG G) (BG GG)) (BookPointedMap (BG G) (BG GG)) in
    let j1 ≔ hom_B G GG (product_group_incl1 G G) in
    let j2 ≔ hom_B G GG (product_group_incl2 G G) in
    bw_restrict_injective (BG G) (BG G) W' (BG GG) (D .snd .snd .fst) (wedge_incl_book G W')
      (concat P (wedge_restrict (BG G) (BG G) W' (BG GG) (D .snd .snd .fst)) (j1, j2)
        (wedge_restrict (BG G) (BG G) W' (BG GG) (wedge_incl_book G W'))
        (D .snd .snd .snd)
        (inverse P (wedge_restrict (BG G) (BG G) W' (BG GG) (wedge_incl_book G W')) (j1, j2)
          (wedge_restrict_extend (BG G) (BG G) W' (BG GG) j1 j2)))

def bw_fold_extension_equiv (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
  : Equiv (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)) (IsAbelian G)
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let V ≔ wedge_pointed (BG G) (BG G) W' in
    compose_equiv (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)) (WedgeFoldExtension G W') (IsAbelian G)
      (id_to_equiv (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)) (WedgeFoldExtension G W')
        (refl (WsumPointedExtension V (BG (product_group G G)) (BG G)) (bw_incl_eq G W D) (bw_fold_eq G W D)))
      (wedge_fold_extension_abelian_equiv G W')

def bridge_xca_whatAREabeliangroups : blind_xca_whatAREabeliangroups
  ≔ G W D ↦
    let E ≔ BlindFoldExtension G W (D .fst) (D .snd .snd .fst) in
    let e ≔ bw_fold_extension_equiv G W D in
    (hab ↦ mere E (equiv_inverse_map E (IsAbelian G) e hab),
     m ↦ mere_rec E (IsAbelian G) (is_abelian_prop G) (e .map) m)

{` Converse (bonus): our statement for the blind data (the extension type itself is equivalent to isAb). `}
def bridge_xca_whatAREabeliangroups_untruncated (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
  : Equiv (BlindFoldExtension G W (D .fst) (D .snd .snd .fst)) (IsAbelian G)
  ≔ bw_fold_extension_equiv G W D
