export "847-wedge-encode-decode"
export "843-sums-of-groups"

{` Chapter 8 (congp.tex), lem:wedgeofgpoidisgpoid (congp.tex:627) for groups.

   The book does not define "decidable group"; IsDecidableGroup G is
   decidable equality of the symmetries USym G.  For decidable groups G_1,
   G_2 and a wedge signature W of BG_1, BG_2, the groupoid hypothesis of
   sum_of_groups (module 843) is discharged by wedge_decidable_groupoid:
   decidable_sum_of_groups G1 G2 W d1 d2 is G_1 ∨ G_2 ≔ Aut_{BG_1∨BG_2}(a_12),
   it is a decidable group (decidable_sum_of_groups_decidable), and the
   book's β : C_1(a_1) → USym(G_1 ∨ G_2) is an equivalence
   (decidable_sum_words_equiv, decidable_sum_words_book_equiv).

   Litmus: Z = circle_group C is decidable (USym Z ≃ Int); hence Z ∨ Z is a
   decidable group for every wedge signature of two circles, its generators
   i_1^g(loop), i_2^g(loop) do not commute (from the word description:
   wedge_loops_noncommuting), and β evaluated on the word (loop, 2, loop, loop)
   is the product i_1^g(loop) · i_2^g(loop) · i_1^g(loop). `}

def IsDecidableGroup (G : Group) : Type ≔ DecidableEquality (USym G)

def decidable_sum_groupoid (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2) : isGroupoid (W .carrier)
  ≔ wedge_decidable_groupoid (BG G1) (BG G2) W d1 d2 (bg_connected G1) (bg_connected G2)

{` G_1 ∨ G_2 for decidable groups (def:sumofgroup with hW discharged). `}
def decidable_sum_of_groups (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2) : Group
  ≔ sum_of_groups G1 G2 W (decidable_sum_groupoid G1 G2 W d1 d2)

def decidable_sum_of_groups_decidable (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2)
  : IsDecidableGroup (decidable_sum_of_groups G1 G2 W d1 d2)
  ≔ wedge_loops_decidable_equality (BG G1) (BG G2) W d1 d2

def decidable_sum_words_equiv (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2)
  : Equiv (WedgeWords (BG G1) (BG G2)) (USym (decidable_sum_of_groups G1 G2 W d1 d2))
  ≔ wedge_words_equiv (BG G1) (BG G2) W d1 d2

def decidable_sum_words_book_equiv (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2)
  : BookIsEquiv (WedgeWords (BG G1) (BG G2)) (USym (decidable_sum_of_groups G1 G2 W d1 d2))
      (wedge_words_compose (BG G1) (BG G2) W)
  ≔ wedge_words_book_equiv (BG G1) (BG G2) W d1 d2

{` The letters of β are the images of the structure homomorphisms. `}
def decidable_sum_words_letters (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2))
  (d1 : IsDecidableGroup G1) (d2 : IsDecidableGroup G2) (g : USym G1) (h : USym G2)
  : Product
      (Id (USym (decidable_sum_of_groups G1 G2 W d1 d2))
        (usym_hom G1 (decidable_sum_of_groups G1 G2 W d1 d2)
          (sum_of_groups_incl1 G1 G2 W (decidable_sum_groupoid G1 G2 W d1 d2)) g)
        (wedge_loop1 (BG G1) (BG G2) W g))
      (Id (USym (decidable_sum_of_groups G1 G2 W d1 d2))
        (usym_hom G2 (decidable_sum_of_groups G1 G2 W d1 d2)
          (sum_of_groups_incl2 G1 G2 W (decidable_sum_groupoid G1 G2 W d1 d2)) h)
        (wedge_loop2 (BG G1) (BG G2) W h))
  ≔ (sum_of_groups_incl1_usym G1 G2 W (decidable_sum_groupoid G1 G2 W d1 d2) g,
     sum_of_groups_incl2_usym G1 G2 W (decidable_sum_groupoid G1 G2 W d1 d2) h)

{` Words of length 2: i_1^g(l_1) and i_2^g(l_2) do not commute when both
   are nontrivial (the words (l_1, 1, l_2) and (refl, 2, l_2, l_1) differ). `}
def wedge_loops_noncommuting (A1 A2 : Pointed) (W : WedgeSignature A1 A2)
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  (l1 : WedgeLetter1 A1) (l2 : WedgeLetter1 A2)
  (h : Id (Loop (wedge_pointed A1 A2 W))
    (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (wedge_point A1 A2 W)
      (wedge_letter2 A1 A2 W l2) (wedge_letter1 A1 A2 W l1))
    (concat (W .carrier) (wedge_point A1 A2 W) (wedge_point A1 A2 W) (wedge_point A1 A2 W)
      (wedge_letter1 A1 A2 W l1) (wedge_letter2 A1 A2 W l2)))
  : Empty
  ≔ let X ≔ W .carrier in let x ≔ wedge_point A1 A2 W in
    let a ≔ wedge_letter1 A1 A2 W l1 in let b ≔ wedge_letter2 A1 A2 W l2 in
    let L ≔ Loop (wedge_pointed A1 A2 W) in
    let wab : WedgeWords A1 A2 ≔ (l1 .fst, cons. l2 nil.) in
    let wba : WedgeWords A1 A2 ≔ (refl (A1 .point), cons. l2 (cons. l1 nil.)) in
    let eab : Id L (wedge_words_compose A1 A2 W wab) (concat X x x x b a)
      ≔ refl ((z ↦ concat X x x x z a) : L → L) (concat_1p X x x b) in
    let eba : Id L (wedge_words_compose A1 A2 W wba) (concat X x x x a b)
      ≔ concat L (wedge_words_compose A1 A2 W wba) (concat X x x x (concat X x x x (refl x) a) b) (concat X x x x a b)
          (concat_p1 X x x (concat X x x x (concat X x x x (refl x) a) b))
          (refl ((z ↦ concat X x x x z b) : L → L) (concat_1p X x x a)) in
    let p : Id (WedgeWords A1 A2) wab wba
      ≔ equivalence_injective (WedgeWords A1 A2) L (wedge_words_equiv A1 A2 W d1 d2) wab wba
          (concat L (wedge_words_compose A1 A2 W wab) (concat X x x x b a) (wedge_words_compose A1 A2 W wba)
            eab (concat L (concat X x x x b a) (concat X x x x a b) (wedge_words_compose A1 A2 W wba) h
              (inverse L (wedge_words_compose A1 A2 W wba) (concat X x x x a b) eba))) in
    l1 .snd (p .fst)

{` Litmus: the circle group is decidable, Z ∨ Z is a decidable group. `}
def wsum_int_one_code : Int → Type ≔ [
  | pos. zero. ↦ Empty
  | pos. (suc. _) ↦ Unit
  | neg. _ ↦ Empty ]

def wedge_circle_loop_nontrivial (C : CircleSignature)
  (p : Id (Loop (circle_pointed C)) (C .loop) (refl (C .base))) : Empty
  ≔ transport Int wsum_int_one_code (pos. (suc. zero.)) int_zero
      (concat Int (pos. (suc. zero.)) (circle_winding C (C .loop)) int_zero
        (inverse Int (circle_winding C (C .loop)) (pos. (suc. zero.)) (circle_winding_loop C))
        (concat Int (circle_winding C (C .loop)) (circle_winding C (refl (C .base))) int_zero
          (refl (circle_winding C) p) (circle_winding_refl C)))
      star.

def circle_loop_letter (C : CircleSignature) : WedgeLetter1 (circle_pointed C)
  ≔ (C .loop, wedge_circle_loop_nontrivial C)

def circle_group_decidable (C : CircleSignature) : IsDecidableGroup (circle_group C)
  ≔ wsum_transfer_decidable_equality Int (USym (circle_group C))
      (native_equivalence Int (USym (circle_group C)) (circle_group_usym_integers C)) int_dec_eq

def circle_decidable_sum_group (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C)) : Group
  ≔ decidable_sum_of_groups (circle_group C) (circle_group C) W (circle_group_decidable C) (circle_group_decidable C)

def circle_decidable_sum_group_decidable (C : CircleSignature)
  (W : WedgeSignature (circle_pointed C) (circle_pointed C)) : IsDecidableGroup (circle_decidable_sum_group C W)
  ≔ decidable_sum_of_groups_decidable (circle_group C) (circle_group C) W (circle_group_decidable C)
      (circle_group_decidable C)

def circle_decidable_sum_not_abelian (C : CircleSignature)
  (W : WedgeSignature (circle_pointed C) (circle_pointed C)) (h : IsAbelian (circle_decidable_sum_group C W)) : Empty
  ≔ wedge_loops_noncommuting (circle_pointed C) (circle_pointed C) W (circle_group_decidable C)
      (circle_group_decidable C) (circle_loop_letter C) (circle_loop_letter C)
      (h (wedge_loop1 (circle_pointed C) (circle_pointed C) W (C .loop))
         (wedge_loop2 (circle_pointed C) (circle_pointed C) W (C .loop)))

{` β on the word (loop, 2, loop, loop) is i_1^g(loop) · i_2^g(loop) · i_1^g(loop). `}
def circle_sum_word_example (C : CircleSignature) : WedgeWords (circle_pointed C) (circle_pointed C)
  ≔ (C .loop, cons. (circle_loop_letter C) (cons. (circle_loop_letter C) nil.))

def circle_sum_word_example_compose (C : CircleSignature)
  (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Id (USym (circle_decidable_sum_group C W))
      (wedge_words_compose (circle_pointed C) (circle_pointed C) W (circle_sum_word_example C))
      (usym_mul (circle_decidable_sum_group C W) (wedge_loop1 (circle_pointed C) (circle_pointed C) W (C .loop))
        (usym_mul (circle_decidable_sum_group C W) (wedge_loop2 (circle_pointed C) (circle_pointed C) W (C .loop))
          (wedge_loop1 (circle_pointed C) (circle_pointed C) W (C .loop))))
  ≔ let X ≔ W .carrier in let x ≔ wedge_point (circle_pointed C) (circle_pointed C) W in
    let a ≔ wedge_loop1 (circle_pointed C) (circle_pointed C) W (C .loop) in
    let b ≔ wedge_loop2 (circle_pointed C) (circle_pointed C) W (C .loop) in
    refl ((z ↦ concat X x x x (concat X x x x z b) a) : Id X x x → Id X x x) (concat_1p X x x a)

def circle_sum_word_example_decompose (C : CircleSignature)
  (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Id (WedgeWords (circle_pointed C) (circle_pointed C))
      (wedge_words_decompose (circle_pointed C) (circle_pointed C) W (circle_group_decidable C) (circle_group_decidable C)
        (wedge_words_compose (circle_pointed C) (circle_pointed C) W (circle_sum_word_example C)))
      (circle_sum_word_example C)
  ≔ wedge_words_roundtrip (circle_pointed C) (circle_pointed C) W (circle_group_decidable C) (circle_group_decidable C)
      (circle_sum_word_example C)

def circle_sum_word_example_length (C : CircleSignature)
  : Id Nat (wsum_alt_length (WedgeLetter1 (circle_pointed C)) (WedgeLetter1 (circle_pointed C))
      (circle_sum_word_example C .snd)) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)
