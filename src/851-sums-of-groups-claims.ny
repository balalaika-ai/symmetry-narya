export "848-decidable-sums-of-groups"
export "844-circle-wedge-homomorphisms"

{` Chapter 8 (congp.tex), running text of section "Sums of groups"
   (congp.tex:500-626) and the unconditional cor:ZplusZuniv.

   - "a pair of symmetries is given by a function f : S¹+S¹ → A with the
     property that f sends each of the base points of the circles to a":
     circle_sum_symmetry_pairs (via wsum_based_sum_maps_equiv: such f are
     pairs of pointed maps).
   - "But S¹+S¹ is not connected, and so not a group" is circle_sum_not_connected
     of module 288 (chapter 3), not repeated here.
   - Margin note of lem:wedgeofgpoidisgpoid: the strings form families of
     sets "since A1 and A2 are groupoids" (wedge_code1_set, wedge_code2_set).
   - cor:ZplusZuniv without the groupoid hypothesis of module 844: the wedge
     of two circles is a groupoid by lem:wedgeofgpoidisgpoid, and
     circle_decidable_sum_group C W ≡ circle_sum_group C W hW for that hW
     (circle_decidable_sum_hom_equiv). `}

{` Maps from X + Y sending both base points to b are pairs of pointed maps. `}
def WsumBasedSumMaps (X Y B : Pointed) : Type
  ≔ Σ (Sum (X .carrier) (Y .carrier) → B .carrier) (f ↦
      Product (Id (B .carrier) (B .point) (f (inl. (X .point)))) (Id (B .carrier) (B .point) (f (inr. (Y .point)))))

def WsumBasedPairs (X Y B : Pointed) : Type
  ≔ Σ (Product (X .carrier → B .carrier) (Y .carrier → B .carrier)) (fg ↦
      Product (Id (B .carrier) (B .point) (fg .fst (X .point))) (Id (B .carrier) (B .point) (fg .snd (Y .point))))

def wsum_based_pairs_split (X Y B : Pointed) (u : WsumBasedPairs X Y B)
  : Product (BookPointedMap X B) (BookPointedMap Y B)
  ≔ ((u .fst .fst, u .snd .fst), (u .fst .snd, u .snd .snd))

def wsum_based_pairs_join (X Y B : Pointed) (v : Product (BookPointedMap X B) (BookPointedMap Y B))
  : WsumBasedPairs X Y B
  ≔ ((v .fst .fst, v .snd .fst), (v .fst .snd, v .snd .snd))

def wsum_based_sum_maps_equiv (X Y B : Pointed)
  : Equiv (WsumBasedSumMaps X Y B) (Product (BookPointedMap X B) (BookPointedMap Y B))
  ≔ compose_equiv (WsumBasedSumMaps X Y B) (WsumBasedPairs X Y B) (Product (BookPointedMap X B) (BookPointedMap Y B))
      (sigma_pullback_equiv (Sum (X .carrier) (Y .carrier) → B .carrier)
        (Product (X .carrier → B .carrier) (Y .carrier → B .carrier))
        (sum_universal_property (X .carrier) (Y .carrier) (B .carrier))
        (fg ↦ Product (Id (B .carrier) (B .point) (fg .fst (X .point))) (Id (B .carrier) (B .point) (fg .snd (Y .point)))))
      (quasi_inverse_equiv (WsumBasedPairs X Y B) (Product (BookPointedMap X B) (BookPointedMap Y B))
        (wsum_based_pairs_split X Y B) (wsum_based_pairs_join X Y B)
        (u ↦ refl u) (v ↦ refl v))

def circle_sum_symmetry_pairs (C : CircleSignature) (A : Type) (a : A)
  : Equiv (WsumBasedSumMaps (circle_pointed C) (circle_pointed C) (A, a)) (Product (Id A a a) (Id A a a))
  ≔ compose_equiv (WsumBasedSumMaps (circle_pointed C) (circle_pointed C) (A, a))
      (Product (BookPointedMap (circle_pointed C) (A, a)) (BookPointedMap (circle_pointed C) (A, a)))
      (Product (Id A a a) (Id A a a))
      (wsum_based_sum_maps_equiv (circle_pointed C) (circle_pointed C) (A, a))
      (product_equiv (BookPointedMap (circle_pointed C) (A, a)) (BookPointedMap (circle_pointed C) (A, a))
        (Id A a a) (Id A a a) (pointed_circle_universal_property C A a) (pointed_circle_universal_property C A a))

{` The strings C_i(x) form families of sets when A_1, A_2 are groupoids. `}
def wedge_word_tail1_set (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : isSet (wedge_word_tail1 A1 A2)
  ≔ decidable_set_is_set (wedge_word_tail1 A1 A2)
      (hedberg (wedge_word_tail1 A1 A2)
        (wsum_alt_decidable_equality (WedgeLetter1 A2) (WedgeLetter1 A1)
          (wsum_nontrivial_decidable_equality (Loop A2) (refl (A2 .point)) d2)
          (wsum_nontrivial_decidable_equality (Loop A1) (refl (A1 .point)) d1)))

def wedge_word_tail2_set (A1 A2 : Pointed) (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2))
  : isSet (wedge_word_tail2 A1 A2)
  ≔ wedge_word_tail1_set A2 A1 d2 d1

def wedge_code1_set (A1 A2 : Pointed) (h1 : isGroupoid (A1 .carrier))
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) (x : A1 .carrier)
  : isSet (wedge_code1 A1 A2 x)
  ≔ product_set (Id (A1 .carrier) (A1 .point) x) (wedge_word_tail1 A1 A2) (h1 (A1 .point) x)
      (wedge_word_tail1_set A1 A2 d1 d2)

def wedge_code2_set (A1 A2 : Pointed) (h2 : isGroupoid (A2 .carrier))
  (d1 : DecidableEquality (Loop A1)) (d2 : DecidableEquality (Loop A2)) (x : A2 .carrier)
  : isSet (wedge_code2 A1 A2 x)
  ≔ product_set (Id (A2 .carrier) (A2 .point) x) (wedge_word_tail2 A1 A2) (h2 (A2 .point) x)
      (wedge_word_tail2_set A1 A2 d1 d2)

{` cor:ZplusZuniv for every wedge of two circles (no groupoid hypothesis). `}
def circle_decidable_sum_hom_equiv (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (G : Group) : Equiv (GroupHom (circle_decidable_sum_group C W) G) (Product (USym G) (USym G))
  ≔ circle_sum_hom_equiv C W
      (decidable_sum_groupoid (circle_group C) (circle_group C) W (circle_group_decidable C) (circle_group_decidable C)) G

def circle_decidable_sum_hom_book_equiv (C : CircleSignature)
  (W : WedgeSignature (circle_pointed C) (circle_pointed C)) (G : Group)
  : BookIsEquiv (GroupHom (circle_decidable_sum_group C W) G) (Product (USym G) (USym G))
      (circle_sum_hom_ev C W
        (decidable_sum_groupoid (circle_group C) (circle_group C) W (circle_group_decidable C) (circle_group_decidable C)) G)
  ≔ circle_sum_hom_book_equiv C W
      (decidable_sum_groupoid (circle_group C) (circle_group C) W (circle_group_decidable C) (circle_group_decidable C)) G
