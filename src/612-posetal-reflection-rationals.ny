export "611-fraction-order-rounding"

{` Chapter 6 (cats.tex), rem:adj-in-posets, ℤ ⊂ ℚ continued. The
   posetal reflection of a preorder (the set quotient by x ~ y iff x ≤ y
   and y ≤ x, module 41) is a poset, and the quotient map is a weak
   equivalence. The rationals with their usual order are the posetal
   reflection of the fraction preorder of module 611 (two fractions are
   identified exactly when a(l+1) = b(k+1)). On ℚ we obtain
   ⌈-⌉ ⊣ ι ⊣ ⌊-⌋ for the inclusion ι : ℤ → ℚ. `}

def preorder_equivalence_relation (P : Preorder) : EquivalenceRelation (P .wild .ob)
  ≔ (predicate ≔ x y ↦ (Product (P .wild .hom x y) (P .wild .hom y x),
        product_prop (P .wild .hom x y) (P .wild .hom y x) (P .homprop x y) (P .homprop y x)),
     reflexive ≔ x ↦ (P .wild .idn x, P .wild .idn x),
     symmetric ≔ x y r ↦ (r .snd, r .fst),
     transitive ≔ x y z r s ↦ (P .wild .comp x y z (s .fst) (r .fst), P .wild .comp z y x (r .snd) (s .snd)))

def PosetalCarrier (P : Preorder) : Type ≔ Quotient (P .wild .ob) (preorder_equivalence_relation P)

def posetal_class (P : Preorder) (x : P .wild .ob) : PosetalCarrier P
  ≔ quotient_class (P .wild .ob) (preorder_equivalence_relation P) x

def preorder_hom_prop_type (P : Preorder) (x y : P .wild .ob) : PropTypes ≔ (P .wild .hom x y, P .homprop x y)

def posetal_leq_left (P : Preorder) (x : P .wild .ob) : PosetalCarrier P → PropTypes
  ≔ quotient_rec (P .wild .ob) PropTypes (preorder_equivalence_relation P) propositions_set
      (preorder_hom_prop_type P x)
      (y y' r ↦ proposition_extensionality (preorder_hom_prop_type P x y) (preorder_hom_prop_type P x y')
        (k ↦ P .wild .comp x y y' (r .fst) k) (k ↦ P .wild .comp x y' y (r .snd) k))

def posetal_leq (P : Preorder) : PosetalCarrier P → PosetalCarrier P → PropTypes
  ≔ quotient_rec (P .wild .ob) (PosetalCarrier P → PropTypes) (preorder_equivalence_relation P)
      (pi_set (PosetalCarrier P) (_ ↦ PropTypes) (_ ↦ propositions_set))
      (posetal_leq_left P)
      (x x' r ↦ funext (PosetalCarrier P) (_ ↦ PropTypes) (posetal_leq_left P x) (posetal_leq_left P x')
        (quotient_prop_induction (P .wild .ob) (preorder_equivalence_relation P)
          (w ↦ Id PropTypes (posetal_leq_left P x w) (posetal_leq_left P x' w))
          (w ↦ propositions_set (posetal_leq_left P x w) (posetal_leq_left P x' w))
          (y ↦ proposition_extensionality (preorder_hom_prop_type P x y) (preorder_hom_prop_type P x' y)
            (k ↦ P .wild .comp x' x y k (r .snd)) (k ↦ P .wild .comp x x' y k (r .fst)))))

{` On classes the order is judgmentally the order of P. `}
def posetal_leq_class (P : Preorder) (x y : P .wild .ob)
  : Id Type (posetal_leq P (posetal_class P x) (posetal_class P y) .fst) (P .wild .hom x y)
  ≔ refl (P .wild .hom x y)

def posetal_leq_refl (P : Preorder) (u : PosetalCarrier P) : posetal_leq P u u .fst
  ≔ quotient_prop_induction (P .wild .ob) (preorder_equivalence_relation P) (w ↦ posetal_leq P w w .fst)
      (w ↦ posetal_leq P w w .snd) (x ↦ P .wild .idn x) u

def posetal_leq_trans (P : Preorder) (u v w : PosetalCarrier P)
  : posetal_leq P u v .fst → posetal_leq P v w .fst → posetal_leq P u w .fst
  ≔ let O ≔ P .wild .ob in
    let R ≔ preorder_equivalence_relation P in
    let L ≔ posetal_leq P in
    let T : PosetalCarrier P → PosetalCarrier P → PosetalCarrier P → Type
      ≔ u v w ↦ L u v .fst → L v w .fst → L u w .fst in
    let hT : (u v w : PosetalCarrier P) → isProp (T u v w)
      ≔ u v w ↦ pi_prop (L u v .fst) (_ ↦ L v w .fst → L u w .fst)
          (_ ↦ pi_prop (L v w .fst) (_ ↦ L u w .fst) (_ ↦ L u w .snd)) in
    quotient_prop_induction O R (u ↦ T u v w) (u ↦ hT u v w) (x ↦
      quotient_prop_induction O R (v ↦ T (posetal_class P x) v w) (v ↦ hT (posetal_class P x) v w) (y ↦
        quotient_prop_induction O R (w ↦ T (posetal_class P x) (posetal_class P y) w)
          (w ↦ hT (posetal_class P x) (posetal_class P y) w)
          (z ↦ f g ↦ P .wild .comp x y z g f) w) v) u

def posetal_preorder (P : Preorder) : Preorder
  ≔ preorder_of_relation (PosetalCarrier P, posetal_leq P, posetal_leq_refl P, posetal_leq_trans P)

def posetal_antisymmetric (P : Preorder) : IsAntisymmetric (posetal_preorder P .wild)
  ≔ let O ≔ P .wild .ob in
    let R ≔ preorder_equivalence_relation P in
    let Q ≔ PosetalCarrier P in
    let T : Q → Q → Type ≔ u v ↦ posetal_leq P u v .fst → posetal_leq P v u .fst → Id Q u v in
    let hT : (u v : Q) → isProp (T u v)
      ≔ u v ↦ pi_prop (posetal_leq P u v .fst) (_ ↦ posetal_leq P v u .fst → Id Q u v)
          (_ ↦ pi_prop (posetal_leq P v u .fst) (_ ↦ Id Q u v) (_ ↦ quotient_set O R u v)) in
    u v ↦ quotient_prop_induction O R (u ↦ T u v) (u ↦ hT u v) (x ↦
      quotient_prop_induction O R (v ↦ T (posetal_class P x) v) (v ↦ hT (posetal_class P x) v)
        (y f g ↦ quotient_encode O R x y (f, g)) v) u

{` The posetal reflection is a poset. `}
def PosetalReflection (P : Preorder) : Poset ≔ poset_from_antisymmetric (posetal_preorder P) (posetal_antisymmetric P)

{` The quotient map is a functor which is fully faithful and essentially
   surjective, i.e. a weak equivalence (def:we-cat). `}
def posetal_unit_functor (P : Preorder) : WildFunctor (P .wild) (PosetalReflection P .wild)
  ≔ preorder_functor_of_monotone P (posetal_preorder P) (posetal_class P, x y k ↦ k)

def posetal_unit_weak_equivalence (P : Preorder)
  : IsWeakEquivalence (P .wild) (PosetalReflection P .wild) (posetal_unit_functor P)
  ≔ ((x y ↦ prop_map_embedding (P .wild .hom x y) (P .wild .hom x y) (P .homprop x y) (P .homprop x y) (k ↦ k),
      x y k ↦ mere (BookFiber (P .wild .hom x y) (P .wild .hom x y) (k ↦ k) k) (k, refl k)),
     u ↦ mere_rec (BookFiber (P .wild .ob) (PosetalCarrier P) (posetal_class P) u)
       (Mere (Σ (P .wild .ob) (c ↦ CatIso (PosetalReflection P .wild) (posetal_class P c) u)))
       (mere_isprop (Σ (P .wild .ob) (c ↦ CatIso (PosetalReflection P .wild) (posetal_class P c) u)))
       (w ↦ mere (Σ (P .wild .ob) (c ↦ CatIso (PosetalReflection P .wild) (posetal_class P c) u))
         (w .fst, cat_idtoiso (PosetalReflection P .wild) (posetal_class P (w .fst)) u
           (inverse (PosetalCarrier P) u (posetal_class P (w .fst)) (w .snd))))
       (quotient_surjective (P .wild .ob) (preorder_equivalence_relation P) u))

{` A monotone map into a poset descends to the posetal reflection. `}
def posetal_descend (P : Preorder) (Q : Poset) (m : MonotoneMap P (poset_preorder Q))
  : PosetalCarrier P → Q .wild .ob
  ≔ quotient_rec (P .wild .ob) (Q .wild .ob) (preorder_equivalence_relation P) (poset_objects_set Q) (m .fst)
      (x y r ↦ preorder_univalent_antisymmetric (poset_preorder Q) (Q .univalent) (m .fst x) (m .fst y)
        (m .snd x y (r .fst)) (m .snd y x (r .snd)))

{` The rationals with their usual order: fractions modulo the "≤ both
   ways" relation, which is the usual cross-multiplication equality. `}
def RationalPoset : Poset ≔ PosetalReflection FracPreorder

def Rational : Type ≔ RationalPoset .wild .ob

def frac_equivalent_iff_cross_equal (x y : Frac)
  : Product (Product (FracLe x y) (FracLe y x)
        → Id Int (int_mul (x .fst) (pos. (suc. (y .snd)))) (int_mul (y .fst) (pos. (suc. (x .snd)))))
      (Id Int (int_mul (x .fst) (pos. (suc. (y .snd)))) (int_mul (y .fst) (pos. (suc. (x .snd))))
        → Product (FracLe x y) (FracLe y x))
  ≔ let l ≔ int_mul (x .fst) (pos. (suc. (y .snd))) in
    let r ≔ int_mul (y .fst) (pos. (suc. (x .snd))) in
    (h ↦ int_le_antisym l r (h .fst) (h .snd),
     p ↦ (int_le_from_equal l r p, int_le_from_equal r l (inverse Int l r p)))

def rational_of_frac (x : Frac) : Rational ≔ posetal_class FracPreorder x

def rational_of_int (n : Int) : Rational ≔ rational_of_frac (frac_of_int n)

def rational_inclusion_functor : WildFunctor (IntLeqPreorder .wild) (RationalPoset .wild)
  ≔ preorder_functor_of_monotone IntLeqPreorder (posetal_preorder FracPreorder) (rational_of_int, m n h ↦ h)

def rational_floor : Rational → Int
  ≔ posetal_descend FracPreorder int_leq_poset
      (preorder_iff_right_monotone IntLeqPreorder FracPreorder frac_inclusion_functor frac_floor frac_floor_iff)

def rational_ceiling : Rational → Int
  ≔ posetal_descend FracPreorder int_leq_poset
      (preorder_iff_left_monotone FracPreorder IntLeqPreorder frac_inclusion_functor frac_ceiling frac_ceiling_iff)

def rational_floor_iff : PreorderAdjointIff IntLeqPreorder (posetal_preorder FracPreorder) rational_of_int rational_floor
  ≔ n u ↦ quotient_prop_induction Frac (preorder_equivalence_relation FracPreorder)
      (u ↦ Product (posetal_leq FracPreorder (rational_of_int n) u .fst → IntLe n (rational_floor u))
        (IntLe n (rational_floor u) → posetal_leq FracPreorder (rational_of_int n) u .fst))
      (u ↦ product_prop (posetal_leq FracPreorder (rational_of_int n) u .fst → IntLe n (rational_floor u))
        (IntLe n (rational_floor u) → posetal_leq FracPreorder (rational_of_int n) u .fst)
        (pi_prop (posetal_leq FracPreorder (rational_of_int n) u .fst) (_ ↦ IntLe n (rational_floor u))
          (_ ↦ int_le_prop n (rational_floor u)))
        (pi_prop (IntLe n (rational_floor u)) (_ ↦ posetal_leq FracPreorder (rational_of_int n) u .fst)
          (_ ↦ posetal_leq FracPreorder (rational_of_int n) u .snd)))
      (x ↦ frac_floor_iff n x) u

def rational_ceiling_iff
  : PreorderAdjointIff (posetal_preorder FracPreorder) IntLeqPreorder rational_ceiling rational_of_int
  ≔ u n ↦ quotient_prop_induction Frac (preorder_equivalence_relation FracPreorder)
      (u ↦ Product (IntLe (rational_ceiling u) n → posetal_leq FracPreorder u (rational_of_int n) .fst)
        (posetal_leq FracPreorder u (rational_of_int n) .fst → IntLe (rational_ceiling u) n))
      (u ↦ product_prop (IntLe (rational_ceiling u) n → posetal_leq FracPreorder u (rational_of_int n) .fst)
        (posetal_leq FracPreorder u (rational_of_int n) .fst → IntLe (rational_ceiling u) n)
        (pi_prop (IntLe (rational_ceiling u) n) (_ ↦ posetal_leq FracPreorder u (rational_of_int n) .fst)
          (_ ↦ posetal_leq FracPreorder u (rational_of_int n) .snd))
        (pi_prop (posetal_leq FracPreorder u (rational_of_int n) .fst) (_ ↦ IntLe (rational_ceiling u) n)
          (_ ↦ int_le_prop (rational_ceiling u) n)))
      (x ↦ frac_ceiling_iff x n) u

{` rem:adj-in-posets: ι : ℤ ↪ ℚ has the right adjoint ⌊-⌋ (rounding down)
   and the left adjoint ⌈-⌉ (rounding up), ⌈-⌉ ⊣ ι ⊣ ⌊-⌋. `}
def rational_floor_right_adjoint
  : RightAdjointData (IntLeqPreorder .wild) (RationalPoset .wild) rational_inclusion_functor
  ≔ preorder_adjunction_from_right_map IntLeqPreorder (posetal_preorder FracPreorder) rational_inclusion_functor
      rational_floor rational_floor_iff

def rational_ceiling_adjunction : WildAdjunction (RationalPoset .wild) (IntLeqPreorder .wild)
  ≔ preorder_adjunction_from_left_map (posetal_preorder FracPreorder) IntLeqPreorder rational_inclusion_functor
      rational_ceiling rational_ceiling_iff

def rational_ceiling_adjunction_right
  : Id (WildFunctor (IntLeqPreorder .wild) (RationalPoset .wild)) (rational_ceiling_adjunction .right_adjoint .right)
      rational_inclusion_functor
  ≔ refl rational_inclusion_functor

def rational_inclusion_embedding : IsEmbedding Int Rational rational_of_int
  ≔ path_reflecting_set_embedding Int Rational (poset_objects_set RationalPoset) rational_of_int
      (m n p ↦ int_le_antisym m n
        (quotient_effective Frac (preorder_equivalence_relation FracPreorder) (frac_of_int m) (frac_of_int n) .map p .fst)
        (quotient_effective Frac (preorder_equivalence_relation FracPreorder) (frac_of_int m) (frac_of_int n) .map p .snd))

{` Litmus checks: 1/1 = 2/2 in ℚ; ⌊7/2⌋ = 3 and ⌈7/2⌉ = 4 computed on ℚ;
   ι is injective (ℤ ↪ ℚ). `}
def rational_one_two_halves : Id Rational (rational_of_frac (pos. 1, zero.)) (rational_of_frac (pos. 2, 1))
  ≔ quotient_encode Frac (preorder_equivalence_relation FracPreorder) (pos. 1, zero.) (pos. 2, 1) (star., star.)

def rational_floor_seven_halves : Id Int (rational_floor (rational_of_frac (pos. 7, 1))) (pos. 3)
  ≔ refl (pos. 3 : Int)

def rational_ceiling_seven_halves : Id Int (rational_ceiling (rational_of_frac (pos. 7, 1))) (pos. 4)
  ≔ refl (pos. 4 : Int)
