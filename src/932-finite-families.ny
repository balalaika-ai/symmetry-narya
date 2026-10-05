export "286-cycle-notation-equivalence"

{` Chapter 9 (subgroups.tex), helper for the hard direction of lem:epi-surj
   (line 161) and for con:monos-are-equalizers (line 204). The book's draft
   uses an injection of the set of cosets into a group A ("for instance the
   free (abelian) group on G/H"). Constructively, without decidable
   equality, we build the free commutative monoid on a set S as finite
   S-labelled families up to (mere) label-preserving isomorphism, and in
   module 933 its group completion. This module: the families, their
   isomorphisms, the commutative monoid M(S) and generic commutative
   semigroup algebra. No decidability or choice is used. `}

{` A finite S-labelled family: a finite type with a labelling. `}
def GepiFamily (S : Type) : Type ≔ sig (carrier : Type, finite : IsFinite carrier, label : carrier → S)

{` Label-preserving equivalences of families. `}
def GepiFamilyIso (S : Type) (a b : GepiFamily S) : Type
  ≔ Σ (Equiv (a .carrier) (b .carrier)) (e ↦ (i : a .carrier) → Id S (a .label i) (b .label (e .map i)))

def gepi_family_iso_refl (S : Type) (a : GepiFamily S) : GepiFamilyIso S a a
  ≔ (identity_equiv (a .carrier), i ↦ refl (a .label i))

def gepi_family_iso_inverse (S : Type) (a b : GepiFamily S) (e : GepiFamilyIso S a b) : GepiFamilyIso S b a
  ≔ (canonical_inverse_equiv (a .carrier) (b .carrier) (e .fst),
     j ↦
       let i ≔ equiv_inverse_map (a .carrier) (b .carrier) (e .fst) j in
       concat S (b .label j) (b .label (e .fst .map i)) (a .label i)
         (refl (b .label) (inverse (b .carrier) (e .fst .map i) j (equiv_counit (a .carrier) (b .carrier) (e .fst) j)))
         (inverse S (a .label i) (b .label (e .fst .map i)) (e .snd i)))

def gepi_family_iso_compose (S : Type) (a b c : GepiFamily S) (e : GepiFamilyIso S a b) (d : GepiFamilyIso S b c)
  : GepiFamilyIso S a c
  ≔ (compose_equiv (a .carrier) (b .carrier) (c .carrier) (e .fst) (d .fst),
     i ↦ concat S (a .label i) (b .label (e .fst .map i)) (c .label (d .fst .map (e .fst .map i)))
           (e .snd i) (d .snd (e .fst .map i)))

{` Mere isomorphism is an equivalence relation. `}
def gepi_family_relation (S : Type) : EquivalenceRelation (GepiFamily S)
  ≔ ((a b ↦ (Mere (GepiFamilyIso S a b), mere_isprop (GepiFamilyIso S a b))),
     (a ↦ mere (GepiFamilyIso S a a) (gepi_family_iso_refl S a)),
     (a b ↦ trunc_map native_truncation (GepiFamilyIso S a b) (GepiFamilyIso S b a) (gepi_family_iso_inverse S a b)),
     (a b c r t ↦ mere_rec (GepiFamilyIso S a b) (Mere (GepiFamilyIso S a c)) (mere_isprop (GepiFamilyIso S a c))
        (e ↦ trunc_map native_truncation (GepiFamilyIso S b c) (GepiFamilyIso S a c)
          (gepi_family_iso_compose S a b c e) t) r))

{` The empty family, singletons and sums of families. `}
def gepi_empty_family (S : Type) : GepiFamily S
  ≔ (Empty, finite_from_equiv Empty zero. (identity_equiv Empty), x ↦ absurd S x)

def gepi_singleton (S : Type) (s : S) : GepiFamily S ≔ (Unit, finite_unit, _ ↦ s)

def gepi_sum_label (S A B : Type) (l : A → S) (m : B → S) : Sum A B → S
  ≔ [ inl. i ↦ l i | inr. j ↦ m j ]

def gepi_family_sum (S : Type) (a b : GepiFamily S) : GepiFamily S
  ≔ (Sum (a .carrier) (b .carrier), finite_sum (a .carrier) (b .carrier) (a .finite) (b .finite),
     gepi_sum_label S (a .carrier) (b .carrier) (a .label) (b .label))

{` Sums of maps and equivalences with top-level case trees. (Using the
   computation of sum_equiv of module 10, whose map is an anonymous case
   function, under a match triggers the Narya anomaly Meta.Map.find_opt; the
   same holds for anonymous dependent case functions in tuple components.) `}
def gepi_sum_map (A B X Y : Type) (f : A → X) (g : B → Y) : Sum A B → Sum X Y
  ≔ [ inl. a ↦ inl. (f a) | inr. b ↦ inr. (g b) ]

def gepi_sum_map_retract (A B X Y : Type) (f : A → X) (g : B → Y) (f' : X → A) (g' : Y → B)
  (hf : (a : A) → Id A (f' (f a)) a) (hg : (b : B) → Id B (g' (g b)) b) (x : Sum A B)
  : Id (Sum A B) (gepi_sum_map X Y A B f' g' (gepi_sum_map A B X Y f g x)) x
  ≔ match x [ inl. a ↦ inl. (hf a) | inr. b ↦ inr. (hg b) ]

def gepi_sum_equiv (A B X Y : Type) (e : Equiv A X) (d : Equiv B Y) : Equiv (Sum A B) (Sum X Y)
  ≔ quasi_inverse_equiv (Sum A B) (Sum X Y) (gepi_sum_map A B X Y (e .map) (d .map))
      (gepi_sum_map X Y A B (equiv_inverse_map A X e) (equiv_inverse_map B Y d))
      (gepi_sum_map_retract A B X Y (e .map) (d .map) (equiv_inverse_map A X e) (equiv_inverse_map B Y d)
         (equiv_retraction A X e) (equiv_retraction B Y d))
      (gepi_sum_map_retract X Y A B (equiv_inverse_map A X e) (equiv_inverse_map B Y d) (e .map) (d .map)
         (equiv_counit A X e) (equiv_counit B Y d))

def gepi_family_iso_sum_labels (S : Type) (a a' b b' : GepiFamily S) (e : GepiFamilyIso S a a')
  (d : GepiFamilyIso S b b') (x : Sum (a .carrier) (b .carrier))
  : Id S (gepi_family_sum S a b .label x)
      (gepi_family_sum S a' b' .label (gepi_sum_equiv (a .carrier) (b .carrier) (a' .carrier) (b' .carrier) (e .fst) (d .fst) .map x))
  ≔ match x [ inl. i ↦ e .snd i | inr. j ↦ d .snd j ]

def gepi_family_iso_sum (S : Type) (a a' b b' : GepiFamily S) (e : GepiFamilyIso S a a') (d : GepiFamilyIso S b b')
  : GepiFamilyIso S (gepi_family_sum S a b) (gepi_family_sum S a' b')
  ≔ (gepi_sum_equiv (a .carrier) (b .carrier) (a' .carrier) (b' .carrier) (e .fst) (d .fst),
     gepi_family_iso_sum_labels S a a' b b' e d)

def gepi_sum_reassoc (A B C : Type) : Sum (Sum A B) C → Sum A (Sum B C)
  ≔ [ inl. s ↦ match s [ inl. a ↦ inl. a | inr. b ↦ inr. (inl. b) ] | inr. c ↦ inr. (inr. c) ]

def gepi_sum_unreassoc (A B C : Type) : Sum A (Sum B C) → Sum (Sum A B) C
  ≔ [ inl. a ↦ inl. (inl. a) | inr. s ↦ match s [ inl. b ↦ inl. (inr. b) | inr. c ↦ inr. c ] ]

def gepi_sum_reassoc_retract (A B C : Type) (x : Sum (Sum A B) C)
  : Id (Sum (Sum A B) C) (gepi_sum_unreassoc A B C (gepi_sum_reassoc A B C x)) x
  ≔ match x [
  | inl. s ↦ match s [ inl. a ↦ refl (inl. (inl. a) : Sum (Sum A B) C) | inr. b ↦ refl (inl. (inr. b) : Sum (Sum A B) C) ]
  | inr. c ↦ refl (inr. c : Sum (Sum A B) C) ]

def gepi_sum_reassoc_section (A B C : Type) (x : Sum A (Sum B C))
  : Id (Sum A (Sum B C)) (gepi_sum_reassoc A B C (gepi_sum_unreassoc A B C x)) x
  ≔ match x [
  | inl. a ↦ refl (inl. a : Sum A (Sum B C))
  | inr. s ↦ match s [ inl. b ↦ refl (inr. (inl. b) : Sum A (Sum B C)) | inr. c ↦ refl (inr. (inr. c) : Sum A (Sum B C)) ] ]

def gepi_sum_reassoc_equiv (A B C : Type) : Equiv (Sum (Sum A B) C) (Sum A (Sum B C))
  ≔ quasi_inverse_equiv (Sum (Sum A B) C) (Sum A (Sum B C)) (gepi_sum_reassoc A B C) (gepi_sum_unreassoc A B C)
      (gepi_sum_reassoc_retract A B C) (gepi_sum_reassoc_section A B C)

def gepi_family_iso_assoc_labels (S : Type) (a b c : GepiFamily S)
  (x : Sum (Sum (a .carrier) (b .carrier)) (c .carrier))
  : Id S (gepi_family_sum S (gepi_family_sum S a b) c .label x)
      (gepi_family_sum S a (gepi_family_sum S b c) .label (gepi_sum_reassoc_equiv (a .carrier) (b .carrier) (c .carrier) .map x))
  ≔ match x [
  | inl. s ↦ match s [ inl. i ↦ refl (a .label i) | inr. j ↦ refl (b .label j) ]
  | inr. k ↦ refl (c .label k) ]

def gepi_family_iso_assoc (S : Type) (a b c : GepiFamily S)
  : GepiFamilyIso S (gepi_family_sum S (gepi_family_sum S a b) c) (gepi_family_sum S a (gepi_family_sum S b c))
  ≔ (gepi_sum_reassoc_equiv (a .carrier) (b .carrier) (c .carrier), gepi_family_iso_assoc_labels S a b c)

def gepi_sum_swap_equiv (A B : Type) : Equiv (Sum A B) (Sum B A)
  ≔ quasi_inverse_equiv (Sum A B) (Sum B A) (sum_swap A B) (sum_swap B A)
      (sum_swap_involutive A B) (sum_swap_involutive B A)

def gepi_family_iso_comm_labels (S : Type) (a b : GepiFamily S) (x : Sum (a .carrier) (b .carrier))
  : Id S (gepi_family_sum S a b .label x)
      (gepi_family_sum S b a .label (gepi_sum_swap_equiv (a .carrier) (b .carrier) .map x))
  ≔ match x [ inl. i ↦ refl (a .label i) | inr. j ↦ refl (b .label j) ]

def gepi_family_iso_comm (S : Type) (a b : GepiFamily S)
  : GepiFamilyIso S (gepi_family_sum S a b) (gepi_family_sum S b a)
  ≔ (gepi_sum_swap_equiv (a .carrier) (b .carrier), gepi_family_iso_comm_labels S a b)

{` The free commutative monoid M(S): families up to mere isomorphism (a set
   quotient, module 41). Only the semigroup structure is needed below. `}
def GepiMonoid (S : Type) : Type ≔ Quotient (GepiFamily S) (gepi_family_relation S)

def gepi_monoid_class (S : Type) (a : GepiFamily S) : GepiMonoid S
  ≔ quotient_class (GepiFamily S) (gepi_family_relation S) a

def gepi_monoid_set (S : Type) : isSet (GepiMonoid S) ≔ quotient_set (GepiFamily S) (gepi_family_relation S)

def gepi_monoid_iso_path (S : Type) (a b : GepiFamily S) (e : GepiFamilyIso S a b)
  : Id (GepiMonoid S) (gepi_monoid_class S a) (gepi_monoid_class S b)
  ≔ quotient_encode (GepiFamily S) (gepi_family_relation S) a b (mere (GepiFamilyIso S a b) e)

def gepi_monoid_plus_left (S : Type) (a : GepiFamily S) : GepiMonoid S → GepiMonoid S
  ≔ quotient_rec (GepiFamily S) (GepiMonoid S) (gepi_family_relation S) (gepi_monoid_set S)
      (b ↦ gepi_monoid_class S (gepi_family_sum S a b))
      (b b' r ↦ mere_rec (GepiFamilyIso S b b')
         (Id (GepiMonoid S) (gepi_monoid_class S (gepi_family_sum S a b)) (gepi_monoid_class S (gepi_family_sum S a b')))
         (gepi_monoid_set S (gepi_monoid_class S (gepi_family_sum S a b)) (gepi_monoid_class S (gepi_family_sum S a b')))
         (e ↦ gepi_monoid_iso_path S (gepi_family_sum S a b) (gepi_family_sum S a b')
           (gepi_family_iso_sum S a a b b' (gepi_family_iso_refl S a) e)) r)

def gepi_monoid_plus (S : Type) : GepiMonoid S → GepiMonoid S → GepiMonoid S
  ≔ let M ≔ GepiMonoid S in
    quotient_rec (GepiFamily S) (M → M) (gepi_family_relation S) (pi_set M (_ ↦ M) (_ ↦ gepi_monoid_set S))
      (gepi_monoid_plus_left S)
      (a a' r ↦ funext M (_ ↦ M) (gepi_monoid_plus_left S a) (gepi_monoid_plus_left S a')
         (quotient_prop_induction (GepiFamily S) (gepi_family_relation S)
           (m ↦ Id M (gepi_monoid_plus_left S a m) (gepi_monoid_plus_left S a' m))
           (m ↦ gepi_monoid_set S (gepi_monoid_plus_left S a m) (gepi_monoid_plus_left S a' m))
           (b ↦ mere_rec (GepiFamilyIso S a a')
              (Id M (gepi_monoid_class S (gepi_family_sum S a b)) (gepi_monoid_class S (gepi_family_sum S a' b)))
              (gepi_monoid_set S (gepi_monoid_class S (gepi_family_sum S a b)) (gepi_monoid_class S (gepi_family_sum S a' b)))
              (e ↦ gepi_monoid_iso_path S (gepi_family_sum S a b) (gepi_family_sum S a' b)
                (gepi_family_iso_sum S a a' b b e (gepi_family_iso_refl S b))) r)))

{` p([a], [b]) = [a + b] (judgmental; stated once so that the associativity
   proof below does not need to unfold nested quotient recursions). `}
def gepi_monoid_plus_class (S : Type) (a b : GepiFamily S)
  : Id (GepiMonoid S) (gepi_monoid_plus S (gepi_monoid_class S a) (gepi_monoid_class S b))
      (gepi_monoid_class S (gepi_family_sum S a b))
  ≔ refl (gepi_monoid_class S (gepi_family_sum S a b))

def gepi_monoid_assoc_classes (S : Type) (a b c : GepiFamily S)
  : Id (GepiMonoid S)
      (gepi_monoid_plus S (gepi_monoid_plus S (gepi_monoid_class S a) (gepi_monoid_class S b)) (gepi_monoid_class S c))
      (gepi_monoid_plus S (gepi_monoid_class S a) (gepi_monoid_plus S (gepi_monoid_class S b) (gepi_monoid_class S c)))
  ≔ let M ≔ GepiMonoid S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    let sm ≔ gepi_family_sum S in
    calc
      p (p (cl a) (cl b)) (cl c)
      = p (cl (sm a b)) (cl c) by refl ((u ↦ p u (cl c)) : M → M) (gepi_monoid_plus_class S a b)
      = cl (sm (sm a b) c) by gepi_monoid_plus_class S (sm a b) c
      = cl (sm a (sm b c)) by gepi_monoid_iso_path S (sm (sm a b) c) (sm a (sm b c)) (gepi_family_iso_assoc S a b c)
      = p (cl a) (cl (sm b c))
        by inverse M (p (cl a) (cl (sm b c))) (cl (sm a (sm b c))) (gepi_monoid_plus_class S a (sm b c))
      = p (cl a) (p (cl b) (cl c))
        by refl (p (cl a)) (inverse M (p (cl b) (cl c)) (cl (sm b c)) (gepi_monoid_plus_class S b c)) ∎

def gepi_monoid_assoc (S : Type) (x y z : GepiMonoid S)
  : Id (GepiMonoid S) (gepi_monoid_plus S (gepi_monoid_plus S x y) z) (gepi_monoid_plus S x (gepi_monoid_plus S y z))
  ≔ let M ≔ GepiMonoid S in
    let R ≔ gepi_family_relation S in
    let p ≔ gepi_monoid_plus S in
    let cl ≔ gepi_monoid_class S in
    quotient_prop_induction (GepiFamily S) R (x ↦ (y z : M) → Id M (p (p x y) z) (p x (p y z)))
      (x ↦ pi_prop M (y ↦ (z : M) → Id M (p (p x y) z) (p x (p y z)))
         (y ↦ pi_prop M (z ↦ Id M (p (p x y) z) (p x (p y z))) (z ↦ gepi_monoid_set S (p (p x y) z) (p x (p y z)))))
      (a ↦ quotient_prop_induction (GepiFamily S) R
         (y ↦ (z : M) → Id M (p (p (cl a) y) z) (p (cl a) (p y z)))
         (y ↦ pi_prop M (z ↦ Id M (p (p (cl a) y) z) (p (cl a) (p y z)))
            (z ↦ gepi_monoid_set S (p (p (cl a) y) z) (p (cl a) (p y z))))
         (b ↦ quotient_prop_induction (GepiFamily S) R
            (z ↦ Id M (p (p (cl a) (cl b)) z) (p (cl a) (p (cl b) z)))
            (z ↦ gepi_monoid_set S (p (p (cl a) (cl b)) z) (p (cl a) (p (cl b) z)))
            (c ↦ gepi_monoid_assoc_classes S a b c)))
      x y z

def gepi_monoid_comm (S : Type) (x y : GepiMonoid S)
  : Id (GepiMonoid S) (gepi_monoid_plus S x y) (gepi_monoid_plus S y x)
  ≔ let M ≔ GepiMonoid S in
    let R ≔ gepi_family_relation S in
    let p ≔ gepi_monoid_plus S in
    quotient_prop_induction (GepiFamily S) R (x ↦ (y : M) → Id M (p x y) (p y x))
      (x ↦ pi_prop M (y ↦ Id M (p x y) (p y x)) (y ↦ gepi_monoid_set S (p x y) (p y x)))
      (a ↦ quotient_prop_induction (GepiFamily S) R
         (y ↦ Id M (p (gepi_monoid_class S a) y) (p y (gepi_monoid_class S a)))
         (y ↦ gepi_monoid_set S (p (gepi_monoid_class S a) y) (p y (gepi_monoid_class S a)))
         (b ↦ gepi_monoid_iso_path S (gepi_family_sum S a b) (gepi_family_sum S b a) (gepi_family_iso_comm S a b)))
      x y

{` Generic commutative semigroup algebra (M, p) with associativity
   (x y) z = x (y z) and commutativity. `}
def gepi_interchange (M : Type) (p : M → M → M) (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z)))
  (cm : (x y : M) → Id M (p x y) (p y x)) (x y z w : M)
  : Id M (p (p x y) (p z w)) (p (p x z) (p y w))
  ≔ calc
      p (p x y) (p z w)
      = p x (p y (p z w)) by as x y (p z w)
      = p x (p (p y z) w) by refl (p x) (inverse M (p (p y z) w) (p y (p z w)) (as y z w))
      = p x (p (p z y) w) by refl ((u ↦ p x (p u w)) : M → M) (cm y z)
      = p x (p z (p y w)) by refl (p x) (as z y w)
      = p (p x z) (p y w) by inverse M (p (p x z) (p y w)) (p x (p z (p y w))) (as x z (p y w)) ∎

def gepi_shift_last (M : Type) (p : M → M → M) (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z)))
  (cm : (x y : M) → Id M (p x y) (p y x)) (u s k : M)
  : Id M (p (p u s) k) (p (p u k) s)
  ≔ calc
      p (p u s) k
      = p u (p s k) by as u s k
      = p u (p k s) by refl (p u) (cm s k)
      = p (p u k) s by inverse M (p (p u k) s) (p u (p k s)) (as u k s) ∎

def gepi_shift_left_summand (M : Type) (p : M → M → M) (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z)))
  (cm : (x y : M) → Id M (p x y) (p y x)) (x s y k : M)
  : Id M (p (p (p x s) y) k) (p (p (p x y) k) s)
  ≔ calc
      p (p (p x s) y) k
      = p (p x (p s y)) k by refl ((t ↦ p t k) : M → M) (as x s y)
      = p (p x (p y s)) k by refl ((t ↦ p (p x t) k) : M → M) (cm s y)
      = p (p (p x y) s) k by refl ((t ↦ p t k) : M → M) (inverse M (p (p x y) s) (p x (p y s)) (as x y s))
      = p (p (p x y) k) s by gepi_shift_last M p as cm (p x y) s k ∎

def gepi_shift_right_summand (M : Type) (p : M → M → M) (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z)))
  (cm : (x y : M) → Id M (p x y) (p y x)) (x y s k : M)
  : Id M (p (p x (p y s)) k) (p (p (p x y) k) s)
  ≔ calc
      p (p x (p y s)) k
      = p (p (p x y) s) k by refl ((t ↦ p t k) : M → M) (inverse M (p (p x y) s) (p x (p y s)) (as x y s))
      = p (p (p x y) k) s by gepi_shift_last M p as cm (p x y) s k ∎

def gepi_move_summand (M : Type) (p : M → M → M) (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z)))
  (cm : (x y : M) → Id M (p x y) (p y x)) (x s y : M)
  : Id M (p (p x s) y) (p x (p y s))
  ≔ calc
      p (p x s) y
      = p x (p s y) by as x s y
      = p x (p y s) by refl (p x) (cm s y) ∎

{` The transitivity computation of the group completion:
   (a+d)+k = (c+b)+k and (c+f)+l = (e+d)+l give
   (a+f)+((c+d)+(k+l)) = (e+b)+((c+d)+(k+l)). `}
def gepi_completion_trans_algebra (M : Type) (p : M → M → M)
  (as : (x y z : M) → Id M (p (p x y) z) (p x (p y z))) (cm : (x y : M) → Id M (p x y) (p y x))
  (a b c d e f k l : M) (E1 : Id M (p (p a d) k) (p (p c b) k)) (E2 : Id M (p (p c f) l) (p (p e d) l))
  : Id M (p (p a f) (p (p c d) (p k l))) (p (p e b) (p (p c d) (p k l)))
  ≔ let ic ≔ gepi_interchange M p as cm in
    let X1 : Id M (p (p a f) (p c d)) (p (p a d) (p c f))
      ≔ calc
          p (p a f) (p c d)
          = p (p a c) (p f d) by ic a f c d
          = p (p a c) (p d f) by refl (p (p a c)) (cm f d)
          = p (p a d) (p c f) by inverse M (p (p a d) (p c f)) (p (p a c) (p d f)) (ic a d c f) ∎ in
    let X2 : Id M (p (p c b) (p e d)) (p (p e b) (p c d))
      ≔ calc
          p (p c b) (p e d)
          = p (p c e) (p b d) by ic c b e d
          = p (p e c) (p b d) by refl ((u ↦ p u (p b d)) : M → M) (cm c e)
          = p (p e b) (p c d) by inverse M (p (p e b) (p c d)) (p (p e c) (p b d)) (ic e b c d) ∎ in
    calc
      p (p a f) (p (p c d) (p k l))
      = p (p (p a f) (p c d)) (p k l)
        by inverse M (p (p (p a f) (p c d)) (p k l)) (p (p a f) (p (p c d) (p k l))) (as (p a f) (p c d) (p k l))
      = p (p (p a d) (p c f)) (p k l) by refl ((u ↦ p u (p k l)) : M → M) X1
      = p (p (p a d) k) (p (p c f) l) by ic (p a d) (p c f) k l
      = p (p (p c b) k) (p (p c f) l) by refl ((u ↦ p u (p (p c f) l)) : M → M) E1
      = p (p (p c b) k) (p (p e d) l) by refl (p (p (p c b) k)) E2
      = p (p (p c b) (p e d)) (p k l)
        by inverse M (p (p (p c b) (p e d)) (p k l)) (p (p (p c b) k) (p (p e d) l)) (ic (p c b) (p e d) k l)
      = p (p (p e b) (p c d)) (p k l) by refl ((u ↦ p u (p k l)) : M → M) X2
      = p (p e b) (p (p c d) (p k l)) by as (p e b) (p c d) (p k l) ∎
