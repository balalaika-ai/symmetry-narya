export "412-symmetric-group-two"

{` Chapter 4, sec:typegroup, motivating examples (group.tex 65-160). `}

{` ex:base=base, for every circle C. The symmetries of base are the
   integers, n ↦ loopⁿ (circle_group_usym_integers, cor:S1groupoid), every
   symmetry is a power of the generating symmetry loop, and composition of
   symmetries corresponds to addition of integers: loopⁿ · loopᵐ = loop^{n+m}. `}
def circle_power (C : CircleSignature) (n : Int) : USym (circle_group C)
  ≔ loop_power (C .carrier) (C .base) (C .loop) n

def circle_every_symmetry_power (C : CircleSignature) (g : USym (circle_group C))
  : Id (USym (circle_group C)) (circle_power C (circle_winding C g)) g
  ≔ circle_power_winding C g

def circle_power_concat (C : CircleSignature) (n m : Int)
  : Id (USym (circle_group C))
      (concat (C .carrier) (C .base) (C .base) (C .base) (circle_power C n) (circle_power C m))
      (circle_power C (int_add n m))
  ≔ equivalence_injective (USym (circle_group C)) Int
      (native_equivalence (USym (circle_group C)) Int (circle_loop_integer_equiv C))
      (concat (C .carrier) (C .base) (C .base) (C .base) (circle_power C n) (circle_power C m))
      (circle_power C (int_add n m))
      (calc
        circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) (circle_power C n) (circle_power C m))
        = int_add (circle_winding C (circle_power C n)) (circle_winding C (circle_power C m))
          by circle_winding_composition C (circle_power C n) (circle_power C m)
        = int_add n m by refl int_add (circle_winding_power C n) (circle_winding_power C m)
        = circle_winding C (circle_power C (int_add n m))
          by inverse Int (circle_winding C (circle_power C (int_add n m))) (int_add n m)
            (circle_winding_power C (int_add n m)) ∎)

{` The same in the book's notation for the group operation:
   loopⁿ · loopᵐ = loop^{n+m} with g · h = usym_mul g h. `}
def circle_power_mul (C : CircleSignature) (n m : Int)
  : Id (USym (circle_group C)) (usym_mul (circle_group C) (circle_power C n) (circle_power C m))
      (circle_power C (int_add n m))
  ≔ concat (USym (circle_group C)) (usym_mul (circle_group C) (circle_power C n) (circle_power C m))
      (circle_power C (int_add m n)) (circle_power C (int_add n m))
      (circle_power_concat C m n) (refl (circle_power C) (int_add_comm m n))

{` The winding number turns composition into addition. `}
def circle_winding_mul (C : CircleSignature) (g h : USym (circle_group C))
  : Id Int (circle_winding C (usym_mul (circle_group C) g h)) (int_add (circle_winding C g) (circle_winding C h))
  ≔ concat Int (circle_winding C (usym_mul (circle_group C) g h))
      (int_add (circle_winding C h) (circle_winding C g)) (int_add (circle_winding C g) (circle_winding C h))
      (circle_winding_composition C h g) (int_add_comm (circle_winding C h) (circle_winding C g))

{` The example at group.tex:89. FinSet_2 pointed at 2 is the classifying
   type of Σ_2 by definition; its symmetries 2 = 2 are exactly refl and swap
   (sigma2_usym_equiv, sigma2_cases, sigma2_swap_nontrivial) and swap·swap = refl
   (sigma2_swap_squared), module 412. `}
def finset_two_pointed : Id Pointed (BG (symmetric_group two)) (BookFiniteSetsAt two, component_point SetTypes (standard_set two))
  ≔ refl (BG (symmetric_group two))

{` The map S¹ → FinSet_2 with base ↦ 2 and loop ↦ swap (circle recursion,
   with its computation rule circle_rec_beta as an identification), pointed by
   that rule; on symmetries it sends loop to swap. `}
def circle_finset_two_map (C : CircleSignature) : C .carrier → BookFiniteSetsAt two
  ≔ circle_rec C (BookFiniteSetsAt two) (shape (symmetric_group two), sigma2_swap)

def circle_finset_two_beta (C : CircleSignature)
  : Id (FreeLoop (BookFiniteSetsAt two)) (circle_eval C (BookFiniteSetsAt two) (circle_finset_two_map C))
      (shape (symmetric_group two), sigma2_swap)
  ≔ circle_rec_beta C (BookFiniteSetsAt two) (shape (symmetric_group two), sigma2_swap)

def circle_finset_two_pointed (C : CircleSignature) : BookPointedMap (circle_pointed C) (BG (symmetric_group two))
  ≔ pointed_circle_loop_rec C (BookFiniteSetsAt two) (shape (symmetric_group two)) sigma2_swap

def circle_finset_two_loop (C : CircleSignature)
  : Id (USym (symmetric_group two))
      (loops_map (circle_pointed C) (BG (symmetric_group two)) (circle_finset_two_pointed C) (C .loop)) sigma2_swap
  ≔ pointed_circle_loop_rec_beta C (BookFiniteSetsAt two) (shape (symmetric_group two)) sigma2_swap

{` rem:heap-preview. The ternary operation (p, q, r) ↦ p q⁻¹ r on a = a'
   (book composition order: first r, then q⁻¹, then p), with the heap laws
   p p⁻¹ r = r and p r⁻¹ r = p. `}
def path_heap_op (A : Type) (a a' : A) (p q r : Id A a a') : Id A a a'
  ≔ concat A a a a' (concat A a a' a r (inverse A a a' q)) p

def concat_cancel_final_inverse_general (A : Type) (a a' : A) (r p : Id A a a')
  : Id (Id A a a') (concat A a a a' (concat A a a' a r (inverse A a a' p)) p) r
  ≔ calc
      concat A a a a' (concat A a a' a r (inverse A a a' p)) p
      = concat A a a' a' r (concat A a' a a' (inverse A a a' p) p)
        by concat_assoc A a a' a a' r (inverse A a a' p) p
      = concat A a a' a' r (refl a') by refl (concat A a a' a' r) (concat_inverse_left A a a' p)
      = r by concat_p1 A a a' r ∎

def path_heap_cancel_left (A : Type) (a a' : A) (p r : Id A a a')
  : Id (Id A a a') (path_heap_op A a a' p p r) r
  ≔ concat_cancel_final_inverse_general A a a' r p

def path_heap_cancel_right (A : Type) (a a' : A) (p r : Id A a a')
  : Id (Id A a a') (path_heap_op A a a' p r r) p
  ≔ calc
      concat A a a a' (concat A a a' a r (inverse A a a' r)) p
      = concat A a a a' (refl a) p by refl ((l ↦ concat A a a a' l p) : Id A a a → Id A a a')
          (concat_inverse_right A a a' r)
      = p by concat_1p A a a' p ∎

{` Transport along f : a = a' in the family x ↦ (a = x) compares a = a with
   a = a'; it is the equivalence l ↦ l · f (concatenation, by definition of
   concat), and it respects the ternary operation. `}
def path_heap_transport_equiv (A : Type) (a a' : A) (f : Id A a a') : Equiv (Id A a a) (Id A a a')
  ≔ transport_equiv (Id A a a) (Id A a a') (refl ((x ↦ Id A a x) : A → Type) f)

def path_heap_transport_map (A : Type) (a a' : A) (f : Id A a a') (l : Id A a a)
  : Id (Id A a a') (path_heap_transport_equiv A a a' f .map l) (concat A a a a' l f)
  ≔ refl (concat A a a a' l f)

def path_heap_transport_respects (A : Type) (a a' : A) (f : Id A a a') (p q r : Id A a a)
  : Id (Id A a a') (concat A a a a' (path_heap_op A a a p q r) f)
      (path_heap_op A a a' (concat A a a a' p f) (concat A a a a' q f) (concat A a a a' r f))
  ≔ J A a (a' f ↦ Id (Id A a a') (concat A a a a' (path_heap_op A a a p q r) f)
        (path_heap_op A a a' (concat A a a a' p f) (concat A a a a' q f) (concat A a a a' r f)))
      (calc
        concat A a a a (path_heap_op A a a p q r) (refl a) = path_heap_op A a a p q r
          by concat_p1 A a a (path_heap_op A a a p q r)
        = path_heap_op A a a (concat A a a a p (refl a)) (concat A a a a q (refl a)) (concat A a a a r (refl a))
          by refl ((u v w ↦ path_heap_op A a a u v w) : Id A a a → Id A a a → Id A a a → Id A a a)
            (inverse (Id A a a) (concat A a a a p (refl a)) p (concat_p1 A a a p))
            (inverse (Id A a a) (concat A a a a q (refl a)) q (concat_p1 A a a q))
            (inverse (Id A a a) (concat A a a a r (refl a)) r (concat_p1 A a a r)) ∎)
      a' f

{` xca:groups, general part (instantiated at the constructed circle in
   module 416). For any circle C and any connectedness and groupoid
   witnesses c, g of S¹, the group H ≔ mkgroup(S¹, base, c, g) has the same
   classifying pointed type as Z = circle_group C. The identity and the flip
   of the circle (base ↦ base, loop ↦ loop⁻¹; rem:flipthecircle) are pointed
   equivalences BZ ≃ BH, giving two identifications Z = H, and they differ. `}
def circle_group_with (C : CircleSignature) (c : Connected (C .carrier)) (g : isGroupoid (C .carrier)) : Group
  ≔ mkgroup (C .carrier, C .base, c, g)

def circle_identity_pointed_equiv (C : CircleSignature) : BookPointedEquiv (circle_pointed C) (circle_pointed C)
  ≔ ((identity (C .carrier), refl (C .base)), identity_book_equiv (C .carrier) .equiv)

def circle_flip_pointed_equiv (C : CircleSignature) : BookPointedEquiv (circle_pointed C) (circle_pointed C)
  ≔ (pointed_circle_loop_rec C (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop)),
      circle_reflection_equiv C .equiv)

def circle_group_identity_path (C : CircleSignature) (c : Connected (C .carrier)) (g : isGroupoid (C .carrier))
  : Id Group (circle_group C) (circle_group_with C c g)
  ≔ group_path_from_pointed_equiv (circle_group C) (circle_group_with C c g) (circle_identity_pointed_equiv C)

def circle_group_flip_path (C : CircleSignature) (c : Connected (C .carrier)) (g : isGroupoid (C .carrier))
  : Id Group (circle_group C) (circle_group_with C c g)
  ≔ group_path_from_pointed_equiv (circle_group C) (circle_group_with C c g) (circle_flip_pointed_equiv C)

{` On symmetries the first sends loop to loop, the second loop to loop⁻¹. `}
def circle_identity_equiv_loop (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base))
      (loops_map (circle_pointed C) (circle_pointed C) (circle_identity_pointed_equiv C .fst) (C .loop)) (C .loop)
  ≔ loop_conjugate_at_refl (C .carrier) (C .base) (C .loop)

def circle_flip_equiv_loop (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base))
      (loops_map (circle_pointed C) (circle_pointed C) (circle_flip_pointed_equiv C .fst) (C .loop))
      (inverse (C .carrier) (C .base) (C .base) (C .loop))
  ≔ pointed_circle_loop_rec_beta C (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop))

def circle_group_iso_eval (C : CircleSignature) (c : Connected (C .carrier)) (g : isGroupoid (C .carrier))
  (w : GroupIso (circle_group C) (circle_group_with C c g)) : Id (C .carrier) (C .base) (C .base)
  ≔ usym_hom (circle_group C) (circle_group_with C c g) (w .fst) (C .loop)

def circle_group_paths_differ (C : CircleSignature) (c : Connected (C .carrier)) (g : isGroupoid (C .carrier))
  (h : Id (Id Group (circle_group C) (circle_group_with C c g))
    (circle_group_identity_path C c g) (circle_group_flip_path C c g))
  : Empty
  ≔ let G ≔ circle_group C in let H ≔ circle_group_with C c g in
    let E ≔ group_path_iso_equiv G H in
    let f1 ≔ circle_identity_pointed_equiv C in let f2 ≔ circle_flip_pointed_equiv C in
    let i1 : GroupIso G H ≔ (mkhom G H (f1 .fst), f1 .snd) in
    let i2 : GroupIso G H ≔ (mkhom G H (f2 .fst), f2 .snd) in
    let Emap : Id Group G H → GroupIso G H ≔ p ↦ E .map p in
    let q : Id (GroupIso G H) i1 i2
      ≔ calc
          i1 = E .map (circle_group_identity_path C c g)
            by inverse (GroupIso G H) (E .map (circle_group_identity_path C c g)) i1
              (equiv_counit (Id Group G H) (GroupIso G H) E i1)
          = E .map (circle_group_flip_path C c g) by refl Emap h
          = i2 by equiv_counit (Id Group G H) (GroupIso G H) E i2 ∎ in
    let L ≔ C .loop in
    let Linv ≔ inverse (C .carrier) (C .base) (C .base) L in
    let r : Id (Id (C .carrier) (C .base) (C .base)) L Linv
      ≔ calc
          L = circle_group_iso_eval C c g i1
            by inverse (Id (C .carrier) (C .base) (C .base)) (circle_group_iso_eval C c g i1) L
              (circle_identity_equiv_loop C)
          = circle_group_iso_eval C c g i2 by refl (circle_group_iso_eval C c g) q
          = Linv by circle_flip_equiv_loop C ∎ in
    int_encode (pos. (suc. zero.)) (neg. zero.)
      (calc
        (pos. (suc. zero.) : Int) = circle_winding C L
          by inverse Int (circle_winding C L) (pos. (suc. zero.)) (circle_winding_loop C)
        = circle_winding C Linv by refl (circle_winding C) r
        = (neg. zero. : Int) by circle_winding_inverse_loop C ∎)
