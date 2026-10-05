export "609-monos-and-epis"

{` Chapter 6 (cats.tex): ex:functor-preorders (functors between preorders
   are monotone maps) and the first sentence of rem:adj-in-posets
   (adjunctions between preorders are logical biimplications
   F(p) ≤ q ↔ p ≤ G(q)). The examples of rem:adj-in-posets are in modules
   611-612 (ℤ ⊂ ℚ) and 613 (∃_f ⊣ f^* ⊣ ∀_f). `}

{` ex:functor-preorders: a monotone map, p ≤ p' implies F(p) ≤ F(p'). `}
def MonotoneMap (P Q : Preorder) : Type
  ≔ Σ (P .wild .ob → Q .wild .ob)
      (F ↦ (p p' : P .wild .ob) → P .wild .hom p p' → Q .wild .hom (F p) (F p'))

def preorder_functor_of_monotone (P Q : Preorder) (m : MonotoneMap P Q) : WildFunctor (P .wild) (Q .wild)
  ≔ (obj ≔ m .fst,
     mor ≔ m .snd,
     map_id ≔ a ↦ Q .homprop (m .fst a) (m .fst a) (m .snd a a (P .wild .idn a)) (Q .wild .idn (m .fst a)),
     map_comp ≔ a b c f g ↦ Q .homprop (m .fst a) (m .fst c) (m .snd a c (P .wild .comp a b c g f))
       (Q .wild .comp (m .fst a) (m .fst b) (m .fst c) (m .snd b c g) (m .snd a b f)))

def preorder_monotone_of_functor (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild)) : MonotoneMap P Q
  ≔ (F .obj, F .mor)

{` ex:functor-preorders: "A functor between preorders amounts to a
   monotone map", as an equivalence of types. `}
def preorder_functor_monotone_equiv (P Q : Preorder)
  : Equiv (WildFunctor (P .wild) (Q .wild)) (MonotoneMap P Q)
  ≔ quasi_inverse_equiv (WildFunctor (P .wild) (Q .wild)) (MonotoneMap P Q)
      (preorder_monotone_of_functor P Q) (preorder_functor_of_monotone P Q)
      (F ↦ functor_path (P .wild) (Q .wild) (preorder_homset Q)
        (preorder_functor_of_monotone P Q (preorder_monotone_of_functor P Q F)) F
        (refl (functor_data (P .wild) (Q .wild) F)))
      (m ↦ refl m)

{` rem:adj-in-posets: the logical biimplication F(p) ≤ q ↔ p ≤ G(q). `}
def PreorderAdjointIff (P Q : Preorder) (f : P .wild .ob → Q .wild .ob) (g : Q .wild .ob → P .wild .ob) : Type
  ≔ (p : P .wild .ob) (q : Q .wild .ob)
    → Product (Q .wild .hom (f p) q → P .wild .hom p (g q)) (P .wild .hom p (g q) → Q .wild .hom (f p) q)

{` rem:adj-in-posets, "only if": the transposition of an adjunction gives
   the biimplication. `}
def preorder_adjunction_iff (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild))
  (R : RightAdjointData (P .wild) (Q .wild) F) : PreorderAdjointIff P Q (F .obj) (R .right .obj)
  ≔ p q ↦ (R .transpose p q, adjunction_untranspose (P .wild) (Q .wild) F R p q)

{` rem:adj-in-posets, "if": a monotone G with the biimplication is a right
   adjoint of F; all naturality conditions hold since arrows of preorders
   are unique. `}
def preorder_right_adjoint_from_iff (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild))
  (G : WildFunctor (Q .wild) (P .wild)) (h : PreorderAdjointIff P Q (F .obj) (G .obj))
  : RightAdjointData (P .wild) (Q .wild) F
  ≔ (right ≔ G,
     transpose ≔ p q ↦ h p q .fst,
     transpose_iso ≔ p q ↦ type_equiv_to_is_iso (Q .wild .hom (F .obj p) q) (P .wild .hom p (G .obj q))
       (h p q .fst)
       (iff_equiv (Q .wild .hom (F .obj p) q) (P .wild .hom p (G .obj q))
         (Q .homprop (F .obj p) q) (P .homprop p (G .obj q)) (h p q .fst) (h p q .snd) .equiv),
     natural_left ≔ p p' f q ↦
       pi_prop (Q .wild .hom (F .obj p) q) (_ ↦ P .wild .hom p' (G .obj q)) (_ ↦ P .homprop p' (G .obj q))
         (k ↦ P .wild .comp p' p (G .obj q) (h p q .fst k) f)
         (k ↦ h p' q .fst (Q .wild .comp (F .obj p') (F .obj p) q k (F .mor p' p f))),
     natural_right ≔ p q q' g ↦
       pi_prop (Q .wild .hom (F .obj p) q) (_ ↦ P .wild .hom p (G .obj q')) (_ ↦ P .homprop p (G .obj q'))
         (k ↦ P .wild .comp p (G .obj q) (G .obj q') (G .mor q q' g) (h p q .fst k))
         (k ↦ h p q' .fst (Q .wild .comp (F .obj p) q q' g k)))

def preorder_right_adjoint_from_iff_right (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild))
  (G : WildFunctor (Q .wild) (P .wild)) (h : PreorderAdjointIff P Q (F .obj) (G .obj))
  : Id (WildFunctor (Q .wild) (P .wild)) (preorder_right_adjoint_from_iff P Q F G h .right) G
  ≔ refl G

{` The biimplication alone already makes an object map monotone, on
   either side; so it suffices to give the object maps. `}
def preorder_iff_right_monotone (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild))
  (g : Q .wild .ob → P .wild .ob) (h : PreorderAdjointIff P Q (F .obj) g) : MonotoneMap Q P
  ≔ (g, q q' k ↦ h (g q) q' .fst
       (Q .wild .comp (F .obj (g q)) q q' k (h (g q) q .snd (P .wild .idn (g q)))))

def preorder_iff_left_monotone (P Q : Preorder) (G : WildFunctor (Q .wild) (P .wild))
  (f : P .wild .ob → Q .wild .ob) (h : PreorderAdjointIff P Q f (G .obj)) : MonotoneMap P Q
  ≔ (f, p p' k ↦ h p (f p') .snd
       (P .wild .comp p p' (G .obj (f p')) (h p' (f p') .fst (Q .wild .idn (f p'))) k))

{` Adjunctions from object maps and a biimplication. `}
def preorder_adjunction_from_right_map (P Q : Preorder) (F : WildFunctor (P .wild) (Q .wild))
  (g : Q .wild .ob → P .wild .ob) (h : PreorderAdjointIff P Q (F .obj) g)
  : RightAdjointData (P .wild) (Q .wild) F
  ≔ preorder_right_adjoint_from_iff P Q F
      (preorder_functor_of_monotone Q P (preorder_iff_right_monotone P Q F g h)) h

def preorder_adjunction_from_left_map (P Q : Preorder) (G : WildFunctor (Q .wild) (P .wild))
  (f : P .wild .ob → Q .wild .ob) (h : PreorderAdjointIff P Q f (G .obj)) : WildAdjunction (P .wild) (Q .wild)
  ≔ let F ≔ preorder_functor_of_monotone P Q (preorder_iff_left_monotone P Q G f h) in
    (left ≔ F, right_adjoint ≔ preorder_right_adjoint_from_iff P Q F G h)

{` Litmus: the identity functor of (ℕ, ≤) is its own right adjoint; the
   unit 2 ≤ 2 is the reflexivity witness (difference 0). `}
def nat_identity_self_adjoint : RightAdjointData (NatLeqPreorder .wild) (NatLeqPreorder .wild)
    (functor_identity (NatLeqPreorder .wild))
  ≔ preorder_right_adjoint_from_iff NatLeqPreorder NatLeqPreorder (functor_identity (NatLeqPreorder .wild))
      (functor_identity (NatLeqPreorder .wild)) (p q ↦ (k ↦ k, k ↦ k))

def nat_identity_unit_difference
  : Id Nat (adjunction_unit (NatLeqPreorder .wild) (NatLeqPreorder .wild) (functor_identity (NatLeqPreorder .wild))
      nat_identity_self_adjoint 2 .fst) zero.
  ≔ refl (zero. : Nat)

def monotone_successor : MonotoneMap NatLeqPreorder NatLeqPreorder
  ≔ (n ↦ suc. n, m n k ↦ (k .fst, refl ((x ↦ suc. x) : Nat → Nat) (k .snd)))
