export "602-functors"

{` Chapter 6, sections 6.4-6.7 (core): representable functors, opposite
   functors, adjunctions, equivalences of (pre)categories. `}

{` ex:repr-functors: the covariant representable k_c = Hom(c, -) : C → U,
   acting by postcomposition. The functor laws are identifications of
   functions, obtained from λ and α by function extensionality. `}
def covariant_representable (C : WildPrecat) (c : C .ob) : WildFunctor C TypeWild
  ≔ (obj ≔ x ↦ C .hom c x,
     mor ≔ x y g k ↦ C .comp c x y g k,
     map_id ≔ x ↦ funext (C .hom c x) (_ ↦ C .hom c x) (k ↦ C .comp c x x (C .idn x) k) (k ↦ k)
       (k ↦ C .lu c x k),
     map_comp ≔ x y z f g ↦ funext (C .hom c x) (_ ↦ C .hom c z)
       (k ↦ C .comp c x z (C .comp x y z g f) k) (k ↦ C .comp c y z g (C .comp c x y f k))
       (k ↦ inverse (C .hom c z) (C .comp c y z g (C .comp c x y f k)) (C .comp c x z (C .comp x y z g f) k)
         (C .assoc c x y z k f g)))

{` ex:repr-functors: the contravariant representable h_c = Hom(-, c) :
   C^op → U, acting by precomposition. `}
def contravariant_representable (C : WildPrecat) (c : C .ob) : WildFunctor (OppositeWild C) TypeWild
  ≔ (obj ≔ x ↦ C .hom x c,
     mor ≔ x y g k ↦ C .comp y x c k g,
     map_id ≔ x ↦ funext (C .hom x c) (_ ↦ C .hom x c) (k ↦ C .comp x x c k (C .idn x)) (k ↦ k)
       (k ↦ C .ru x c k),
     map_comp ≔ x y z f g ↦ funext (C .hom x c) (_ ↦ C .hom z c)
       (k ↦ C .comp z x c k (C .comp z y x f g)) (k ↦ C .comp z y c (C .comp y x c k f) g)
       (k ↦ C .assoc z y x c g f k))

{` The opposite of a wild functor, F^op : C^op → D^op. `}
def opposite_functor (C D : WildPrecat) (F : WildFunctor C D)
  : WildFunctor (OppositeWild C) (OppositeWild D)
  ≔ (obj ≔ F .obj,
     mor ≔ x y f ↦ F .mor y x f,
     map_id ≔ F .map_id,
     map_comp ≔ x y z f g ↦ F .map_comp z y x g f)

{` def:adjunction. The data of a right adjoint to F: a functor G, the
   transposition maps α_{c,d} : Hom_D(F c, d) → Hom_C(c, G d), each an
   isomorphism in the wild category of types (biinvertible), natural in c
   and in d. Naturality is stated separately in each variable, as in the
   prose before the definition ("if we fix either X or Y, then we get
   natural transformations"); adjunction_nat_trans_left/right below show
   that these are exactly the naturality squares of wild natural
   transformations between the representable composites. `}
def RightAdjointData (C D : WildPrecat) (F : WildFunctor C D) : Type ≔ sig (
  right : WildFunctor D C,
  transpose : (c : C .ob) (d : D .ob) → D .hom (F .obj c) d → C .hom c (right .obj d),
  transpose_iso : (c : C .ob) (d : D .ob)
    → CatIsIso TypeWild (D .hom (F .obj c) d) (C .hom c (right .obj d)) (transpose c d),
  natural_left : (c c' : C .ob) (f : C .hom c' c) (d : D .ob)
    → Id (D .hom (F .obj c) d → C .hom c' (right .obj d))
        (k ↦ C .comp c' c (right .obj d) (transpose c d k) f)
        (k ↦ transpose c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f))),
  natural_right : (c : C .ob) (d d' : D .ob) (g : D .hom d d')
    → Id (D .hom (F .obj c) d → C .hom c (right .obj d'))
        (k ↦ C .comp c (right .obj d) (right .obj d') (right .mor d d' g) (transpose c d k))
        (k ↦ transpose c d' (D .comp (F .obj c) d d' g k)) )

{` def:adjunction: a (wild) adjunction F ⊣ G. `}
def WildAdjunction (C D : WildPrecat) : Type
  ≔ sig (left : WildFunctor C D, right_adjoint : RightAdjointData C D left)

{` For fixed d, α_{-,d} is a wild natural transformation
   Hom_D(F -, d) → Hom_C(-, G d) of functors C^op → U, and for fixed c,
   α_{c,-} is one Hom_D(F c, -) → Hom_C(c, G -) of functors D → U. `}
def adjunction_nat_trans_left (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (d : D .ob)
  : WildNatTrans (OppositeWild C) TypeWild
      (functor_compose (OppositeWild C) (OppositeWild D) TypeWild (contravariant_representable D d)
        (opposite_functor C D F))
      (contravariant_representable C (R .right .obj d))
  ≔ (component ≔ c ↦ R .transpose c d,
     natural ≔ c c' f ↦ R .natural_left c c' f d)

def adjunction_nat_trans_right (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob)
  : WildNatTrans D TypeWild (covariant_representable D (F .obj c))
      (functor_compose D C TypeWild (covariant_representable C c) (R .right))
  ≔ (component ≔ d ↦ R .transpose c d,
     natural ≔ d d' g ↦ R .natural_right c d d' g)

{` The inverse transposition Hom_C(c, G d) → Hom_D(F c, d); we use the
   section supplied by the isomorphism data. `}
def adjunction_untranspose (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) : C .hom c (R .right .obj d) → D .hom (F .obj c) d
  ≔ R .transpose_iso c d .fst .fst

def adjunction_untranspose_section (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (m : C .hom c (R .right .obj d))
  : Id (C .hom c (R .right .obj d)) (R .transpose c d (adjunction_untranspose C D F R c d m)) m
  ≔ R .transpose_iso c d .fst .snd (refl m)

def adjunction_transpose_equiv (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) : Equiv (D .hom (F .obj c) d) (C .hom c (R .right .obj d))
  ≔ (R .transpose c d,
     type_is_iso_to_equiv (D .hom (F .obj c) d) (C .hom c (R .right .obj d)) (R .transpose c d)
       (R .transpose_iso c d))

{` eq:adj-unit-counit: the unit η_c, the transpose of id_{F c}, and the
   counit ε_d, the inverse transpose of id_{G d}. `}
def adjunction_unit (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) (c : C .ob)
  : C .hom c (R .right .obj (F .obj c))
  ≔ R .transpose c (F .obj c) (D .idn (F .obj c))

def adjunction_counit (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) (d : D .ob)
  : D .hom (F .obj (R .right .obj d)) d
  ≔ adjunction_untranspose C D F R (R .right .obj d) d (C .idn (R .right .obj d))

{` def:cat-equiv. F is an equivalence of (pre)categories if it is a left
   adjoint whose unit and counit are isomorphisms (componentwise, which
   is equivalent to being isomorphisms in the functor precategories by
   xca:funext-nat-trans). C ≃ D is the type of equivalences. `}
def IsCatEquivalence (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ Σ (RightAdjointData C D F) (R ↦
      Product ((c : C .ob) → CatIsIso C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c))
        ((d : D .ob) → CatIsIso D (F .obj (R .right .obj d)) d (adjunction_counit C D F R d)))

def CatEquivalence (C D : WildPrecat) : Type ≔ Σ (WildFunctor C D) (IsCatEquivalence C D)

{` The identity functor is an equivalence (the identity equivalence used
   in cor:Cat-ua). `}
def identity_right_adjoint (C : WildPrecat) : RightAdjointData C C (functor_identity C)
  ≔ (right ≔ functor_identity C,
     transpose ≔ c d k ↦ k,
     transpose_iso ≔ c d ↦ cat_identity_is_iso TypeWild (C .hom c d),
     natural_left ≔ c c' f d ↦ refl (k ↦ C .comp c' c d k f),
     natural_right ≔ c d d' g ↦ refl (k ↦ C .comp c d d' g k))

def identity_is_cat_equivalence (C : WildPrecat) : IsCatEquivalence C C (functor_identity C)
  ≔ (identity_right_adjoint C, (c ↦ cat_identity_is_iso C c, d ↦ cat_identity_is_iso C d))

def cat_equivalence_identity (C : WildPrecat) : CatEquivalence C C
  ≔ (functor_identity C, identity_is_cat_equivalence C)

{` Litmus: the unit and counit of the identity adjunction are identities. `}
def identity_adjunction_unit (C : WildPrecat) (c : C .ob)
  : Id (C .hom c c) (adjunction_unit C C (functor_identity C) (identity_right_adjoint C) c) (C .idn c)
  ≔ refl (C .idn c)

def identity_adjunction_counit (C : WildPrecat) (d : C .ob)
  : Id (C .hom d d) (adjunction_counit C C (functor_identity C) (identity_right_adjoint C) d) (C .idn d)
  ≔ refl (C .idn d)
