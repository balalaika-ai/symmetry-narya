export "624-adjunctions-via-representability"
export "626-path-functor-categories"
export "628-adjunction-hom-bifunctors"

{` Chapter 6 (cats.tex), ex:repr-functors and running-text claims of
   sections 6.4-6.6 handled by this part (lines 720-933, 1027-1099). This
   module also collects modules 620-628. `}

{` Text before ex:repr-functors: a contravariant functor F : C^op → D
   sends f : c → c' to F(f) : F(c') → F(c). `}
def contravariant_functor_action (C D : WildPrecat) (F : WildFunctor (OppositeWild C) D) (c c' : C .ob)
  (f : C .hom c c') : D .hom (F .obj c') (F .obj c)
  ≔ F .mor c' c f

{` ex:repr-functors: k_c = Hom(c, -) acts by postcomposition and
   h_c = Hom(-, c) by precomposition (on the nose). `}
def covariant_representable_action (C : WildPrecat) (c x y : C .ob) (g : C .hom x y) (k : C .hom c x)
  : Id (C .hom c y) (covariant_representable C c .mor x y g k) (C .comp c x y g k)
  ≔ refl (C .comp c x y g k)

def contravariant_representable_action (C : WildPrecat) (c x y : C .ob) (g : C .hom x y) (k : C .hom y c)
  : Id (C .hom x c) (contravariant_functor_action C TypeWild (contravariant_representable C c) x y g k)
      (C .comp x y c k g)
  ≔ refl (C .comp x y c k g)

{` Litmus in Set: k_Bool(not)(id) = not, and h_Bool(not)(const true) is
   const true. `}
def covariant_representable_set_litmus
  : Id Bool (covariant_representable SetWild set_cat_bool .mor set_cat_bool set_cat_bool bool_not (x ↦ x) true.)
      false.
  ≔ refl (false. : Bool)

def contravariant_representable_set_litmus
  : Id Bool (contravariant_representable SetWild set_cat_bool .mor set_cat_bool set_cat_bool bool_not (_ ↦ true.)
      false.) true.
  ≔ refl (true. : Bool)

{` Litmus on a path category: the covariant representable of PathWild X
   at x sends y to the type of paths x = y. `}
def covariant_representable_paths (X : Type) (x y : X)
  : Id Type (covariant_representable (PathWild X) x .obj y) (Id X x y)
  ≔ refl (Id X x y)

{` Text after def:adjunction: "the essence of an adjunction is the
   ability to transpose" between F(c) → d and c → G(d). `}
def adjunction_transposition (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) : BookEquiv (D .hom (F .obj c) d) (C .hom c (R .right .obj d))
  ≔ book_equivalence (D .hom (F .obj c) d) (C .hom c (R .right .obj d)) (adjunction_transpose_equiv C D F R c d)

{` Footnote to xca:adj-from-triangles: for a functor defined on a
   category, the data of a right adjoint is a proposition; in particular
   any two right adjoints have identified right functors. `}
def right_adjoints_agree (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (R R' : RightAdjointData (C .wild) D F)
  : Id (WildFunctor D (C .wild)) (R .right) (R' .right)
  ≔ refl ((S ↦ S .right) : RightAdjointData (C .wild) D F → WildFunctor D (C .wild))
      (right_adjoint_data_prop C D F R R')

{` Litmus for cor:adj-unique: the identity functor of Set has, up to
   identification, only the identity right adjoint. `}
def set_identity_right_adjoint_unique (R : RightAdjointData SetWild SetWild (functor_identity SetWild))
  : Id (RightAdjointData SetWild SetWild (functor_identity SetWild)) R (identity_right_adjoint SetWild)
  ≔ right_adjoint_data_prop SetCat SetWild (functor_identity SetWild) R (identity_right_adjoint SetWild)

{` Litmus for lem:adj-via-repr: for the identity functor of Set with
   G0 = id and identity representing isomorphisms, the unique extension
   acts on arrows by g ↦ g (computed by reflexivity at not). `}
def set_identity_representing_data
  : AdjRepresentingData set_precat SetWild (functor_identity SetWild) (d ↦ d)
  ≔ d ↦ ((component ≔ c k ↦ k,
          natural ≔ c c' f ↦ refl ((k ↦ SetWild .comp c' c d k f) : SetWild .hom c d → SetWild .hom c' d)),
         c ↦ cat_identity_is_iso TypeWild (SetWild .hom c d))

def set_identity_extension_litmus
  : Id (Bool → Bool)
      (adjunction_via_representability set_precat SetWild (functor_identity SetWild) (d ↦ d)
        set_identity_representing_data .center .fst set_cat_bool set_cat_bool bool_not)
      bool_not
  ≔ refl bool_not
