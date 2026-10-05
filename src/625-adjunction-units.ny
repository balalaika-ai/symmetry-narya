export "620-natural-isomorphisms"

{` Chapter 6 (cats.tex), section 6.5: unit and counit of an adjunction
   (eq:adj-unit-counit), the triangle laws (xca:adj-triangles) and the
   converse construction from unit, counit and triangle laws
   (xca:adj-from-triangles). All in wild precategories. `}

{` Injectivity of the transposition α (it has a retraction). `}
def adjunction_transpose_injective (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (x y : D .hom (F .obj c) d)
  (q : Id (C .hom c (R .right .obj d)) (R .transpose c d x) (R .transpose c d y))
  : Id (D .hom (F .obj c) d) x y
  ≔ let r ≔ R .transpose_iso c d .snd .fst in
    concat (D .hom (F .obj c) d) x (r (R .transpose c d x)) y
      (inverse (D .hom (F .obj c) d) (r (R .transpose c d x)) x (R .transpose_iso c d .snd .snd (refl x)))
      (concat (D .hom (F .obj c) d) (r (R .transpose c d x)) (r (R .transpose c d y)) y
        (refl r q) (R .transpose_iso c d .snd .snd (refl y)))

{` Pointwise forms of the two naturality laws of α. `}
def adjunction_natural_left_at (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c c' : C .ob) (f : C .hom c' c) (d : D .ob) (k : D .hom (F .obj c) d)
  : Id (C .hom c' (R .right .obj d)) (C .comp c' c (R .right .obj d) (R .transpose c d k) f)
      (R .transpose c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
  ≔ happly (D .hom (F .obj c) d) (_ ↦ C .hom c' (R .right .obj d))
      (k ↦ C .comp c' c (R .right .obj d) (R .transpose c d k) f)
      (k ↦ R .transpose c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
      (R .natural_left c c' f d) k

def adjunction_natural_right_at (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d d' : D .ob) (g : D .hom d d') (k : D .hom (F .obj c) d)
  : Id (C .hom c (R .right .obj d'))
      (C .comp c (R .right .obj d) (R .right .obj d') (R .right .mor d d' g) (R .transpose c d k))
      (R .transpose c d' (D .comp (F .obj c) d d' g k))
  ≔ happly (D .hom (F .obj c) d) (_ ↦ C .hom c (R .right .obj d'))
      (k ↦ C .comp c (R .right .obj d) (R .right .obj d') (R .right .mor d d' g) (R .transpose c d k))
      (k ↦ R .transpose c d' (D .comp (F .obj c) d d' g k))
      (R .natural_right c d d' g) k

{` eq:adj-unit-counit: the unit η : id_C → GF is natural. `}
def adjunction_unit_natural (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (a b : C .ob) (f : C .hom a b)
  : Id (C .hom a (R .right .obj (F .obj b)))
      (C .comp a (R .right .obj (F .obj a)) (R .right .obj (F .obj b))
        (R .right .mor (F .obj a) (F .obj b) (F .mor a b f)) (adjunction_unit C D F R a))
      (C .comp a b (R .right .obj (F .obj b)) (adjunction_unit C D F R b) f)
  ≔ let Fa ≔ F .obj a in let Fb ≔ F .obj b in let Ff ≔ F .mor a b f in
    calc
      C .comp a (R .right .obj Fa) (R .right .obj Fb) (R .right .mor Fa Fb Ff) (R .transpose a Fa (D .idn Fa))
      = R .transpose a Fb (D .comp Fa Fa Fb Ff (D .idn Fa))
        by adjunction_natural_right_at C D F R a Fa Fb Ff (D .idn Fa)
      = R .transpose a Fb Ff
        by refl (R .transpose a Fb) (D .ru Fa Fb Ff)
      = R .transpose a Fb (D .comp Fa Fb Fb (D .idn Fb) Ff)
        by refl (R .transpose a Fb) (inverse (D .hom Fa Fb) (D .comp Fa Fb Fb (D .idn Fb) Ff) Ff (D .lu Fa Fb Ff))
      = C .comp a b (R .right .obj Fb) (R .transpose b Fb (D .idn Fb)) f
        by inverse (C .hom a (R .right .obj Fb)) (C .comp a b (R .right .obj Fb) (R .transpose b Fb (D .idn Fb)) f)
             (R .transpose a Fb (D .comp Fa Fb Fb (D .idn Fb) Ff))
             (adjunction_natural_left_at C D F R b a f Fb (D .idn Fb)) ∎

def adjunction_unit_nat_trans (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : WildNatTrans C C (functor_identity C) (functor_compose C D C (R .right) F)
  ≔ (component ≔ adjunction_unit C D F R,
     natural ≔ adjunction_unit_natural C D F R)

{` α(ε_d) = id_{G d} (the section law at the identity). `}
def adjunction_counit_transpose (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) (d : D .ob)
  : Id (C .hom (R .right .obj d) (R .right .obj d))
      (R .transpose (R .right .obj d) d (adjunction_counit C D F R d)) (C .idn (R .right .obj d))
  ≔ adjunction_untranspose_section C D F R (R .right .obj d) d (C .idn (R .right .obj d))

{` eq:adj-unit-counit: the counit ε : FG → id_D is natural. Both sides
   transpose to G(g). `}
def adjunction_counit_natural (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (d d' : D .ob) (g : D .hom d d')
  : Id (D .hom (F .obj (R .right .obj d)) d')
      (D .comp (F .obj (R .right .obj d)) d d' g (adjunction_counit C D F R d))
      (D .comp (F .obj (R .right .obj d)) (F .obj (R .right .obj d')) d' (adjunction_counit C D F R d')
        (F .mor (R .right .obj d) (R .right .obj d') (R .right .mor d d' g)))
  ≔ let G ≔ R .right in
    let Gd ≔ G .obj d in let Gd' ≔ G .obj d' in let Gg ≔ G .mor d d' g in
    let e ≔ adjunction_counit C D F R d in let e' ≔ adjunction_counit C D F R d' in
    adjunction_transpose_injective C D F R Gd d'
      (D .comp (F .obj Gd) d d' g e) (D .comp (F .obj Gd) (F .obj Gd') d' e' (F .mor Gd Gd' Gg))
      (calc
        R .transpose Gd d' (D .comp (F .obj Gd) d d' g e)
        = C .comp Gd Gd Gd' Gg (R .transpose Gd d e)
          by inverse (C .hom Gd Gd') (C .comp Gd Gd Gd' Gg (R .transpose Gd d e))
               (R .transpose Gd d' (D .comp (F .obj Gd) d d' g e))
               (adjunction_natural_right_at C D F R Gd d d' g e)
        = C .comp Gd Gd Gd' Gg (C .idn Gd)
          by cat_whisker_left C Gd Gd Gd' Gg (R .transpose Gd d e) (C .idn Gd)
               (adjunction_counit_transpose C D F R d)
        = Gg by C .ru Gd Gd' Gg
        = C .comp Gd Gd' Gd' (C .idn Gd') Gg
          by inverse (C .hom Gd Gd') (C .comp Gd Gd' Gd' (C .idn Gd') Gg) Gg (C .lu Gd Gd' Gg)
        = C .comp Gd Gd' Gd' (R .transpose Gd' d' e') Gg
          by cat_whisker_right C Gd Gd' Gd' (C .idn Gd') (R .transpose Gd' d' e') Gg
               (inverse (C .hom Gd' Gd') (R .transpose Gd' d' e') (C .idn Gd') (adjunction_counit_transpose C D F R d'))
        = R .transpose Gd d' (D .comp (F .obj Gd) (F .obj Gd') d' e' (F .mor Gd Gd' Gg))
          by adjunction_natural_left_at C D F R Gd' Gd Gg d' e' ∎)

def adjunction_counit_nat_trans (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : WildNatTrans D D (functor_compose D C D F (R .right)) (functor_identity D)
  ≔ (component ≔ adjunction_counit C D F R,
     natural ≔ adjunction_counit_natural C D F R)

{` xca:adj-triangles, first triangle: ε_{F c} ∘ F(η_c) = id_{F c}. `}
def adjunction_triangle_left (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) (c : C .ob)
  : Id (D .hom (F .obj c) (F .obj c))
      (D .comp (F .obj c) (F .obj (R .right .obj (F .obj c))) (F .obj c)
        (adjunction_counit C D F R (F .obj c)) (F .mor c (R .right .obj (F .obj c)) (adjunction_unit C D F R c)))
      (D .idn (F .obj c))
  ≔ let Fc ≔ F .obj c in let GFc ≔ R .right .obj Fc in
    let eta ≔ adjunction_unit C D F R c in let eps ≔ adjunction_counit C D F R Fc in
    adjunction_transpose_injective C D F R c Fc
      (D .comp Fc (F .obj GFc) Fc eps (F .mor c GFc eta)) (D .idn Fc)
      (calc
        R .transpose c Fc (D .comp Fc (F .obj GFc) Fc eps (F .mor c GFc eta))
        = C .comp c GFc GFc (R .transpose GFc Fc eps) eta
          by inverse (C .hom c GFc) (C .comp c GFc GFc (R .transpose GFc Fc eps) eta)
               (R .transpose c Fc (D .comp Fc (F .obj GFc) Fc eps (F .mor c GFc eta)))
               (adjunction_natural_left_at C D F R GFc c eta Fc eps)
        = C .comp c GFc GFc (C .idn GFc) eta
          by cat_whisker_right C c GFc GFc (R .transpose GFc Fc eps) (C .idn GFc) eta
               (adjunction_counit_transpose C D F R Fc)
        = eta by C .lu c GFc eta ∎)

{` xca:adj-triangles, second triangle: G(ε_d) ∘ η_{G d} = id_{G d}. `}
def adjunction_triangle_right (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) (d : D .ob)
  : Id (C .hom (R .right .obj d) (R .right .obj d))
      (C .comp (R .right .obj d) (R .right .obj (F .obj (R .right .obj d))) (R .right .obj d)
        (R .right .mor (F .obj (R .right .obj d)) d (adjunction_counit C D F R d))
        (adjunction_unit C D F R (R .right .obj d)))
      (C .idn (R .right .obj d))
  ≔ let Gd ≔ R .right .obj d in let FGd ≔ F .obj Gd in
    let eps ≔ adjunction_counit C D F R d in
    calc
      C .comp Gd (R .right .obj FGd) Gd (R .right .mor FGd d eps) (R .transpose Gd FGd (D .idn FGd))
      = R .transpose Gd d (D .comp FGd FGd d eps (D .idn FGd))
        by adjunction_natural_right_at C D F R Gd FGd d eps (D .idn FGd)
      = R .transpose Gd d eps
        by refl (R .transpose Gd d) (D .ru FGd d eps)
      = C .idn Gd by adjunction_counit_transpose C D F R d ∎

{` "Conversely ... we can recover α": α(f) = G(f) ∘ η_c. `}
def adjunction_transpose_via_unit (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (f : D .hom (F .obj c) d)
  : Id (C .hom c (R .right .obj d)) (R .transpose c d f)
      (C .comp c (R .right .obj (F .obj c)) (R .right .obj d) (R .right .mor (F .obj c) d f)
        (adjunction_unit C D F R c))
  ≔ concat (C .hom c (R .right .obj d)) (R .transpose c d f)
      (R .transpose c d (D .comp (F .obj c) (F .obj c) d f (D .idn (F .obj c))))
      (C .comp c (R .right .obj (F .obj c)) (R .right .obj d) (R .right .mor (F .obj c) d f)
        (adjunction_unit C D F R c))
      (refl (R .transpose c d)
        (inverse (D .hom (F .obj c) d) (D .comp (F .obj c) (F .obj c) d f (D .idn (F .obj c))) f
          (D .ru (F .obj c) d f)))
      (inverse (C .hom c (R .right .obj d))
        (C .comp c (R .right .obj (F .obj c)) (R .right .obj d) (R .right .mor (F .obj c) d f)
          (adjunction_unit C D F R c))
        (R .transpose c d (D .comp (F .obj c) (F .obj c) d f (D .idn (F .obj c))))
        (adjunction_natural_right_at C D F R c (F .obj c) d f (D .idn (F .obj c))))

{` xca:adj-from-triangles. The data: functors F, G, natural η, ε and
   the two triangle laws. `}
def UnitCounitAdjunction (C D : WildPrecat) (F : WildFunctor C D) : Type ≔ sig (
  right : WildFunctor D C,
  unit : WildNatTrans C C (functor_identity C) (functor_compose C D C right F),
  counit : WildNatTrans D D (functor_compose D C D F right) (functor_identity D),
  triangle_left : (c : C .ob)
    → Id (D .hom (F .obj c) (F .obj c))
        (D .comp (F .obj c) (F .obj (right .obj (F .obj c))) (F .obj c)
          (counit .component (F .obj c)) (F .mor c (right .obj (F .obj c)) (unit .component c)))
        (D .idn (F .obj c)),
  triangle_right : (d : D .ob)
    → Id (C .hom (right .obj d) (right .obj d))
        (C .comp (right .obj d) (right .obj (F .obj (right .obj d))) (right .obj d)
          (right .mor (F .obj (right .obj d)) d (counit .component d)) (unit .component (right .obj d)))
        (C .idn (right .obj d)) )

{` From an adjunction to unit, counit and triangle laws. `}
def unit_counit_of_adjunction (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : UnitCounitAdjunction C D F
  ≔ (right ≔ R .right,
     unit ≔ adjunction_unit_nat_trans C D F R,
     counit ≔ adjunction_counit_nat_trans C D F R,
     triangle_left ≔ adjunction_triangle_left C D F R,
     triangle_right ≔ adjunction_triangle_right C D F R)

{` The transposition α(f) = G(f) ∘ η_c and its candidate inverse
   β(m) = ε_d ∘ F(m). `}
def triangle_transpose (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (c : C .ob) (d : D .ob) (f : D .hom (F .obj c) d) : C .hom c (T .right .obj d)
  ≔ C .comp c (T .right .obj (F .obj c)) (T .right .obj d) (T .right .mor (F .obj c) d f) (T .unit .component c)

def triangle_untranspose (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (c : C .ob) (d : D .ob) (m : C .hom c (T .right .obj d)) : D .hom (F .obj c) d
  ≔ D .comp (F .obj c) (F .obj (T .right .obj d)) d (T .counit .component d) (F .mor c (T .right .obj d) m)

def triangle_transpose_section (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (c : C .ob) (d : D .ob) (m : C .hom c (T .right .obj d))
  : Id (C .hom c (T .right .obj d)) (triangle_transpose C D F T c d (triangle_untranspose C D F T c d m)) m
  ≔ let G ≔ T .right in let Gd ≔ G .obj d in let Fc ≔ F .obj c in let GFc ≔ G .obj Fc in
    let FGd ≔ F .obj Gd in let GFGd ≔ G .obj FGd in
    let eta ≔ T .unit .component in let eps ≔ T .counit .component d in
    let Fm ≔ F .mor c Gd m in
    calc
      C .comp c GFc Gd (G .mor Fc d (D .comp Fc FGd d eps Fm)) (eta c)
      = C .comp c GFc Gd (C .comp GFc GFGd Gd (G .mor FGd d eps) (G .mor Fc FGd Fm)) (eta c)
        by cat_whisker_right C c GFc Gd (G .mor Fc d (D .comp Fc FGd d eps Fm))
             (C .comp GFc GFGd Gd (G .mor FGd d eps) (G .mor Fc FGd Fm)) (eta c)
             (G .map_comp Fc FGd d Fm eps)
      = C .comp c GFGd Gd (G .mor FGd d eps) (C .comp c GFc GFGd (G .mor Fc FGd Fm) (eta c))
        by inverse (C .hom c Gd) (C .comp c GFGd Gd (G .mor FGd d eps) (C .comp c GFc GFGd (G .mor Fc FGd Fm) (eta c)))
             (C .comp c GFc Gd (C .comp GFc GFGd Gd (G .mor FGd d eps) (G .mor Fc FGd Fm)) (eta c))
             (C .assoc c GFc GFGd Gd (eta c) (G .mor Fc FGd Fm) (G .mor FGd d eps))
      = C .comp c GFGd Gd (G .mor FGd d eps) (C .comp c Gd GFGd (eta Gd) m)
        by cat_whisker_left C c GFGd Gd (G .mor FGd d eps) (C .comp c GFc GFGd (G .mor Fc FGd Fm) (eta c))
             (C .comp c Gd GFGd (eta Gd) m) (T .unit .natural c Gd m)
      = C .comp c Gd Gd (C .comp Gd GFGd Gd (G .mor FGd d eps) (eta Gd)) m
        by C .assoc c Gd GFGd Gd m (eta Gd) (G .mor FGd d eps)
      = C .comp c Gd Gd (C .idn Gd) m
        by cat_whisker_right C c Gd Gd (C .comp Gd GFGd Gd (G .mor FGd d eps) (eta Gd)) (C .idn Gd) m
             (T .triangle_right d)
      = m by C .lu c Gd m ∎

def triangle_transpose_retraction (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (c : C .ob) (d : D .ob) (f : D .hom (F .obj c) d)
  : Id (D .hom (F .obj c) d) (triangle_untranspose C D F T c d (triangle_transpose C D F T c d f)) f
  ≔ let G ≔ T .right in let Gd ≔ G .obj d in let Fc ≔ F .obj c in let GFc ≔ G .obj Fc in
    let FGd ≔ F .obj Gd in let FGFc ≔ F .obj GFc in
    let etac ≔ T .unit .component c in let eps ≔ T .counit .component in
    let Gf ≔ G .mor Fc d f in
    calc
      D .comp Fc FGd d (eps d) (F .mor c Gd (C .comp c GFc Gd Gf etac))
      = D .comp Fc FGd d (eps d) (D .comp Fc FGFc FGd (F .mor GFc Gd Gf) (F .mor c GFc etac))
        by cat_whisker_left D Fc FGd d (eps d) (F .mor c Gd (C .comp c GFc Gd Gf etac))
             (D .comp Fc FGFc FGd (F .mor GFc Gd Gf) (F .mor c GFc etac)) (F .map_comp c GFc Gd etac Gf)
      = D .comp Fc FGFc d (D .comp FGFc FGd d (eps d) (F .mor GFc Gd Gf)) (F .mor c GFc etac)
        by D .assoc Fc FGFc FGd d (F .mor c GFc etac) (F .mor GFc Gd Gf) (eps d)
      = D .comp Fc FGFc d (D .comp FGFc Fc d f (eps Fc)) (F .mor c GFc etac)
        by cat_whisker_right D Fc FGFc d (D .comp FGFc FGd d (eps d) (F .mor GFc Gd Gf))
             (D .comp FGFc Fc d f (eps Fc)) (F .mor c GFc etac)
             (inverse (D .hom FGFc d) (D .comp FGFc Fc d f (eps Fc)) (D .comp FGFc FGd d (eps d) (F .mor GFc Gd Gf))
               (T .counit .natural Fc d f))
      = D .comp Fc Fc d f (D .comp Fc FGFc Fc (eps Fc) (F .mor c GFc etac))
        by inverse (D .hom Fc d) (D .comp Fc Fc d f (D .comp Fc FGFc Fc (eps Fc) (F .mor c GFc etac)))
             (D .comp Fc FGFc d (D .comp FGFc Fc d f (eps Fc)) (F .mor c GFc etac))
             (D .assoc Fc FGFc Fc d (F .mor c GFc etac) (eps Fc) f)
      = D .comp Fc Fc d f (D .idn Fc)
        by cat_whisker_left D Fc Fc d f (D .comp Fc FGFc Fc (eps Fc) (F .mor c GFc etac)) (D .idn Fc)
             (T .triangle_left c)
      = f by D .ru Fc d f ∎

{` xca:adj-from-triangles: α thus defined is a natural isomorphism, so
   F ⊣ G. `}
def adjunction_from_triangles (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  : RightAdjointData C D F
  ≔ let G ≔ T .right in
    (right ≔ G,
     transpose ≔ triangle_transpose C D F T,
     transpose_iso ≔ c d ↦
       ((triangle_untranspose C D F T c d,
         funext (C .hom c (G .obj d)) (_ ↦ C .hom c (G .obj d))
           (m ↦ triangle_transpose C D F T c d (triangle_untranspose C D F T c d m)) (m ↦ m)
           (triangle_transpose_section C D F T c d)),
        (triangle_untranspose C D F T c d,
         funext (D .hom (F .obj c) d) (_ ↦ D .hom (F .obj c) d)
           (f ↦ triangle_untranspose C D F T c d (triangle_transpose C D F T c d f)) (f ↦ f)
           (triangle_transpose_retraction C D F T c d))),
     natural_left ≔ c c' f d ↦
       funext (D .hom (F .obj c) d) (_ ↦ C .hom c' (G .obj d))
         (k ↦ C .comp c' c (G .obj d) (triangle_transpose C D F T c d k) f)
         (k ↦ triangle_transpose C D F T c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
         (k ↦
           let Fc ≔ F .obj c in let Fc' ≔ F .obj c' in let GFc ≔ G .obj Fc in let GFc' ≔ G .obj Fc' in
           let Gd ≔ G .obj d in let eta ≔ T .unit .component in let Ff ≔ F .mor c' c f in
           calc
             C .comp c' c Gd (C .comp c GFc Gd (G .mor Fc d k) (eta c)) f
             = C .comp c' GFc Gd (G .mor Fc d k) (C .comp c' c GFc (eta c) f)
               by inverse (C .hom c' Gd) (C .comp c' GFc Gd (G .mor Fc d k) (C .comp c' c GFc (eta c) f))
                    (C .comp c' c Gd (C .comp c GFc Gd (G .mor Fc d k) (eta c)) f)
                    (C .assoc c' c GFc Gd f (eta c) (G .mor Fc d k))
             = C .comp c' GFc Gd (G .mor Fc d k) (C .comp c' GFc' GFc (G .mor Fc' Fc Ff) (eta c'))
               by cat_whisker_left C c' GFc Gd (G .mor Fc d k) (C .comp c' c GFc (eta c) f)
                    (C .comp c' GFc' GFc (G .mor Fc' Fc Ff) (eta c'))
                    (inverse (C .hom c' GFc) (C .comp c' GFc' GFc (G .mor Fc' Fc Ff) (eta c'))
                      (C .comp c' c GFc (eta c) f) (T .unit .natural c' c f))
             = C .comp c' GFc' Gd (C .comp GFc' GFc Gd (G .mor Fc d k) (G .mor Fc' Fc Ff)) (eta c')
               by C .assoc c' GFc' GFc Gd (eta c') (G .mor Fc' Fc Ff) (G .mor Fc d k)
             = C .comp c' GFc' Gd (G .mor Fc' d (D .comp Fc' Fc d k Ff)) (eta c')
               by cat_whisker_right C c' GFc' Gd (C .comp GFc' GFc Gd (G .mor Fc d k) (G .mor Fc' Fc Ff))
                    (G .mor Fc' d (D .comp Fc' Fc d k Ff)) (eta c')
                    (inverse (C .hom GFc' Gd) (G .mor Fc' d (D .comp Fc' Fc d k Ff))
                      (C .comp GFc' GFc Gd (G .mor Fc d k) (G .mor Fc' Fc Ff)) (G .map_comp Fc' Fc d Ff k)) ∎),
     natural_right ≔ c d d' g ↦
       funext (D .hom (F .obj c) d) (_ ↦ C .hom c (G .obj d'))
         (k ↦ C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (triangle_transpose C D F T c d k))
         (k ↦ triangle_transpose C D F T c d' (D .comp (F .obj c) d d' g k))
         (k ↦
           let Fc ≔ F .obj c in let GFc ≔ G .obj Fc in let Gd ≔ G .obj d in let Gd' ≔ G .obj d' in
           let etac ≔ T .unit .component c in
           calc
             C .comp c Gd Gd' (G .mor d d' g) (C .comp c GFc Gd (G .mor Fc d k) etac)
             = C .comp c GFc Gd' (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k)) etac
               by C .assoc c GFc Gd Gd' etac (G .mor Fc d k) (G .mor d d' g)
             = C .comp c GFc Gd' (G .mor Fc d' (D .comp Fc d d' g k)) etac
               by cat_whisker_right C c GFc Gd' (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k))
                    (G .mor Fc d' (D .comp Fc d d' g k)) etac
                    (inverse (C .hom GFc Gd') (G .mor Fc d' (D .comp Fc d d' g k))
                      (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k)) (G .map_comp Fc d d' k g)) ∎))

{` Going back and forth (footnote to xca:adj-from-triangles): the
   adjunction built from (G, η, ε) has unit η and counit ε, and the
   transposition rebuilt from an adjunction's own unit agrees with α. `}
def adjunction_from_triangles_unit (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (c : C .ob)
  : Id (C .hom c (T .right .obj (F .obj c)))
      (adjunction_unit C D F (adjunction_from_triangles C D F T) c) (T .unit .component c)
  ≔ let G ≔ T .right in let Fc ≔ F .obj c in let GFc ≔ G .obj Fc in
    concat (C .hom c GFc) (C .comp c GFc GFc (G .mor Fc Fc (D .idn Fc)) (T .unit .component c))
      (C .comp c GFc GFc (C .idn GFc) (T .unit .component c)) (T .unit .component c)
      (cat_whisker_right C c GFc GFc (G .mor Fc Fc (D .idn Fc)) (C .idn GFc) (T .unit .component c) (G .map_id Fc))
      (C .lu c GFc (T .unit .component c))

def adjunction_from_triangles_counit (C D : WildPrecat) (F : WildFunctor C D) (T : UnitCounitAdjunction C D F)
  (d : D .ob)
  : Id (D .hom (F .obj (T .right .obj d)) d)
      (adjunction_counit C D F (adjunction_from_triangles C D F T) d) (T .counit .component d)
  ≔ let Gd ≔ T .right .obj d in let FGd ≔ F .obj Gd in
    concat (D .hom FGd d) (D .comp FGd FGd d (T .counit .component d) (F .mor Gd Gd (C .idn Gd)))
      (D .comp FGd FGd d (T .counit .component d) (D .idn FGd)) (T .counit .component d)
      (cat_whisker_left D FGd FGd d (T .counit .component d) (F .mor Gd Gd (C .idn Gd)) (D .idn FGd) (F .map_id Gd))
      (D .ru FGd d (T .counit .component d))

def adjunction_round_trip_transpose (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (f : D .hom (F .obj c) d)
  : Id (C .hom c (R .right .obj d))
      (adjunction_from_triangles C D F (unit_counit_of_adjunction C D F R) .transpose c d f) (R .transpose c d f)
  ≔ inverse (C .hom c (R .right .obj d)) (R .transpose c d f)
      (adjunction_from_triangles C D F (unit_counit_of_adjunction C D F R) .transpose c d f)
      (adjunction_transpose_via_unit C D F R c d f)

{` Litmus: the identity adjunction id ⊣ id; its unit and counit are the
   identities, and the triangle-built transposition of the identity
   functor at k : c → d is k ∘ id = k up to ρ. `}
def identity_unit_counit_adjunction (C : WildPrecat) : UnitCounitAdjunction C C (functor_identity C)
  ≔ unit_counit_of_adjunction C C (functor_identity C) (identity_right_adjoint C)

def identity_unit_counit_unit (C : WildPrecat) (c : C .ob)
  : Id (C .hom c c) (identity_unit_counit_adjunction C .unit .component c) (C .idn c)
  ≔ refl (C .idn c)

def identity_triangle_transpose (C : WildPrecat) (c d : C .ob) (k : C .hom c d)
  : Id (C .hom c d)
      (adjunction_from_triangles C C (functor_identity C) (identity_unit_counit_adjunction C) .transpose c d k)
      (C .comp c c d k (C .idn c))
  ≔ refl (C .comp c c d k (C .idn c))

{` Litmus in Set: for the identity adjunction on Set, the triangle-built
   transposition of not is not. `}
def set_identity_triangle_transpose
  : Id (Bool → Bool)
      (adjunction_from_triangles SetWild SetWild (functor_identity SetWild) (identity_unit_counit_adjunction SetWild)
        .transpose set_cat_bool set_cat_bool bool_not)
      bool_not
  ≔ refl bool_not
