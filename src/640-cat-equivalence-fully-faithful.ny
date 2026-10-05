export "603-adjunctions-and-equivalences"

{` Chapter 6, section 6.7 (equivalences of categories), part 1:
   lem:cat-equiv-ff (equivalences are fully faithful) and the prose claim
   after lem:cat-equiv-is-prop (AKS 2015, Lemma 6.2): a functor G with
   natural isomorphisms id ≅ GF and FG ≅ id makes F an equivalence.
   Everything here holds for wild precategories. `}

{` Generalities on equivalences of types. `}
def ch6c_equiv_inverse_path (A B : Type) (e : Equiv A B) (a : A) (b : B) (p : Id B (e .map a) b)
  : Id A (equiv_inverse_map A B e b) a
  ≔ concat A (equiv_inverse_map A B e b) (equiv_inverse_map A B e (e .map a)) a
      (refl (equiv_inverse_map A B e) (inverse B (e .map a) b p))
      (equiv_retraction A B e a)

{` The 2-out-of-6 property: if g ∘ f and h ∘ g are equivalences, then so
   is g (it has a section and a retraction). `}
def ch6c_two_out_of_six (A B X Y : Type) (f : A → B) (g : B → X) (h : X → Y)
  (gf : isEquiv A X (x ↦ g (f x))) (hg : isEquiv B Y (y ↦ h (g y))) : isEquiv B X g
  ≔ let e1 : Equiv A X ≔ (x ↦ g (f x), gf) in
    let e2 : Equiv B Y ≔ (y ↦ h (g y), hg) in
    let bi : Equiv B X ≔ biinvertible_equiv B X g
      (c ↦ f (equiv_inverse_map A X e1 c)) (c ↦ equiv_counit A X e1 c)
      (c ↦ equiv_inverse_map B Y e2 (h c)) (b ↦ equiv_retraction B Y e2 b) in
    bi .equiv

{` 2-out-of-3: if h ∘ f is homotopic to an equivalence g and h is an
   equivalence, then f is an equivalence. `}
def ch6c_two_out_of_three_left (A B X : Type) (f : A → B) (g : A → X) (h : B → X)
  (e : (a : A) → Id X (h (f a)) (g a)) (hg : isEquiv A X g) (hh : isEquiv B X h) : isEquiv A B f
  ≔ let he : Equiv B X ≔ (h, hh) in
    let res : Equiv A B ≔ equiv_change_map A B (compose_equiv A X B (g, hg) (canonical_inverse_equiv B X he)) f
      (a ↦ concat B (equiv_inverse_map B X he (g a)) (equiv_inverse_map B X he (h (f a))) (f a)
         (refl (equiv_inverse_map B X he) (inverse X (h (f a)) (g a) (e a)))
         (equiv_retraction B X he (f a))) in
    res .equiv

{` Isomorphisms. Being an isomorphism is transported along
   identifications of arrows. `}
def cat_is_iso_transport (C : WildPrecat) (a b : C .ob) (f g : C .hom a b) (p : Id (C .hom a b) f g)
  (i : CatIsIso C a b f) : CatIsIso C a b g
  ≔ transport (C .hom a b) (CatIsIso C a b) f g p i

{` A left inverse of an isomorphism is an isomorphism: if f is an
   isomorphism and g ∘ f = id, then g is an isomorphism (inverse f). `}
def cat_left_inverse_is_iso (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (g : C .hom b a) (p : Id (C .hom a a) (C .comp a b a g f) (C .idn a)) : CatIsIso C b a g
  ≔ let f' ≔ i .fst .fst in
    let fg ≔ C .comp b a b f g in
    ((f, p),
     (f, calc
        C .comp b a b f g
        = C .comp b b b fg (C .idn b)
          by inverse (C .hom b b) (C .comp b b b fg (C .idn b)) fg (C .ru b b fg)
        = C .comp b b b fg (C .comp b a b f f')
          by cat_whisker_left C b b b fg (C .idn b) (C .comp b a b f f')
               (inverse (C .hom b b) (C .comp b a b f f') (C .idn b) (i .fst .snd))
        = C .comp b a b (C .comp a b b fg f) f'
          by C .assoc b a b b f' f fg
        = C .comp b a b (C .comp a a b f (C .comp a b a g f)) f'
          by cat_whisker_right C b a b (C .comp a b b fg f) (C .comp a a b f (C .comp a b a g f)) f'
               (inverse (C .hom a b) (C .comp a a b f (C .comp a b a g f)) (C .comp a b b fg f)
                 (C .assoc a b a b f g f))
        = C .comp b a b (C .comp a a b f (C .idn a)) f'
          by cat_whisker_right C b a b (C .comp a a b f (C .comp a b a g f)) (C .comp a a b f (C .idn a)) f'
               (cat_whisker_left C a a b f (C .comp a b a g f) (C .idn a) p)
        = C .comp b a b f f'
          by cat_whisker_right C b a b (C .comp a a b f (C .idn a)) f f' (C .ru a b f)
        = C .idn b by i .fst .snd ∎))

{` A functor whose actions on arrows are equivalences reflects
   isomorphisms. `}
def mor_equiv_functor_reflects_iso (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  (a b : C .ob) (k : C .hom a b) (i : CatIsIso D (F .obj a) (F .obj b) (F .mor a b k)) : CatIsIso C a b k
  ≔ let Fa ≔ F .obj a in
    let Fb ≔ F .obj b in
    let e_ba : Equiv (C .hom b a) (D .hom (F .obj b) (F .obj a)) ≔ (F .mor b a, hF b a) in
    let m ≔ i .fst .fst in
    let m' ≔ i .snd .fst in
    let k1 ≔ equiv_inverse_map (C .hom b a) (D .hom Fb Fa) e_ba m in
    let k2 ≔ equiv_inverse_map (C .hom b a) (D .hom Fb Fa) e_ba m' in
    ((k1, equivalence_injective (C .hom b b) (D .hom Fb Fb) (F .mor b b, hF b b) (C .comp b a b k k1) (C .idn b)
        (calc
          F .mor b b (C .comp b a b k k1)
          = D .comp Fb Fa Fb (F .mor a b k) (F .mor b a k1) by F .map_comp b a b k1 k
          = D .comp Fb Fa Fb (F .mor a b k) m
            by cat_whisker_left D Fb Fa Fb (F .mor a b k) (F .mor b a k1) m
                 (equiv_counit (C .hom b a) (D .hom Fb Fa) e_ba m)
          = D .idn Fb by i .fst .snd
          = F .mor b b (C .idn b) by inverse (D .hom Fb Fb) (F .mor b b (C .idn b)) (D .idn Fb) (F .map_id b) ∎)),
     (k2, equivalence_injective (C .hom a a) (D .hom Fa Fa) (F .mor a a, hF a a) (C .comp a b a k2 k) (C .idn a)
        (calc
          F .mor a a (C .comp a b a k2 k)
          = D .comp Fa Fb Fa (F .mor b a k2) (F .mor a b k) by F .map_comp a b a k k2
          = D .comp Fa Fb Fa m' (F .mor a b k)
            by cat_whisker_right D Fa Fb Fa (F .mor b a k2) m' (F .mor a b k)
                 (equiv_counit (C .hom b a) (D .hom Fb Fa) e_ba m')
          = D .idn Fa by i .snd .snd
          = F .mor a a (C .idn a) by inverse (D .hom Fa Fa) (F .mor a a (C .idn a)) (D .idn Fa) (F .map_id a) ∎)))

{` Fully faithful functors in the native convention: every action on
   arrows is an equivalence. `}
def ff_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (h : IsFullyFaithful C D F) (a b : C .ob)
  : isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)
  ≔ native_equivalence (C .hom a b) (D .hom (F .obj a) (F .obj b)) (fully_faithful_equiv C D F h a b) .equiv

def ff_from_mor_equivs (C D : WildPrecat) (F : WildFunctor C D)
  (h : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  : IsFullyFaithful C D F
  ≔ fully_faithful_from_equivs C D F (a b ↦
      book_equivalence (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b, h a b) .equiv)

{` lem:cat-equiv-ff. The transpose of F(f) is η_b ∘ f (naturality of the
   transposition in the first variable and λ). `}
def adjunction_transpose_of_image (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (a b : C .ob) (f : C .hom a b)
  : Id (C .hom a (R .right .obj (F .obj b)))
      (C .comp a b (R .right .obj (F .obj b)) (adjunction_unit C D F R b) f)
      (R .transpose a (F .obj b) (F .mor a b f))
  ≔ concat (C .hom a (R .right .obj (F .obj b)))
      (C .comp a b (R .right .obj (F .obj b)) (adjunction_unit C D F R b) f)
      (R .transpose a (F .obj b) (D .comp (F .obj a) (F .obj b) (F .obj b) (D .idn (F .obj b)) (F .mor a b f)))
      (R .transpose a (F .obj b) (F .mor a b f))
      (R .natural_left b a f (F .obj b) (refl (D .idn (F .obj b))))
      (refl (R .transpose a (F .obj b)) (D .lu (F .obj a) (F .obj b) (F .mor a b f)))

{` If F is a left adjoint whose unit is an isomorphism, then F is fully
   faithful: transpose ∘ F(-) = η_b ∘ -, and both η_b ∘ - and the
   transposition are equivalences. Only the unit is used. `}
def left_adjoint_unit_iso_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (u : (c : C .ob) → CatIsIso C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c)) (a b : C .ob)
  : isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)
  ≔ let GFb ≔ R .right .obj (F .obj b) in
    ch6c_two_out_of_three_left (C .hom a b) (D .hom (F .obj a) (F .obj b)) (C .hom a GFb)
      (F .mor a b) (f ↦ C .comp a b GFb (adjunction_unit C D F R b) f) (R .transpose a (F .obj b))
      (f ↦ inverse (C .hom a GFb) (C .comp a b GFb (adjunction_unit C D F R b) f)
          (R .transpose a (F .obj b) (F .mor a b f)) (adjunction_transpose_of_image C D F R a b f))
      (cat_postcompose_equiv C b GFb (adjunction_unit C D F R b) (u b) a .equiv)
      (adjunction_transpose_equiv C D F R a (F .obj b) .equiv)

def cat_equivalence_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (E : IsCatEquivalence C D F)
  (a b : C .ob) : isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)
  ≔ left_adjoint_unit_iso_mor_is_equiv C D F (E .fst) (E .snd .fst) a b

def wild_cat_equivalence_ff (C D : WildPrecat) (F : WildFunctor C D) (E : IsCatEquivalence C D F)
  : IsFullyFaithful C D F
  ≔ ff_from_mor_equivs C D F (cat_equivalence_mor_is_equiv C D F E)

{` lem:cat-equiv-ff: "Any equivalence of precategories is fully
   faithful" (the proof above works for wild precategories). `}
def cat_equivalence_ff (C D : Precat) (F : WildFunctor (C .wild) (D .wild))
  (E : IsCatEquivalence (C .wild) (D .wild) F) : IsFullyFaithful (C .wild) (D .wild) F
  ≔ wild_cat_equivalence_ff (C .wild) (D .wild) F E

{` AKS 2015, Lemma 6.2 (the claim after lem:cat-equiv-is-prop): from a
   functor G : D → C and natural isomorphisms η : id_C ≅ GF and
   ε : FG ≅ id_D we obtain an adjunction F ⊣ G with transposition
   k ↦ G(k) ∘ η_c, whose unit and counit are isomorphisms. `}
def nat_iso_unit_double_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F)) (a b : C .ob)
  : isEquiv (C .hom a b) (C .hom (G .obj (F .obj a)) (G .obj (F .obj b)))
      (f ↦ G .mor (F .obj a) (F .obj b) (F .mor a b f))
  ≔ let Fa ≔ F .obj a in
    let Fb ≔ F .obj b in
    let GFa ≔ G .obj Fa in
    let GFb ≔ G .obj Fb in
    let ea ≔ eta .fst .component a in
    let eb ≔ eta .fst .component b in
    ch6c_two_out_of_three_left (C .hom a b) (C .hom GFa GFb) (C .hom a GFb)
      (f ↦ G .mor Fa Fb (F .mor a b f)) (f ↦ C .comp a b GFb eb f) (m ↦ C .comp a GFa GFb m ea)
      (f ↦ eta .fst .natural a b f)
      (cat_postcompose_equiv C b GFb eb (eta .snd b) a .equiv)
      (cat_precompose_equiv C a GFa ea (eta .snd a) GFb .equiv)

def nat_iso_counit_double_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) (x y : D .ob)
  : isEquiv (D .hom x y) (D .hom (F .obj (G .obj x)) (F .obj (G .obj y)))
      (g ↦ F .mor (G .obj x) (G .obj y) (G .mor x y g))
  ≔ let FGx ≔ F .obj (G .obj x) in
    let FGy ≔ F .obj (G .obj y) in
    let ex ≔ eps .fst .component x in
    let ey ≔ eps .fst .component y in
    ch6c_two_out_of_three_left (D .hom x y) (D .hom FGx FGy) (D .hom FGx y)
      (g ↦ F .mor (G .obj x) (G .obj y) (G .mor x y g)) (g ↦ D .comp FGx x y g ex) (m ↦ D .comp FGx FGy y ey m)
      (g ↦ inverse (D .hom FGx y) (D .comp FGx x y g ex)
          (D .comp FGx FGy y ey (F .mor (G .obj x) (G .obj y) (G .mor x y g))) (eps .fst .natural x y g))
      (cat_precompose_equiv D FGx x ex (eps .snd x) y .equiv)
      (cat_postcompose_equiv D FGy y ey (eps .snd y) FGx .equiv)

{` G is fully faithful (2-out-of-6, then 2-out-of-3). `}
def nat_isos_inverse_mor_is_equiv (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) (x y : D .ob)
  : isEquiv (D .hom x y) (C .hom (G .obj x) (G .obj y)) (G .mor x y)
  ≔ let Gx ≔ G .obj x in
    let Gy ≔ G .obj y in
    let FGx ≔ F .obj Gx in
    let FGy ≔ F .obj Gy in
    ch6c_two_out_of_three_left (D .hom x y) (C .hom Gx Gy) (D .hom FGx FGy)
      (G .mor x y) (g ↦ F .mor Gx Gy (G .mor x y g)) (F .mor Gx Gy)
      (g ↦ refl (F .mor Gx Gy (G .mor x y g)))
      (nat_iso_counit_double_mor_is_equiv C D F G eps x y)
      (ch6c_two_out_of_six (D .hom x y) (C .hom Gx Gy) (D .hom FGx FGy) (C .hom (G .obj FGx) (G .obj FGy))
        (G .mor x y) (F .mor Gx Gy) (G .mor FGx FGy)
        (nat_iso_counit_double_mor_is_equiv C D F G eps x y)
        (nat_iso_unit_double_mor_is_equiv C D F G eta Gx Gy))

def nat_isos_transpose (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F)) (c : C .ob) (d : D .ob)
  (k : D .hom (F .obj c) d) : C .hom c (G .obj d)
  ≔ C .comp c (G .obj (F .obj c)) (G .obj d) (G .mor (F .obj c) d k) (eta .fst .component c)

def nat_isos_transpose_equiv (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) (c : C .ob) (d : D .ob)
  : Equiv (D .hom (F .obj c) d) (C .hom c (G .obj d))
  ≔ compose_equiv (D .hom (F .obj c) d) (C .hom (G .obj (F .obj c)) (G .obj d)) (C .hom c (G .obj d))
      (G .mor (F .obj c) d, nat_isos_inverse_mor_is_equiv C D F G eta eps (F .obj c) d)
      (cat_precompose_equiv C c (G .obj (F .obj c)) (eta .fst .component c) (eta .snd c) (G .obj d))

def nat_isos_natural_left (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F)) (c c' : C .ob) (f : C .hom c' c)
  (d : D .ob) (k : D .hom (F .obj c) d)
  : Id (C .hom c' (G .obj d))
      (C .comp c' c (G .obj d) (nat_isos_transpose C D F G eta c d k) f)
      (nat_isos_transpose C D F G eta c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
  ≔ let Fc ≔ F .obj c in
    let Fc' ≔ F .obj c' in
    let GFc ≔ G .obj Fc in
    let GFc' ≔ G .obj Fc' in
    let Gd ≔ G .obj d in
    let Gk ≔ G .mor Fc d k in
    let GFf ≔ G .mor Fc' Fc (F .mor c' c f) in
    let ec ≔ eta .fst .component c in
    let ec' ≔ eta .fst .component c' in
    calc
      C .comp c' c Gd (C .comp c GFc Gd Gk ec) f
      = C .comp c' GFc Gd Gk (C .comp c' c GFc ec f)
        by inverse (C .hom c' Gd) (C .comp c' GFc Gd Gk (C .comp c' c GFc ec f))
             (C .comp c' c Gd (C .comp c GFc Gd Gk ec) f) (C .assoc c' c GFc Gd f ec Gk)
      = C .comp c' GFc Gd Gk (C .comp c' GFc' GFc GFf ec')
        by cat_whisker_left C c' GFc Gd Gk (C .comp c' c GFc ec f) (C .comp c' GFc' GFc GFf ec')
             (inverse (C .hom c' GFc) (C .comp c' GFc' GFc GFf ec') (C .comp c' c GFc ec f)
               (eta .fst .natural c' c f))
      = C .comp c' GFc' Gd (C .comp GFc' GFc Gd Gk GFf) ec'
        by C .assoc c' GFc' GFc Gd ec' GFf Gk
      = C .comp c' GFc' Gd (G .mor Fc' d (D .comp Fc' Fc d k (F .mor c' c f))) ec'
        by cat_whisker_right C c' GFc' Gd (C .comp GFc' GFc Gd Gk GFf)
             (G .mor Fc' d (D .comp Fc' Fc d k (F .mor c' c f))) ec'
             (inverse (C .hom GFc' Gd) (G .mor Fc' d (D .comp Fc' Fc d k (F .mor c' c f)))
               (C .comp GFc' GFc Gd Gk GFf) (G .map_comp Fc' Fc d (F .mor c' c f) k)) ∎

def nat_isos_natural_right (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F)) (c : C .ob) (d d' : D .ob)
  (g : D .hom d d') (k : D .hom (F .obj c) d)
  : Id (C .hom c (G .obj d'))
      (C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (nat_isos_transpose C D F G eta c d k))
      (nat_isos_transpose C D F G eta c d' (D .comp (F .obj c) d d' g k))
  ≔ let Fc ≔ F .obj c in
    let GFc ≔ G .obj Fc in
    let Gd ≔ G .obj d in
    let Gd' ≔ G .obj d' in
    let ec ≔ eta .fst .component c in
    concat (C .hom c Gd')
      (C .comp c Gd Gd' (G .mor d d' g) (C .comp c GFc Gd (G .mor Fc d k) ec))
      (C .comp c GFc Gd' (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k)) ec)
      (C .comp c GFc Gd' (G .mor Fc d' (D .comp Fc d d' g k)) ec)
      (C .assoc c GFc Gd Gd' ec (G .mor Fc d k) (G .mor d d' g))
      (cat_whisker_right C c GFc Gd' (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k))
        (G .mor Fc d' (D .comp Fc d d' g k)) ec
        (inverse (C .hom GFc Gd') (G .mor Fc d' (D .comp Fc d d' g k))
          (C .comp GFc Gd Gd' (G .mor d d' g) (G .mor Fc d k)) (G .map_comp Fc d d' k g)))

def nat_isos_right_adjoint (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) : RightAdjointData C D F
  ≔ (right ≔ G,
     transpose ≔ nat_isos_transpose C D F G eta,
     transpose_iso ≔ c d ↦ type_equiv_to_is_iso (D .hom (F .obj c) d) (C .hom c (G .obj d))
       (nat_isos_transpose C D F G eta c d) (nat_isos_transpose_equiv C D F G eta eps c d .equiv),
     natural_left ≔ c c' f d ↦ funext (D .hom (F .obj c) d) (_ ↦ C .hom c' (G .obj d))
       (k ↦ C .comp c' c (G .obj d) (nat_isos_transpose C D F G eta c d k) f)
       (k ↦ nat_isos_transpose C D F G eta c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
       (k ↦ nat_isos_natural_left C D F G eta c c' f d k),
     natural_right ≔ c d d' g ↦ funext (D .hom (F .obj c) d) (_ ↦ C .hom c (G .obj d'))
       (k ↦ C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (nat_isos_transpose C D F G eta c d k))
       (k ↦ nat_isos_transpose C D F G eta c d' (D .comp (F .obj c) d d' g k))
       (k ↦ nat_isos_natural_right C D F G eta c d d' g k))

{` The unit G(id) ∘ η_c is a composite of isomorphisms. `}
def nat_isos_unit_iso (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) (c : C .ob)
  : CatIsIso C c (G .obj (F .obj c)) (adjunction_unit C D F (nat_isos_right_adjoint C D F G eta eps) c)
  ≔ cat_iso_compose C c (G .obj (F .obj c)) (G .obj (F .obj c))
      (functor_iso D C G (F .obj c) (F .obj c) (cat_identity_iso D (F .obj c)))
      (eta .fst .component c, eta .snd c) .snd

{` The counit ε'_d is the arrow with G(ε'_d) ∘ η_{Gd} = id; G(ε'_d) is a
   left inverse of an isomorphism, and G reflects isomorphisms. `}
def nat_isos_counit_iso (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) (d : D .ob)
  : CatIsIso D (F .obj (G .obj d)) d (adjunction_counit C D F (nat_isos_right_adjoint C D F G eta eps) d)
  ≔ let Gd ≔ G .obj d in
    let FGd ≔ F .obj Gd in
    let e ≔ nat_isos_transpose_equiv C D F G eta eps Gd d in
    let k ≔ equiv_inverse_map (D .hom FGd d) (C .hom Gd Gd) e (C .idn Gd) in
    mor_equiv_functor_reflects_iso D C G (nat_isos_inverse_mor_is_equiv C D F G eta eps) FGd d k
      (cat_left_inverse_is_iso C Gd (G .obj FGd) (eta .fst .component Gd) (eta .snd Gd) (G .mor FGd d k)
        (equiv_counit (D .hom FGd d) (C .hom Gd Gd) e (C .idn Gd)))

def cat_equivalence_from_nat_isos (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D)) : IsCatEquivalence C D F
  ≔ (nat_isos_right_adjoint C D F G eta eps,
     (nat_isos_unit_iso C D F G eta eps, nat_isos_counit_iso C D F G eta eps))

{` Litmus checks. The right adjoint produced from G is G itself, and its
   transposition is G(k) ∘ η_c. `}
def cat_equivalence_from_nat_isos_right (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (eta : NatIso C C (functor_identity C) (functor_compose C D C G F))
  (eps : NatIso D D (functor_compose D C D F G) (functor_identity D))
  : Id (WildFunctor D C) (cat_equivalence_from_nat_isos C D F G eta eps .fst .right) G
  ≔ refl G

{` The identity natural isomorphisms between the identity functor and its
   composite with itself (which agree on objects and arrows). `}
def nat_iso_identity_functor_unit (C : WildPrecat)
  : NatIso C C (functor_identity C) (functor_compose C C C (functor_identity C) (functor_identity C))
  ≔ ((component ≔ a ↦ C .idn a, natural ≔ nat_trans_identity C C (functor_identity C) .natural),
     a ↦ cat_identity_is_iso C a)

def nat_iso_identity_functor_counit (C : WildPrecat)
  : NatIso C C (functor_compose C C C (functor_identity C) (functor_identity C)) (functor_identity C)
  ≔ ((component ≔ a ↦ C .idn a, natural ≔ nat_trans_identity C C (functor_identity C) .natural),
     a ↦ cat_identity_is_iso C a)

def identity_cat_equivalence_from_nat_isos (C : WildPrecat) : IsCatEquivalence C C (functor_identity C)
  ≔ cat_equivalence_from_nat_isos C C (functor_identity C) (functor_identity C)
      (nat_iso_identity_functor_unit C) (nat_iso_identity_functor_counit C)

{` Its transposition is G(k) ∘ η_c = k ∘ id. `}
def identity_cat_equivalence_from_nat_isos_transpose (C : WildPrecat) (c d : C .ob) (k : C .hom c d)
  : Id (C .hom c d) (identity_cat_equivalence_from_nat_isos C .fst .transpose c d k) (C .comp c c d k (C .idn c))
  ≔ refl (C .comp c c d k (C .idn c))

{` The identity equivalence is fully faithful. `}
def identity_cat_equivalence_ff (C : WildPrecat) : IsFullyFaithful C C (functor_identity C)
  ≔ wild_cat_equivalence_ff C C (functor_identity C) (identity_is_cat_equivalence C)

{` A concrete non-equivalence: the functor from the path groupoid of Bool
   to the path groupoid of Unit induced by the constant map is not full
   (there is no path true = false), so by lem:cat-equiv-ff it is not an
   equivalence. `}
def bool_to_unit_path_functor : WildFunctor (PathWild Bool) (PathWild Unit)
  ≔ (obj ≔ _ ↦ star.,
     mor ≔ a b p ↦ refl (star. : Unit),
     map_id ≔ a ↦ refl (refl (star. : Unit)),
     map_comp ≔ a b c p q ↦
       inverse (Id Unit star. star.) (concat Unit star. star. star. (refl (star. : Unit)) (refl (star. : Unit)))
         (refl (star. : Unit)) (concat_p1 Unit star. star. (refl (star. : Unit))))

def bool_to_unit_path_functor_not_equivalence
  (E : IsCatEquivalence (PathWild Bool) (PathWild Unit) bool_to_unit_path_functor) : Empty
  ≔ let ff ≔ wild_cat_equivalence_ff (PathWild Bool) (PathWild Unit) bool_to_unit_path_functor E in
    mere_rec (BookFiber (Id Bool true. false.) (Id Unit star. star.)
        (bool_to_unit_path_functor .mor true. false.) (refl (star. : Unit)))
      Empty empty_prop
      (t ↦ bool_encode true. false. (t .fst))
      (ff .snd true. false. (refl (star. : Unit)))
