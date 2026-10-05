export "601-categories-of-types"

{` Chapter 6, sections 6.3-6.4 (core): opposite categories, wild functors,
   natural transformations, functor precategories, fully faithful and
   essentially surjective functors. `}

{` def:op-cat. Same objects and identities, hom_op(a,b) = hom(b,a),
   composition reversed; λ and ρ swap roles and α⁻¹ plays the role of α. `}
def OppositeWild (C : WildPrecat) : WildPrecat
  ≔ (ob ≔ C .ob,
     hom ≔ a b ↦ C .hom b a,
     idn ≔ C .idn,
     comp ≔ a b c g f ↦ C .comp c b a f g,
     lu ≔ a b f ↦ C .ru b a f,
     ru ≔ a b f ↦ C .lu b a f,
     assoc ≔ a b c d f g h ↦
       inverse (C .hom d a) (C .comp d b a f (C .comp d c b g h)) (C .comp d c a (C .comp c b a f g) h)
         (C .assoc d c b a h g f))

def opposite_precat (C : Precat) : Precat ≔ (OppositeWild (C .wild), a b ↦ C .homset b a)

{` def:functor. A wild functor; F_id : F(id_a) = id_{F a} and
   F_∘ : F(g ∘ f) = F(g) ∘ F(f). Between precategories (or whenever the
   codomain is a precategory) these are the book's functors. `}
def WildFunctor (C D : WildPrecat) : Type ≔ sig (
  obj : C .ob → D .ob,
  mor : (a b : C .ob) → C .hom a b → D .hom (obj a) (obj b),
  map_id : (a : C .ob) → Id (D .hom (obj a) (obj a)) (mor a a (C .idn a)) (D .idn (obj a)),
  map_comp : (a b c : C .ob) (f : C .hom a b) (g : C .hom b c)
    → Id (D .hom (obj a) (obj c)) (mor a c (C .comp a b c g f))
        (D .comp (obj a) (obj b) (obj c) (mor b c g) (mor a b f)) )

{` xca:wildprecat-of-wildprecats (identity and composite wild functors). `}
def functor_identity (C : WildPrecat) : WildFunctor C C
  ≔ (obj ≔ x ↦ x,
     mor ≔ a b f ↦ f,
     map_id ≔ a ↦ refl (C .idn a),
     map_comp ≔ a b c f g ↦ refl (C .comp a b c g f))

def functor_compose (C D E : WildPrecat) (G : WildFunctor D E) (F : WildFunctor C D) : WildFunctor C E
  ≔ (obj ≔ x ↦ G .obj (F .obj x),
     mor ≔ a b f ↦ G .mor (F .obj a) (F .obj b) (F .mor a b f),
     map_id ≔ a ↦
       concat (E .hom (G .obj (F .obj a)) (G .obj (F .obj a)))
         (G .mor (F .obj a) (F .obj a) (F .mor a a (C .idn a)))
         (G .mor (F .obj a) (F .obj a) (D .idn (F .obj a)))
         (E .idn (G .obj (F .obj a)))
         (refl (G .mor (F .obj a) (F .obj a)) (F .map_id a))
         (G .map_id (F .obj a)),
     map_comp ≔ a b c f g ↦
       concat (E .hom (G .obj (F .obj a)) (G .obj (F .obj c)))
         (G .mor (F .obj a) (F .obj c) (F .mor a c (C .comp a b c g f)))
         (G .mor (F .obj a) (F .obj c) (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)))
         (E .comp (G .obj (F .obj a)) (G .obj (F .obj b)) (G .obj (F .obj c))
           (G .mor (F .obj b) (F .obj c) (F .mor b c g)) (G .mor (F .obj a) (F .obj b) (F .mor a b f)))
         (refl (G .mor (F .obj a) (F .obj c)) (F .map_comp a b c f g))
         (G .map_comp (F .obj a) (F .obj b) (F .obj c) (F .mor a b f) (F .mor b c g)))

{` xca:wild-functor-isos: every wild functor maps isomorphisms to
   isomorphisms. `}
def functor_preserves_iso (C D : WildPrecat) (F : WildFunctor C D) (a b : C .ob) (f : C .hom a b)
  (i : CatIsIso C a b f) : CatIsIso D (F .obj a) (F .obj b) (F .mor a b f)
  ≔ let g ≔ i .fst .fst in
    let h ≔ i .snd .fst in
    ((F .mor b a g,
      concat (D .hom (F .obj b) (F .obj b))
        (D .comp (F .obj b) (F .obj a) (F .obj b) (F .mor a b f) (F .mor b a g))
        (F .mor b b (C .comp b a b f g)) (D .idn (F .obj b))
        (inverse (D .hom (F .obj b) (F .obj b)) (F .mor b b (C .comp b a b f g))
          (D .comp (F .obj b) (F .obj a) (F .obj b) (F .mor a b f) (F .mor b a g)) (F .map_comp b a b g f))
        (concat (D .hom (F .obj b) (F .obj b)) (F .mor b b (C .comp b a b f g)) (F .mor b b (C .idn b))
          (D .idn (F .obj b)) (refl (F .mor b b) (i .fst .snd)) (F .map_id b))),
     (F .mor b a h,
      concat (D .hom (F .obj a) (F .obj a))
        (D .comp (F .obj a) (F .obj b) (F .obj a) (F .mor b a h) (F .mor a b f))
        (F .mor a a (C .comp a b a h f)) (D .idn (F .obj a))
        (inverse (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .comp a b a h f))
          (D .comp (F .obj a) (F .obj b) (F .obj a) (F .mor b a h) (F .mor a b f)) (F .map_comp a b a f h))
        (concat (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .comp a b a h f)) (F .mor a a (C .idn a))
          (D .idn (F .obj a)) (refl (F .mor a a) (i .snd .snd)) (F .map_id a))))

def functor_iso (C D : WildPrecat) (F : WildFunctor C D) (a b : C .ob) (e : CatIso C a b)
  : CatIso D (F .obj a) (F .obj b)
  ≔ (F .mor a b (e .fst), functor_preserves_iso C D F a b (e .fst) (e .snd))

{` def:nat-trans. Components α_a : F a → G a and fillers of the
   naturality squares, oriented G(f) ∘ α_a = α_b ∘ F(f). `}
def WildNatTrans (C D : WildPrecat) (F G : WildFunctor C D) : Type ≔ sig (
  component : (a : C .ob) → D .hom (F .obj a) (G .obj a),
  natural : (a b : C .ob) (f : C .hom a b)
    → Id (D .hom (F .obj a) (G .obj b))
        (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (component a))
        (D .comp (F .obj a) (F .obj b) (G .obj b) (component b) (F .mor a b f)) )

def NatSquare (C D : WildPrecat) (F G : WildFunctor C D) (alpha : (a : C .ob) → D .hom (F .obj a) (G .obj a))
  : Type
  ≔ (a b : C .ob) (f : C .hom a b)
    → Id (D .hom (F .obj a) (G .obj b))
        (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
        (D .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f))

{` "If D is a precategory, then the types of the naturality square fillers
   are propositions." `}
def nat_square_prop (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  (alpha : (a : C .ob) → D .hom (F .obj a) (G .obj a)) : isProp (NatSquare C D F G alpha)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b)
        → Id (D .hom (F .obj a) (G .obj b))
            (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
            (D .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b)
          → Id (D .hom (F .obj a) (G .obj b))
              (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
              (D .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
        (b ↦ pi_prop (C .hom a b) (f ↦ Id (D .hom (F .obj a) (G .obj b))
              (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
              (D .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
          (f ↦ hs (F .obj a) (G .obj b)
              (D .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
              (D .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))))

def nat_trans_sigma_equiv (C D : WildPrecat) (F G : WildFunctor C D)
  : Equiv (WildNatTrans C D F G) (Σ ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G))
  ≔ quasi_inverse_equiv (WildNatTrans C D F G) (Σ ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G))
      (t ↦ (t .component, t .natural)) (s ↦ (s .fst, s .snd)) (t ↦ refl t) (s ↦ refl s)

{` Natural transformations into a precategory are determined by their
   components. `}
def nat_trans_path (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  (alpha beta : WildNatTrans C D F G)
  (p : Id ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (alpha .component) (beta .component))
  : Id (WildNatTrans C D F G) alpha beta
  ≔ (p, pathover_of_eq ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G)
        (alpha .component) (beta .component) p (alpha .natural) (beta .natural)
        (nat_square_prop C D hs F G (beta .component)
          (transport ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G)
            (alpha .component) (beta .component) p (alpha .natural)) (beta .natural)))

def nat_trans_path_pointwise (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  (alpha beta : WildNatTrans C D F G)
  (h : (a : C .ob) → Id (D .hom (F .obj a) (G .obj a)) (alpha .component a) (beta .component a))
  : Id (WildNatTrans C D F G) alpha beta
  ≔ nat_trans_path C D hs F G alpha beta
      (funext (C .ob) (a ↦ D .hom (F .obj a) (G .obj a)) (alpha .component) (beta .component) h)

def nat_trans_set (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  : isSet (WildNatTrans C D F G)
  ≔ hlevel_two_to_set (WildNatTrans C D F G)
      (hlevel_equiv (suc. (suc. zero.)) (Σ ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G))
        (WildNatTrans C D F G)
        (canonical_inverse_equiv (WildNatTrans C D F G)
          (Σ ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G)) (nat_trans_sigma_equiv C D F G))
        (set_to_hlevel_two (Σ ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G))
          (sigma_set ((a : C .ob) → D .hom (F .obj a) (G .obj a)) (NatSquare C D F G)
            (pi_set (C .ob) (a ↦ D .hom (F .obj a) (G .obj a)) (a ↦ hs (F .obj a) (G .obj a)))
            (alpha ↦ prop_is_set (NatSquare C D F G alpha) (nat_square_prop C D hs F G alpha)))))

{` def:functor-cat: identity natural transformation and objectwise
   composition. `}
def nat_trans_identity (C D : WildPrecat) (F : WildFunctor C D) : WildNatTrans C D F F
  ≔ (component ≔ a ↦ D .idn (F .obj a),
     natural ≔ a b f ↦
       concat (D .hom (F .obj a) (F .obj b))
         (D .comp (F .obj a) (F .obj a) (F .obj b) (F .mor a b f) (D .idn (F .obj a)))
         (F .mor a b f)
         (D .comp (F .obj a) (F .obj b) (F .obj b) (D .idn (F .obj b)) (F .mor a b f))
         (D .ru (F .obj a) (F .obj b) (F .mor a b f))
         (inverse (D .hom (F .obj a) (F .obj b))
           (D .comp (F .obj a) (F .obj b) (F .obj b) (D .idn (F .obj b)) (F .mor a b f)) (F .mor a b f)
           (D .lu (F .obj a) (F .obj b) (F .mor a b f))))

def nat_trans_compose (C D : WildPrecat) (F G H : WildFunctor C D)
  (beta : WildNatTrans C D G H) (alpha : WildNatTrans C D F G) : WildNatTrans C D F H
  ≔ (component ≔ a ↦ D .comp (F .obj a) (G .obj a) (H .obj a) (beta .component a) (alpha .component a),
     natural ≔ a b f ↦
       let Fa ≔ F .obj a in let Fb ≔ F .obj b in
       let Ga ≔ G .obj a in let Gb ≔ G .obj b in
       let Ha ≔ H .obj a in let Hb ≔ H .obj b in
       let al ≔ alpha .component a in let bl ≔ alpha .component b in
       let be ≔ beta .component a in let bb ≔ beta .component b in
       let Hf ≔ H .mor a b f in let Gf ≔ G .mor a b f in let Ff ≔ F .mor a b f in
       concat (D .hom Fa Hb)
         (D .comp Fa Ha Hb Hf (D .comp Fa Ga Ha be al))
         (D .comp Fa Ga Hb (D .comp Ga Ha Hb Hf be) al)
         (D .comp Fa Fb Hb (D .comp Fb Gb Hb bb bl) Ff)
         (D .assoc Fa Ga Ha Hb al be Hf)
         (concat (D .hom Fa Hb)
           (D .comp Fa Ga Hb (D .comp Ga Ha Hb Hf be) al)
           (D .comp Fa Ga Hb (D .comp Ga Gb Hb bb Gf) al)
           (D .comp Fa Fb Hb (D .comp Fb Gb Hb bb bl) Ff)
           (cat_whisker_right D Fa Ga Hb (D .comp Ga Ha Hb Hf be) (D .comp Ga Gb Hb bb Gf) al
             (beta .natural a b f))
           (concat (D .hom Fa Hb)
             (D .comp Fa Ga Hb (D .comp Ga Gb Hb bb Gf) al)
             (D .comp Fa Gb Hb bb (D .comp Fa Ga Gb Gf al))
             (D .comp Fa Fb Hb (D .comp Fb Gb Hb bb bl) Ff)
             (inverse (D .hom Fa Hb) (D .comp Fa Gb Hb bb (D .comp Fa Ga Gb Gf al))
               (D .comp Fa Ga Hb (D .comp Ga Gb Hb bb Gf) al) (D .assoc Fa Ga Gb Hb al Gf bb))
             (concat (D .hom Fa Hb)
               (D .comp Fa Gb Hb bb (D .comp Fa Ga Gb Gf al))
               (D .comp Fa Gb Hb bb (D .comp Fa Fb Gb bl Ff))
               (D .comp Fa Fb Hb (D .comp Fb Gb Hb bb bl) Ff)
               (cat_whisker_left D Fa Gb Hb bb (D .comp Fa Ga Gb Gf al) (D .comp Fa Fb Gb bl Ff)
                 (alpha .natural a b f))
               (D .assoc Fa Fb Gb Hb Ff bl bb)))))

{` def:functor-cat: the functor precategory [C, D] for a wild
   precategory C and a precategory D. `}
def FunctorWild (C : WildPrecat) (D : Precat) : WildPrecat
  ≔ (ob ≔ WildFunctor C (D .wild),
     hom ≔ F G ↦ WildNatTrans C (D .wild) F G,
     idn ≔ F ↦ nat_trans_identity C (D .wild) F,
     comp ≔ F G H beta alpha ↦ nat_trans_compose C (D .wild) F G H beta alpha,
     lu ≔ F G alpha ↦ nat_trans_path_pointwise C (D .wild) (D .homset) F G
       (nat_trans_compose C (D .wild) F G G (nat_trans_identity C (D .wild) G) alpha) alpha
       (a ↦ D .wild .lu (F .obj a) (G .obj a) (alpha .component a)),
     ru ≔ F G alpha ↦ nat_trans_path_pointwise C (D .wild) (D .homset) F G
       (nat_trans_compose C (D .wild) F F G alpha (nat_trans_identity C (D .wild) F)) alpha
       (a ↦ D .wild .ru (F .obj a) (G .obj a) (alpha .component a)),
     assoc ≔ F G H K alpha beta gamma ↦ nat_trans_path_pointwise C (D .wild) (D .homset) F K
       (nat_trans_compose C (D .wild) F H K gamma (nat_trans_compose C (D .wild) F G H beta alpha))
       (nat_trans_compose C (D .wild) F G K (nat_trans_compose C (D .wild) G H K gamma beta) alpha)
       (a ↦ D .wild .assoc (F .obj a) (G .obj a) (H .obj a) (K .obj a)
         (alpha .component a) (beta .component a) (gamma .component a)))

def FunctorPrecat (C : WildPrecat) (D : Precat) : Precat
  ≔ (FunctorWild C D, F G ↦ nat_trans_set C (D .wild) (D .homset) F G)

{` def:full-faithful. Faithful: the maps on arrows are injections (the
   book's def:injection, IsEmbedding); full: they are surjections. `}
def IsFaithful (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ (a b : C .ob) → IsEmbedding (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)

def IsFull (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ (a b : C .ob) → Surjective (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)

def IsFullyFaithful (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ Product (IsFaithful C D F) (IsFull C D F)

{` def:full-faithful: "(and hence equivalences)", in both directions. `}
def fully_faithful_equiv (C D : WildPrecat) (F : WildFunctor C D) (h : IsFullyFaithful C D F)
  (a b : C .ob) : BookEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b))
  ≔ native_embedding_surjection_equiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)
      (h .fst a b) (h .snd a b)

def fully_faithful_from_equivs (C D : WildPrecat) (F : WildFunctor C D)
  (h : (a b : C .ob) → BookIsEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  : IsFullyFaithful C D F
  ≔ (a b ↦ y ↦ contractible_prop (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y)
        (native_contraction (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y) (h a b y)),
     a b ↦ y ↦ mere (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y) (h a b y .center))

def is_fully_faithful_prop (C D : WildPrecat) (F : WildFunctor C D) : isProp (IsFullyFaithful C D F)
  ≔ product_prop (IsFaithful C D F) (IsFull C D F)
      (pi_prop (C .ob) (a ↦ (b : C .ob) → IsEmbedding (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
        (a ↦ pi_prop (C .ob) (b ↦ IsEmbedding (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
          (b ↦ pi_prop (D .hom (F .obj a) (F .obj b))
            (y ↦ isProp (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y))
            (y ↦ isprop_isprop (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y)))))
      (pi_prop (C .ob) (a ↦ (b : C .ob) → Surjective (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
        (a ↦ pi_prop (C .ob) (b ↦ Surjective (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
          (b ↦ pi_prop (D .hom (F .obj a) (F .obj b))
            (y ↦ Mere (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y))
            (y ↦ mere_isprop (BookFiber (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b) y)))))

{` def:functor-split-eso. Split essentially surjective: for every d a
   chosen c with an isomorphism F(c) ≅ d; essentially surjective: merely. `}
def IsSplitEso (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ (d : D .ob) → Σ (C .ob) (c ↦ CatIso D (F .obj c) d)

def IsEso (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ (d : D .ob) → Mere (Σ (C .ob) (c ↦ CatIso D (F .obj c) d))

def is_eso_prop (C D : WildPrecat) (F : WildFunctor C D) : isProp (IsEso C D F)
  ≔ pi_prop (D .ob) (d ↦ Mere (Σ (C .ob) (c ↦ CatIso D (F .obj c) d)))
      (d ↦ mere_isprop (Σ (C .ob) (c ↦ CatIso D (F .obj c) d)))

{` def:we-cat: a weak equivalence is fully faithful and essentially
   surjective on objects. `}
def IsWeakEquivalence (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ Product (IsFullyFaithful C D F) (IsEso C D F)

{` Natural isomorphisms: natural transformations whose components are
   isomorphisms (by xca:funext-nat-trans, these are the isomorphisms of
   the functor precategory when D is a precategory). `}
def IsNatIso (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G) : Type
  ≔ (a : C .ob) → CatIsIso D (F .obj a) (G .obj a) (alpha .component a)

def NatIso (C D : WildPrecat) (F G : WildFunctor C D) : Type
  ≔ Σ (WildNatTrans C D F G) (IsNatIso C D F G)

{` Identifications of functors into a precategory: the functor laws are
   propositions, so a functor is determined by its actions on objects and
   arrows (FunctorData). `}
def FunctorData (C D : WildPrecat) : Type
  ≔ Σ (C .ob → D .ob) (obj ↦ (a b : C .ob) → C .hom a b → D .hom (obj a) (obj b))

def functor_data (C D : WildPrecat) (F : WildFunctor C D) : FunctorData C D ≔ (F .obj, F .mor)

def FunctorLaws (C D : WildPrecat) (t : FunctorData C D) : Type
  ≔ Product ((a : C .ob) → Id (D .hom (t .fst a) (t .fst a)) (t .snd a a (C .idn a)) (D .idn (t .fst a)))
      ((a b c : C .ob) (f : C .hom a b) (g : C .hom b c)
        → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
            (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))

def functor_laws_prop (C D : WildPrecat) (hs : HasHomSets D) (t : FunctorData C D) : isProp (FunctorLaws C D t)
  ≔ product_prop
      ((a : C .ob) → Id (D .hom (t .fst a) (t .fst a)) (t .snd a a (C .idn a)) (D .idn (t .fst a)))
      ((a b c : C .ob) (f : C .hom a b) (g : C .hom b c)
        → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
            (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
      (pi_prop (C .ob) (a ↦ Id (D .hom (t .fst a) (t .fst a)) (t .snd a a (C .idn a)) (D .idn (t .fst a)))
        (a ↦ hs (t .fst a) (t .fst a) (t .snd a a (C .idn a)) (D .idn (t .fst a))))
      (pi_prop (C .ob) (a ↦ (b c : C .ob) (f : C .hom a b) (g : C .hom b c)
          → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
              (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
        (a ↦ pi_prop (C .ob) (b ↦ (c : C .ob) (f : C .hom a b) (g : C .hom b c)
            → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
                (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
          (b ↦ pi_prop (C .ob) (c ↦ (f : C .hom a b) (g : C .hom b c)
              → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
                  (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
            (c ↦ pi_prop (C .hom a b) (f ↦ (g : C .hom b c)
                → Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
                    (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
              (f ↦ pi_prop (C .hom b c) (g ↦ Id (D .hom (t .fst a) (t .fst c)) (t .snd a c (C .comp a b c g f))
                    (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f)))
                (g ↦ hs (t .fst a) (t .fst c) (t .snd a c (C .comp a b c g f))
                    (D .comp (t .fst a) (t .fst b) (t .fst c) (t .snd b c g) (t .snd a b f))))))))

def functor_sigma_equiv (C D : WildPrecat)
  : Equiv (WildFunctor C D) (Σ (FunctorData C D) (FunctorLaws C D))
  ≔ quasi_inverse_equiv (WildFunctor C D) (Σ (FunctorData C D) (FunctorLaws C D))
      (F ↦ ((F .obj, F .mor), (F .map_id, F .map_comp)))
      (s ↦ (obj ≔ s .fst .fst, mor ≔ s .fst .snd, map_id ≔ s .snd .fst, map_comp ≔ s .snd .snd))
      (F ↦ refl F) (s ↦ refl s)

def functor_path_equiv (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  : Equiv (Id (WildFunctor C D) F G) (Id (FunctorData C D) (functor_data C D F) (functor_data C D G))
  ≔ let S ≔ Σ (FunctorData C D) (FunctorLaws C D) in
    let e ≔ functor_sigma_equiv C D in
    compose_equiv (Id (WildFunctor C D) F G) (Id S (e .map F) (e .map G))
      (Id (FunctorData C D) (functor_data C D F) (functor_data C D G))
      (equivalence_on_paths (WildFunctor C D) S e F G)
      (subtype_path_equiv (FunctorData C D) (FunctorLaws C D) (functor_laws_prop C D hs) (e .map F) (e .map G))

def functor_path (C D : WildPrecat) (hs : HasHomSets D) (F G : WildFunctor C D)
  (r : Id (FunctorData C D) (functor_data C D F) (functor_data C D G)) : Id (WildFunctor C D) F G
  ≔ equiv_inverse_map (Id (WildFunctor C D) F G) (Id (FunctorData C D) (functor_data C D F) (functor_data C D G))
      (functor_path_equiv C D hs F G) r
