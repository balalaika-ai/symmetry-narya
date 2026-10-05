export "625-adjunction-units"
export "627-faithful-functor-examples"

{` Chapter 6 (cats.tex), def:adjunction, fidelity check of
   RightAdjointData (module 603). The book asks for a (wild) natural
   isomorphism α : Hom_D(F -, -) ≅ Hom_C(-, G -) of functors
   C^op × D → U; RightAdjointData records naturality in each variable
   separately, as in the prose before the definition. We show the two
   packagings are interchangeable: an adjunction gives a natural
   isomorphism of hom-bifunctors on the product C^op × D, and conversely
   (with the same G and the same α). `}

{` Hom_X(P -, Q -) : C^op × D → U for functors P : C → X, Q : D → X;
   (f, g) acts by k ↦ Q(g) ∘ (k ∘ P(f)). `}
def hom_bifunctor (C D X : WildPrecat) (P : WildFunctor C X) (Q : WildFunctor D X)
  : WildFunctor (ProductWild (OppositeWild C) D) TypeWild
  ≔ (obj ≔ x ↦ X .hom (P .obj (x .fst)) (Q .obj (x .snd)),
     mor ≔ x y f k ↦ X .comp (P .obj (y .fst)) (Q .obj (x .snd)) (Q .obj (y .snd)) (Q .mor (x .snd) (y .snd) (f .snd))
       (X .comp (P .obj (y .fst)) (P .obj (x .fst)) (Q .obj (x .snd)) k (P .mor (y .fst) (x .fst) (f .fst))),
     map_id ≔ x ↦
       let a ≔ P .obj (x .fst) in let u ≔ Q .obj (x .snd) in
       funext (X .hom a u) (_ ↦ X .hom a u)
         (k ↦ X .comp a u u (Q .mor (x .snd) (x .snd) (D .idn (x .snd)))
            (X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst)))))
         (k ↦ k)
         (k ↦ calc
            X .comp a u u (Q .mor (x .snd) (x .snd) (D .idn (x .snd)))
              (X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst))))
            = X .comp a u u (X .idn u) (X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst))))
              by cat_whisker_right X a u u (Q .mor (x .snd) (x .snd) (D .idn (x .snd))) (X .idn u)
                   (X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst)))) (Q .map_id (x .snd))
            = X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst)))
              by X .lu a u (X .comp a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst))))
            = X .comp a a u k (X .idn a)
              by cat_whisker_left X a a u k (P .mor (x .fst) (x .fst) (C .idn (x .fst))) (X .idn a) (P .map_id (x .fst))
            = k by X .ru a u k ∎),
     map_comp ≔ x y z f g ↦
       let c ≔ x .fst in let c' ≔ y .fst in let c'' ≔ z .fst in
       let d ≔ x .snd in let d' ≔ y .snd in let d'' ≔ z .snd in
       let a ≔ P .obj c'' in let b ≔ P .obj c' in let c0 ≔ P .obj c in
       let u ≔ Q .obj d in let v ≔ Q .obj d' in let w ≔ Q .obj d'' in
       let Pf ≔ P .mor c' c (f .fst) in let Pg ≔ P .mor c'' c' (g .fst) in
       let Qf ≔ Q .mor d d' (f .snd) in let Qg ≔ Q .mor d' d'' (g .snd) in
       funext (X .hom c0 u) (_ ↦ X .hom a w)
         (k ↦ X .comp a u w (Q .mor d d'' (D .comp d d' d'' (g .snd) (f .snd)))
            (X .comp a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst)))))
         (k ↦ X .comp a v w Qg (X .comp a b v (X .comp b u v Qf (X .comp b c0 u k Pf)) Pg))
         (k ↦ calc
            X .comp a u w (Q .mor d d'' (D .comp d d' d'' (g .snd) (f .snd)))
              (X .comp a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst))))
            = X .comp a u w (X .comp u v w Qg Qf) (X .comp a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst))))
              by cat_whisker_right X a u w (Q .mor d d'' (D .comp d d' d'' (g .snd) (f .snd))) (X .comp u v w Qg Qf)
                   (X .comp a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst))))
                   (Q .map_comp d d' d'' (f .snd) (g .snd))
            = X .comp a u w (X .comp u v w Qg Qf) (X .comp a c0 u k (X .comp a b c0 Pf Pg))
              by cat_whisker_left X a u w (X .comp u v w Qg Qf)
                   (X .comp a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst))))
                   (X .comp a c0 u k (X .comp a b c0 Pf Pg))
                   (cat_whisker_left X a c0 u k (P .mor c'' c (C .comp c'' c' c (f .fst) (g .fst)))
                     (X .comp a b c0 Pf Pg) (P .map_comp c'' c' c (g .fst) (f .fst)))
            = X .comp a u w (X .comp u v w Qg Qf) (X .comp a b u (X .comp b c0 u k Pf) Pg)
              by cat_whisker_left X a u w (X .comp u v w Qg Qf) (X .comp a c0 u k (X .comp a b c0 Pf Pg))
                   (X .comp a b u (X .comp b c0 u k Pf) Pg) (X .assoc a b c0 u Pg Pf k)
            = X .comp a v w Qg (X .comp a u v Qf (X .comp a b u (X .comp b c0 u k Pf) Pg))
              by inverse (X .hom a w) (X .comp a v w Qg (X .comp a u v Qf (X .comp a b u (X .comp b c0 u k Pf) Pg)))
                   (X .comp a u w (X .comp u v w Qg Qf) (X .comp a b u (X .comp b c0 u k Pf) Pg))
                   (X .assoc a u v w (X .comp a b u (X .comp b c0 u k Pf) Pg) Qf Qg)
            = X .comp a v w Qg (X .comp a b v (X .comp b u v Qf (X .comp b c0 u k Pf)) Pg)
              by cat_whisker_left X a v w Qg (X .comp a u v Qf (X .comp a b u (X .comp b c0 u k Pf) Pg))
                   (X .comp a b v (X .comp b u v Qf (X .comp b c0 u k Pf)) Pg)
                   (X .assoc a b u v Pg (X .comp b c0 u k Pf) Qf) ∎))

{` def:adjunction: Hom_D(F -, -) and Hom_C(-, G -). `}
def adjunction_left_hom_bifunctor (C D : WildPrecat) (F : WildFunctor C D)
  : WildFunctor (ProductWild (OppositeWild C) D) TypeWild
  ≔ hom_bifunctor C D D F (functor_identity D)

def adjunction_right_hom_bifunctor (C D : WildPrecat) (G : WildFunctor D C)
  : WildFunctor (ProductWild (OppositeWild C) D) TypeWild
  ≔ hom_bifunctor C D C (functor_identity C) G

{` An adjunction gives a natural isomorphism of hom-bifunctors. `}
def adjunction_hom_nat_iso (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : NatIso (ProductWild (OppositeWild C) D) TypeWild (adjunction_left_hom_bifunctor C D F)
      (adjunction_right_hom_bifunctor C D (R .right))
  ≔ ((component ≔ x ↦ R .transpose (x .fst) (x .snd),
      natural ≔ x y f ↦
        let c ≔ x .fst in let d ≔ x .snd in let c' ≔ y .fst in let d' ≔ y .snd in
        let G ≔ R .right in let Ff ≔ F .mor c' c (f .fst) in
        funext (D .hom (F .obj c) d) (_ ↦ C .hom c' (G .obj d'))
          (k ↦ C .comp c' (G .obj d) (G .obj d') (G .mor d d' (f .snd))
             (C .comp c' c (G .obj d) (R .transpose c d k) (f .fst)))
          (k ↦ R .transpose c' d' (D .comp (F .obj c') d d' (f .snd) (D .comp (F .obj c') (F .obj c) d k Ff)))
          (k ↦ concat (C .hom c' (G .obj d'))
             (C .comp c' (G .obj d) (G .obj d') (G .mor d d' (f .snd))
               (C .comp c' c (G .obj d) (R .transpose c d k) (f .fst)))
             (C .comp c' (G .obj d) (G .obj d') (G .mor d d' (f .snd))
               (R .transpose c' d (D .comp (F .obj c') (F .obj c) d k Ff)))
             (R .transpose c' d' (D .comp (F .obj c') d d' (f .snd) (D .comp (F .obj c') (F .obj c) d k Ff)))
             (cat_whisker_left C c' (G .obj d) (G .obj d') (G .mor d d' (f .snd))
               (C .comp c' c (G .obj d) (R .transpose c d k) (f .fst))
               (R .transpose c' d (D .comp (F .obj c') (F .obj c) d k Ff))
               (adjunction_natural_left_at C D F R c c' (f .fst) d k))
             (adjunction_natural_right_at C D F R c' d d' (f .snd) (D .comp (F .obj c') (F .obj c) d k Ff)))),
     x ↦ R .transpose_iso (x .fst) (x .snd))

{` Conversely, a natural isomorphism of hom-bifunctors gives an
   adjunction with the same G and α (naturality in each variable is the
   joint naturality at (f, id) and at (id, g)). `}
def right_adjoint_from_hom_nat_iso (C D : WildPrecat) (F : WildFunctor C D) (G : WildFunctor D C)
  (alpha : NatIso (ProductWild (OppositeWild C) D) TypeWild (adjunction_left_hom_bifunctor C D F)
     (adjunction_right_hom_bifunctor C D G))
  : RightAdjointData C D F
  ≔ let a ≔ alpha .fst .component in
    (right ≔ G,
     transpose ≔ c d ↦ a (c, d),
     transpose_iso ≔ c d ↦ alpha .snd (c, d),
     natural_left ≔ c c' f d ↦
       funext (D .hom (F .obj c) d) (_ ↦ C .hom c' (G .obj d))
         (k ↦ C .comp c' c (G .obj d) (a (c, d) k) f)
         (k ↦ a (c', d) (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
         (k ↦ calc
            C .comp c' c (G .obj d) (a (c, d) k) f
            = C .comp c' (G .obj d) (G .obj d) (C .idn (G .obj d)) (C .comp c' c (G .obj d) (a (c, d) k) f)
              by inverse (C .hom c' (G .obj d))
                   (C .comp c' (G .obj d) (G .obj d) (C .idn (G .obj d)) (C .comp c' c (G .obj d) (a (c, d) k) f))
                   (C .comp c' c (G .obj d) (a (c, d) k) f)
                   (C .lu c' (G .obj d) (C .comp c' c (G .obj d) (a (c, d) k) f))
            = C .comp c' (G .obj d) (G .obj d) (G .mor d d (D .idn d)) (C .comp c' c (G .obj d) (a (c, d) k) f)
              by cat_whisker_right C c' (G .obj d) (G .obj d) (C .idn (G .obj d)) (G .mor d d (D .idn d))
                   (C .comp c' c (G .obj d) (a (c, d) k) f)
                   (inverse (C .hom (G .obj d) (G .obj d)) (G .mor d d (D .idn d)) (C .idn (G .obj d)) (G .map_id d))
            = a (c', d) (D .comp (F .obj c') d d (D .idn d) (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))
              by happly (D .hom (F .obj c) d) (_ ↦ C .hom c' (G .obj d))
                   (k ↦ C .comp c' (G .obj d) (G .obj d) (G .mor d d (D .idn d)) (C .comp c' c (G .obj d) (a (c, d) k) f))
                   (k ↦ a (c', d) (D .comp (F .obj c') d d (D .idn d) (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f))))
                   (alpha .fst .natural (c, d) (c', d) (f, D .idn d)) k
            = a (c', d) (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f))
              by refl (a (c', d)) (D .lu (F .obj c') d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f))) ∎),
     natural_right ≔ c d d' g ↦
       funext (D .hom (F .obj c) d) (_ ↦ C .hom c (G .obj d'))
         (k ↦ C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (a (c, d) k))
         (k ↦ a (c, d') (D .comp (F .obj c) d d' g k))
         (k ↦ calc
            C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (a (c, d) k)
            = C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (C .comp c c (G .obj d) (a (c, d) k) (C .idn c))
              by cat_whisker_left C c (G .obj d) (G .obj d') (G .mor d d' g) (a (c, d) k)
                   (C .comp c c (G .obj d) (a (c, d) k) (C .idn c))
                   (inverse (C .hom c (G .obj d)) (C .comp c c (G .obj d) (a (c, d) k) (C .idn c)) (a (c, d) k)
                     (C .ru c (G .obj d) (a (c, d) k)))
            = a (c, d') (D .comp (F .obj c) d d' g (D .comp (F .obj c) (F .obj c) d k (F .mor c c (C .idn c))))
              by happly (D .hom (F .obj c) d) (_ ↦ C .hom c (G .obj d'))
                   (k ↦ C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (C .comp c c (G .obj d) (a (c, d) k) (C .idn c)))
                   (k ↦ a (c, d') (D .comp (F .obj c) d d' g (D .comp (F .obj c) (F .obj c) d k (F .mor c c (C .idn c)))))
                   (alpha .fst .natural (c, d) (c, d') (C .idn c, g)) k
            = a (c, d') (D .comp (F .obj c) d d' g (D .comp (F .obj c) (F .obj c) d k (D .idn (F .obj c))))
              by refl (a (c, d'))
                   (cat_whisker_left D (F .obj c) d d' g (D .comp (F .obj c) (F .obj c) d k (F .mor c c (C .idn c)))
                     (D .comp (F .obj c) (F .obj c) d k (D .idn (F .obj c)))
                     (cat_whisker_left D (F .obj c) (F .obj c) d k (F .mor c c (C .idn c)) (D .idn (F .obj c))
                       (F .map_id c)))
            = a (c, d') (D .comp (F .obj c) d d' g k)
              by refl (a (c, d'))
                   (cat_whisker_left D (F .obj c) d d' g (D .comp (F .obj c) (F .obj c) d k (D .idn (F .obj c))) k
                     (D .ru (F .obj c) d k)) ∎))

{` Round trip: going to the bifunctor form and back keeps G and α on the
   nose. `}
def adjunction_hom_nat_iso_round_trip (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob)
  : Id (D .hom (F .obj c) d → C .hom c (R .right .obj d))
      (right_adjoint_from_hom_nat_iso C D F (R .right) (adjunction_hom_nat_iso C D F R) .transpose c d)
      (R .transpose c d)
  ≔ refl (R .transpose c d)

{` Litmus: the hom-bifunctor of the identity adjunction on Set acts on
   (f, g) by k ↦ g ∘ k ∘ f. `}
def set_hom_bifunctor_litmus
  : Id Bool
      (adjunction_left_hom_bifunctor SetWild SetWild (functor_identity SetWild)
        .mor (set_cat_bool, set_cat_bool) (set_cat_bool, set_cat_bool) (bool_not, bool_not) (x ↦ x) true.)
      true.
  ≔ refl (true. : Bool)
