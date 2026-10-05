export "03-functors"
export "../../../src/53-integer-multiplication"

{` Blind statements, chapter 6, section "Adjunctions".

   def:adjunction. The natural isomorphism α : Hom_D(F−,−) ≅ Hom_C(−,G−) is
   given, as the text before the definition explains ("if we fix either X or
   Y, we get natural transformations"), by components
   α_{c,d} : Hom_D(F c, d) → Hom_C(c, G d) that are isomorphisms in the wild
   category of types, with naturality squares (identifications of functions,
   in the orientation of def:nat-trans: G'(k) ∘ α = α ∘ F'(k)) in each
   variable separately. `}
def BlindAdjTranspose (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (G : BlindWildFunctor D C) : Type
  ≔ (c : C .ob) (d : D .ob) → D .hom (F .fob c) d → C .hom c (G .fob d)

def BlindAdjNatIso (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (G : BlindWildFunctor D C)
  (tr : BlindAdjTranspose C D F G) : Type
  ≔ Product
      ((c : C .ob) (d : D .ob)
        → BlindIsIso blind_universe_wild_precat (D .hom (F .fob c) d) (C .hom c (G .fob d)) (tr c d))
      (Product
        ((c : C .ob) (d d' : D .ob) (k : D .hom d d')
          → Id (D .hom (F .fob c) d → C .hom c (G .fob d'))
              (h ↦ C .comp c (G .fob d) (G .fob d') (G .fhom d d' k) (tr c d h))
              (h ↦ tr c d' (D .comp (F .fob c) d d' k h)))
        ((c c' : C .ob) (d : D .ob) (f : C .hom c' c)
          → Id (D .hom (F .fob c) d → C .hom c' (G .fob d))
              (h ↦ C .comp c' c (G .fob d) (tr c d h) f)
              (h ↦ tr c' d (D .comp (F .fob c') (F .fob c) d h (F .fhom c' c f)))))

{` F ⊣ G for given functors: the natural isomorphism. `}
def BlindAdjoint (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (G : BlindWildFunctor D C) : Type
  ≔ Σ (BlindAdjTranspose C D F G) (BlindAdjNatIso C D F G)

def BlindAdjunction (C D : BlindWildPrecat) : Type ≔ sig (
  left : BlindWildFunctor C D,
  right : BlindWildFunctor D C,
  adj : BlindAdjoint C D left right)

{` The data of a right adjoint of a fixed F (cor:adj-unique). `}
def BlindRightAdjoint (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ Σ (BlindWildFunctor D C) (G ↦ BlindAdjoint C D F G)

{` eq:adj-unit-counit (components). η_c = α(id_{F c}), ε_d = α⁻¹(id_{G d})
   with α⁻¹ the section from the iso data. `}
def blind_adj_unit (C D : BlindWildPrecat) (A : BlindAdjunction C D) (c : C .ob)
  : C .hom c (A .right .fob (A .left .fob c))
  ≔ A .adj .fst c (A .left .fob c) (D .idn (A .left .fob c))

def blind_adj_counit (C D : BlindWildPrecat) (A : BlindAdjunction C D) (d : D .ob)
  : D .hom (A .left .fob (A .right .fob d)) d
  ≔ A .adj .snd .fst (A .right .fob d) d .fst .fst (C .idn (A .right .fob d))

{` xca:adj-triangles (fig:adj-triangles). `}
def blind_xca_adj_triangles : Type
  ≔ (C D : BlindWildPrecat) (A : BlindAdjunction C D)
    → let F ≔ A .left in let G ≔ A .right in
      Product
        ((c : C .ob) → Id (D .hom (F .fob c) (F .fob c))
           (D .comp (F .fob c) (F .fob (G .fob (F .fob c))) (F .fob c)
              (blind_adj_counit C D A (F .fob c)) (F .fhom c (G .fob (F .fob c)) (blind_adj_unit C D A c)))
           (D .idn (F .fob c)))
        ((d : D .ob) → Id (C .hom (G .fob d) (G .fob d))
           (C .comp (G .fob d) (G .fob (F .fob (G .fob d))) (G .fob d)
              (G .fhom (F .fob (G .fob d)) d (blind_adj_counit C D A d)) (blind_adj_unit C D A (G .fob d)))
           (C .idn (G .fob d)))

{` xca:adj-from-triangles. From F, G, natural η : id → GF, ε : FG → id and
   triangle fillers, α(f) ≔ G(f) ∘ η_c is a natural isomorphism. `}
def blind_xca_adj_from_triangles : Type
  ≔ (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (G : BlindWildFunctor D C)
    (eta : BlindNatTrans C C (blind_functor_id C) (blind_functor_comp C D C G F))
    (eps : BlindNatTrans D D (blind_functor_comp D C D F G) (blind_functor_id D))
    (t1 : (c : C .ob) → Id (D .hom (F .fob c) (F .fob c))
       (D .comp (F .fob c) (F .fob (G .fob (F .fob c))) (F .fob c)
          (eps .fst (F .fob c)) (F .fhom c (G .fob (F .fob c)) (eta .fst c)))
       (D .idn (F .fob c)))
    (t2 : (d : D .ob) → Id (C .hom (G .fob d) (G .fob d))
       (C .comp (G .fob d) (G .fob (F .fob (G .fob d))) (G .fob d)
          (G .fhom (F .fob (G .fob d)) d (eps .fst d)) (eta .fst (G .fob d)))
       (C .idn (G .fob d)))
    → BlindAdjNatIso C D F G
        (c d f ↦ C .comp c (G .fob (F .fob c)) (G .fob d) (G .fhom (F .fob c) d f) (eta .fst c))

{` ex:trunc-adj. Left adjoint: the truncation functor (given its laws,
   ex:n-trunc-functor); right adjoint: the inclusion; α = precomposition with
   the unit |−|. `}
def blind_ex_trunc_adj : Type
  ≔ (k : Nat)
    (tl : BlindWildFunctorLaws blind_universe_wild_precat (blind_truncated_universe k)
            (A ↦ (Trunc k A, trunc_level k A)) (blind_trunc_hom k))
    → BlindAdjNatIso blind_universe_wild_precat (blind_truncated_universe k)
        (blind_functor_of_laws blind_universe_wild_precat (blind_truncated_universe k)
           (A ↦ (Trunc k A, trunc_level k A)) (blind_trunc_hom k) tl)
        (blind_full_subcat_inclusion blind_universe_wild_precat
           (A ↦ (HLevel (suc. k) A, hlevel_isprop (suc. k) A)))
        (X Y h ↦ x ↦ h (trunc_unit k X x))

{` ex:pt-unpt-adj. WRONG AS PRINTED: "(A_+ →* X) ≃ (A → X_÷) for A : U_*,
   X : U" has the roles of A and X swapped (X_÷ is meaningless for X : U), so
   no literal statement is possible. Corrected: (X_+ →* A) ≃ (X → A_÷) for
   X : U, A : U_*, by precomposition with inl. `}
def blind_ex_pt_unpt_adj_corrected : Type
  ≔ (pl : BlindWildFunctorLaws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom)
    → BlindAdjNatIso blind_universe_wild_precat blind_pointed_wild_precat
        (blind_functor_of_laws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom pl)
        blind_forget_functor
        (X A h ↦ x ↦ h .fst (inl. x))

{` ex:Sigma-Pi-adj. Set^A and U^A as categories of families over A with
   fiberwise maps. `}
def blind_family_set_precat (A : Type) : BlindPrecat
  ≔ (((A → SetTypes), (X Y ↦ (a : A) → X a .fst → Y a .fst), (X ↦ a x ↦ x),
      (X Y Z g f ↦ a x ↦ g a (f a x)),
      (X Y f ↦ refl f), (X Y f ↦ refl f), (X Y Z W f g h ↦ refl (a x ↦ h a (g a (f a x))))),
     (X Y ↦ pi_set A (a ↦ X a .fst → Y a .fst) (a ↦ pi_set (X a .fst) (_ ↦ Y a .fst) (_ ↦ Y a .snd))))

def blind_family_wild_precat (A : Type) : BlindWildPrecat
  ≔ ((A → Type), (X Y ↦ (a : A) → X a → Y a), (X ↦ a x ↦ x),
     (X Y Z g f ↦ a x ↦ g a (f a x)),
     (X Y f ↦ refl f), (X Y f ↦ refl f), (X Y Z W f g h ↦ refl (a x ↦ h a (g a (f a x)))))

{` f^*, f_!, f_* on families of sets. `}
def blind_set_pullback (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_family_set_precat B .fst) (blind_family_set_precat A .fst)
  ≔ ((Y ↦ a ↦ Y (f a)), (Y Y' g ↦ a ↦ g (f a)), (Y ↦ refl (a ↦ (y : Y (f a) .fst) ↦ y)),
     (Y Y' Y'' g g' ↦ refl (a ↦ (y : Y (f a) .fst) ↦ g' (f a) (g (f a) y))))

def BlindSetLowerSum (A B : Type) (f : A → B) (X : A → SetTypes) (b : B) : Type
  ≔ Σ A (a ↦ Product (Id B (f a) b) (X a .fst))

def blind_set_lower_ob (A B : Type) (f : A → B) (X : A → SetTypes) : B → SetTypes
  ≔ b ↦ (SetTrunc (BlindSetLowerSum A B f X b), set_trunc_set (BlindSetLowerSum A B f X b))

def blind_set_lower_hom (A B : Type) (f : A → B) (X X' : A → SetTypes)
  (g : (a : A) → X a .fst → X' a .fst) (b : B)
  : SetTrunc (BlindSetLowerSum A B f X b) → SetTrunc (BlindSetLowerSum A B f X' b)
  ≔ set_trunc_rec (BlindSetLowerSum A B f X b) (SetTrunc (BlindSetLowerSum A B f X' b))
      (set_trunc_set (BlindSetLowerSum A B f X' b))
      (u ↦ set_trunc (BlindSetLowerSum A B f X' b) (u .fst, (u .snd .fst, g (u .fst) (u .snd .snd))))

def blind_set_upper_ob (A B : Type) (f : A → B) (X : A → SetTypes) : B → SetTypes
  ≔ b ↦ ((a : A) → Id B (f a) b → X a .fst,
         pi_set A (a ↦ Id B (f a) b → X a .fst) (a ↦ pi_set (Id B (f a) b) (_ ↦ X a .fst) (_ ↦ X a .snd)))

def blind_set_upper (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_family_set_precat A .fst) (blind_family_set_precat B .fst)
  ≔ (blind_set_upper_ob A B f, (X X' g ↦ b s a p ↦ g a (s a p)),
     (X ↦ refl (b ↦ (s : (a : A) → Id B (f a) b → X a .fst) ↦ s)),
     (X X' X'' g g' ↦ refl (b ↦ (s : (a : A) → Id B (f a) b → X a .fst) ↦ a p ↦ g' a (g a (s a p)))))

{` f^*, f_! (no truncation), f_* on families of types. `}
def blind_type_pullback (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_family_wild_precat B) (blind_family_wild_precat A)
  ≔ ((Y ↦ a ↦ Y (f a)), (Y Y' g ↦ a ↦ g (f a)), (Y ↦ refl (a ↦ (y : Y (f a)) ↦ y)),
     (Y Y' Y'' g g' ↦ refl (a ↦ (y : Y (f a)) ↦ g' (f a) (g (f a) y))))

def blind_type_lower (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_family_wild_precat A) (blind_family_wild_precat B)
  ≔ ((X ↦ b ↦ Σ A (a ↦ Product (Id B (f a) b) (X a))),
     (X X' g ↦ b u ↦ (u .fst, (u .snd .fst, g (u .fst) (u .snd .snd)))),
     (X ↦ refl (b ↦ (u : Σ A (a ↦ Product (Id B (f a) b) (X a))) ↦ (u .fst, (u .snd .fst, u .snd .snd)))),
     (X X' X'' g g' ↦ refl (b ↦ (u : Σ A (a ↦ Product (Id B (f a) b) (X a)))
        ↦ (u .fst, (u .snd .fst, g' (u .fst) (g (u .fst) (u .snd .snd)))))))

def blind_type_upper (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_family_wild_precat A) (blind_family_wild_precat B)
  ≔ ((X ↦ b ↦ (a : A) → Id B (f a) b → X a), (X X' g ↦ b s a p ↦ g a (s a p)),
     (X ↦ refl (b ↦ (s : (a : A) → Id B (f a) b → X a) ↦ s)),
     (X X' X'' g g' ↦ refl (b ↦ (s : (a : A) → Id B (f a) b → X a) ↦ a p ↦ g' a (g a (s a p)))))

{` f_! ⊣ f^* ⊣ f_* for families of sets (given the functor laws of f_!). `}
def blind_ex_sigma_pi_adj_sets : Type
  ≔ (A B : Type) (f : A → B)
    (ll : BlindWildFunctorLaws (blind_family_set_precat A .fst) (blind_family_set_precat B .fst)
            (blind_set_lower_ob A B f) (blind_set_lower_hom A B f))
    → Product
        (BlindAdjoint (blind_family_set_precat A .fst) (blind_family_set_precat B .fst)
           (blind_functor_of_laws (blind_family_set_precat A .fst) (blind_family_set_precat B .fst)
              (blind_set_lower_ob A B f) (blind_set_lower_hom A B f) ll)
           (blind_set_pullback A B f))
        (BlindAdjoint (blind_family_set_precat B .fst) (blind_family_set_precat A .fst)
           (blind_set_pullback A B f) (blind_set_upper A B f))

def blind_ex_sigma_pi_adj_types : Type
  ≔ (A B : Type) (f : A → B)
    → Product
        (BlindAdjoint (blind_family_wild_precat A) (blind_family_wild_precat B)
           (blind_type_lower A B f) (blind_type_pullback A B f))
        (BlindAdjoint (blind_family_wild_precat B) (blind_family_wild_precat A)
           (blind_type_pullback A B f) (blind_type_upper A B f))

{` The special case A → 1: Σ_A ⊣ cst ⊣ Π_A between U^A and U. `}
def blind_sigma_functor (A : Type) : BlindWildFunctor (blind_family_wild_precat A) blind_universe_wild_precat
  ≔ ((X ↦ Σ A X), (X X' g ↦ u ↦ (u .fst, g (u .fst) (u .snd))),
     (X ↦ refl ((u : Σ A X) ↦ (u .fst, u .snd))),
     (X X' X'' g g' ↦ refl ((u : Σ A X) ↦ (u .fst, g' (u .fst) (g (u .fst) (u .snd))))))

def blind_const_functor (A : Type) : BlindWildFunctor blind_universe_wild_precat (blind_family_wild_precat A)
  ≔ ((Y ↦ _ ↦ Y), (Y Y' g ↦ _ ↦ g), (Y ↦ refl ((_ : A) ↦ (y : Y) ↦ y)),
     (Y Y' Y'' g g' ↦ refl ((_ : A) ↦ (y : Y) ↦ g' (g y))))

def blind_pi_functor (A : Type) : BlindWildFunctor (blind_family_wild_precat A) blind_universe_wild_precat
  ≔ ((X ↦ (a : A) → X a), (X X' g ↦ s a ↦ g a (s a)),
     (X ↦ refl ((s : (a : A) → X a) ↦ s)),
     (X X' X'' g g' ↦ refl ((s : (a : A) → X a) ↦ a ↦ g' a (g a (s a)))))

def blind_ex_sigma_pi_adj_terminal : Type
  ≔ (A : Type)
    → Product (BlindAdjoint (blind_family_wild_precat A) blind_universe_wild_precat
                 (blind_sigma_functor A) (blind_const_functor A))
        (BlindAdjoint blind_universe_wild_precat (blind_family_wild_precat A)
           (blind_const_functor A) (blind_pi_functor A))

{` rem:adj-in-posets (1): for preorders, G is right adjoint to F iff
   F(p) ≤ q ↔ p ≤ G(q). `}
def blind_rem_adj_in_posets : Type
  ≔ (P Q : BlindPreorder) (F : BlindWildFunctor (P .fst .fst) (Q .fst .fst))
    (G : BlindWildFunctor (Q .fst .fst) (P .fst .fst))
    → let Pw ≔ P .fst .fst in let Qw ≔ Q .fst .fst in
      Product
        (BlindAdjoint Pw Qw F G
          → (p : Pw .ob) (q : Qw .ob)
            → Product (Qw .hom (F .fob p) q → Pw .hom p (G .fob q)) (Pw .hom p (G .fob q) → Qw .hom (F .fob p) q))
        (((p : Pw .ob) (q : Qw .ob)
            → Product (Qw .hom (F .fob p) q → Pw .hom p (G .fob q)) (Pw .hom p (G .fob q) → Qw .hom (F .fob p) q))
          → BlindAdjoint Pw Qw F G)

{` rem:adj-in-posets (2): ⌈−⌉ ⊣ ι ⊣ ⌊−⌋ for ι : Z → Q. Rationals as
   fractions n/(d+1) with the cross-multiplied order (a preorder; the
   adjunctions are stated in the biimplication form of (1)). `}
def BlindFrac : Type ≔ Product Int Nat

def blind_frac_le (x y : BlindFrac) : Type
  ≔ IntLe (int_mul (x .fst) (pos. (suc. (y .snd)))) (int_mul (y .fst) (pos. (suc. (x .snd))))

def blind_int_to_frac (n : Int) : BlindFrac ≔ (n, zero.)

def blind_rem_adj_floor_ceil : Type
  ≔ Σ (BlindFrac → Int) (ceil ↦ Σ (BlindFrac → Int) (floor ↦
      Product
        ((q : BlindFrac) (n : Int)
          → Product (IntLe (ceil q) n → blind_frac_le q (blind_int_to_frac n))
              (blind_frac_le q (blind_int_to_frac n) → IntLe (ceil q) n))
        ((n : Int) (q : BlindFrac)
          → Product (blind_frac_le (blind_int_to_frac n) q → IntLe n (floor q))
              (IntLe n (floor q) → blind_frac_le (blind_int_to_frac n) q))))

{` rem:adj-in-posets (3): ∃_f ⊣ f^* ⊣ ∀_f on Sub(A), Sub(B). `}
def blind_sub_exists (A B : Type) (f : A → B) (P : Subtypes A) : Subtypes B
  ≔ b ↦ (Mere (Σ A (a ↦ Product (Id B (f a) b) (P a .fst))),
         mere_isprop (Σ A (a ↦ Product (Id B (f a) b) (P a .fst))))

def blind_sub_forall (A B : Type) (f : A → B) (P : Subtypes A) : Subtypes B
  ≔ b ↦ ((a : A) → Id B (f a) b → P a .fst,
         pi_prop A (a ↦ Id B (f a) b → P a .fst) (a ↦ pi_prop (Id B (f a) b) (_ ↦ P a .fst) (_ ↦ P a .snd)))

def blind_sub_pullback (A B : Type) (f : A → B) (Q : Subtypes B) : Subtypes A ≔ a ↦ Q (f a)

def blind_rem_adj_subsets : Type
  ≔ (A B : Type) (f : A → B)
    → Product
        ((P : Subtypes A) (Q : Subtypes B)
          → Product (Inclusion B (blind_sub_exists A B f P) Q → Inclusion A P (blind_sub_pullback A B f Q))
              (Inclusion A P (blind_sub_pullback A B f Q) → Inclusion B (blind_sub_exists A B f P) Q))
        ((Q : Subtypes B) (P : Subtypes A)
          → Product (Inclusion A (blind_sub_pullback A B f Q) P → Inclusion B Q (blind_sub_forall A B f P))
              (Inclusion B Q (blind_sub_forall A B f P) → Inclusion A (blind_sub_pullback A B f Q) P))
