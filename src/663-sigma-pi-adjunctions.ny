export "662-families-of-sets"

{` Chapter 6 (cats.tex), ex:Sigma-Pi-adj, the wild version: for
   f : A → B the string of wild adjunctions f_! ⊣ f^* ⊣ f_* between the
   wild categories of families U^A and U^B, with
     f^*(Y) ≔ Y ∘ f,
     f_!(X)(b) ≔ Σ_{a:A} (f(a) = b) × X(a),
     f_*(X)(b) ≔ Π_{a:A} (f(a) = b) → X(a),
   and the special case ! : A → 1, Σ_A ⊣ cst ⊣ Π_A between U^A and U. The
   adjunctions are RightAdjointData (module 603): transposition maps that
   are isomorphisms in the wild category of types, natural in both
   variables. `}

def family_reindex_functor (A B : Type) (f : A → B) : WildFunctor (FamilyWild B) (FamilyWild A)
  ≔ (obj ≔ Y ↦ a ↦ Y (f a),
     mor ≔ Y Y' g ↦ a ↦ g (f a),
     map_id ≔ Y ↦ refl ((a y ↦ y) : (a : A) → Y (f a) → Y (f a)),
     map_comp ≔ Y Y' Y'' g g' ↦ refl ((a y ↦ g' (f a) (g (f a) y)) : (a : A) → Y (f a) → Y'' (f a)))

def FamilyPushSum (A B : Type) (f : A → B) (X : A → Type) : B → Type
  ≔ b ↦ Σ A (a ↦ Product (Id B (f a) b) (X a))

def FamilyPushProduct (A B : Type) (f : A → B) (X : A → Type) : B → Type
  ≔ b ↦ (a : A) → Id B (f a) b → X a

def family_sum_functor (A B : Type) (f : A → B) : WildFunctor (FamilyWild A) (FamilyWild B)
  ≔ (obj ≔ FamilyPushSum A B f,
     mor ≔ X X' g ↦ b t ↦ (t .fst, (t .snd .fst, g (t .fst) (t .snd .snd))),
     map_id ≔ X ↦ refl ((b t ↦ t) : (b : B) → FamilyPushSum A B f X b → FamilyPushSum A B f X b),
     map_comp ≔ X X' X'' g g' ↦
       refl ((b t ↦ (t .fst, (t .snd .fst, g' (t .fst) (g (t .fst) (t .snd .snd)))))
         : (b : B) → FamilyPushSum A B f X b → FamilyPushSum A B f X'' b))

def family_product_functor (A B : Type) (f : A → B) : WildFunctor (FamilyWild A) (FamilyWild B)
  ≔ (obj ≔ FamilyPushProduct A B f,
     mor ≔ X X' g ↦ b s a p ↦ g a (s a p),
     map_id ≔ X ↦ refl ((b s ↦ s) : (b : B) → FamilyPushProduct A B f X b → FamilyPushProduct A B f X b),
     map_comp ≔ X X' X'' g g' ↦
       refl ((b s a p ↦ g' a (g a (s a p))) : (b : B) → FamilyPushProduct A B f X b → FamilyPushProduct A B f X'' b))

{` Path-induction lemmas for the two transpositions. `}
def family_sum_transport_lemma (A B : Type) (f : A → B) (Y : B → Type) (a : A)
  (u : (b : B) → Id B (f a) b → Y b) (b : B) (p : Id B (f a) b)
  : Id (Y b) (transport B Y (f a) b p (u (f a) (refl (f a)))) (u b p)
  ≔ J B (f a) (b p ↦ Id (Y b) (transport B Y (f a) b p (u (f a) (refl (f a)))) (u b p))
      (transport_refl B Y (f a) (u (f a) (refl (f a)))) b p

def family_transport_inverse_refl (B : Type) (Y : B → Type) (b : B) (y : Y b)
  : Id (Y b) (transport B Y b b (inverse B b b (refl b)) y) y
  ≔ concat (Y b) (transport B Y b b (inverse B b b (refl b)) y) (transport B Y b b (refl b) y) y
      (refl ((r ↦ transport B Y b b r y) : Id B b b → Y b) (inverse_refl B b))
      (transport_refl B Y b y)

def family_product_transport_lemma (A B : Type) (f : A → B) (Y : B → Type) (Z : A → Type)
  (chi : (b : B) → Y b → (a : A) → Id B (f a) b → Z a) (a : A) (b : B) (p : Id B (f a) b) (y : Y b)
  : Id (Z a) (chi (f a) (transport B Y b (f a) (inverse B (f a) b p) y) a (refl (f a))) (chi b y a p)
  ≔ J B (f a)
      (b p ↦ (y : Y b) → Id (Z a) (chi (f a) (transport B Y b (f a) (inverse B (f a) b p) y) a (refl (f a)))
                (chi b y a p))
      (y ↦ refl ((w ↦ chi (f a) w a (refl (f a))) : Y (f a) → Z a) (family_transport_inverse_refl B Y (f a) y))
      b p y

def family_transport_natural (B : Type) (Y Y' : B → Type) (g : (b : B) → Y' b → Y b) (b0 b1 : B)
  (q : Id B b0 b1) (y : Y' b0)
  : Id (Y b1) (transport B Y b0 b1 q (g b0 y)) (g b1 (transport B Y' b0 b1 q y))
  ≔ J B b0 (b1 q ↦ Id (Y b1) (transport B Y b0 b1 q (g b0 y)) (g b1 (transport B Y' b0 b1 q y)))
      (concat (Y b0) (transport B Y b0 b0 (refl b0) (g b0 y)) (g b0 y) (g b0 (transport B Y' b0 b0 (refl b0) y))
        (transport_refl B Y b0 (g b0 y))
        (inverse (Y b0) (g b0 (transport B Y' b0 b0 (refl b0) y)) (g b0 y)
          (refl (g b0) (transport_refl B Y' b0 y))))
      b1 q

{` ex:Sigma-Pi-adj, f_! ⊣ f^*: transposition φ ↦ (a, x) ↦ φ(f a)(a, refl, x);
   its inverse transports along the identification f(a) = b. `}
def family_sum_transpose (A B : Type) (f : A → B) (X : A → Type) (Y : B → Type)
  (phi : (b : B) → FamilyPushSum A B f X b → Y b) : (a : A) → X a → Y (f a)
  ≔ a x ↦ phi (f a) (a, (refl (f a), x))

def family_sum_untranspose (A B : Type) (f : A → B) (X : A → Type) (Y : B → Type)
  (psi : (a : A) → X a → Y (f a)) : (b : B) → FamilyPushSum A B f X b → Y b
  ≔ b t ↦ transport B Y (f (t .fst)) b (t .snd .fst) (psi (t .fst) (t .snd .snd))

def family_sum_transpose_is_iso (A B : Type) (f : A → B) (X : A → Type) (Y : B → Type)
  : CatIsIso TypeWild ((b : B) → FamilyPushSum A B f X b → Y b) ((a : A) → X a → Y (f a))
      (family_sum_transpose A B f X Y)
  ≔ let HB ≔ (b : B) → FamilyPushSum A B f X b → Y b in
    let HA ≔ (a : A) → X a → Y (f a) in
    ((family_sum_untranspose A B f X Y,
      funext HA (_ ↦ HA) (psi ↦ family_sum_transpose A B f X Y (family_sum_untranspose A B f X Y psi)) (psi ↦ psi)
        (psi ↦ funext2 A X (a _ ↦ Y (f a))
          (family_sum_transpose A B f X Y (family_sum_untranspose A B f X Y psi)) psi
          (a x ↦ transport_refl B Y (f a) (psi a x)))),
     (family_sum_untranspose A B f X Y,
      funext HB (_ ↦ HB) (phi ↦ family_sum_untranspose A B f X Y (family_sum_transpose A B f X Y phi)) (phi ↦ phi)
        (phi ↦ funext2 B (FamilyPushSum A B f X) (b _ ↦ Y b)
          (family_sum_untranspose A B f X Y (family_sum_transpose A B f X Y phi)) phi
          (b t ↦ family_sum_transport_lemma A B f Y (t .fst) (b' p ↦ phi b' (t .fst, (p, t .snd .snd))) b
                   (t .snd .fst)))))

def family_sum_right_adjoint (A B : Type) (f : A → B)
  : RightAdjointData (FamilyWild A) (FamilyWild B) (family_sum_functor A B f)
  ≔ (right ≔ family_reindex_functor A B f,
     transpose ≔ family_sum_transpose A B f,
     transpose_iso ≔ family_sum_transpose_is_iso A B f,
     natural_left ≔ X X' g Y ↦
       refl ((k ↦ (a x ↦ k (f a) (a, (refl (f a), g a x))))
         : ((b : B) → FamilyPushSum A B f X b → Y b) → (a : A) → X' a → Y (f a)),
     natural_right ≔ X Y Y' h ↦
       refl ((k ↦ (a x ↦ h (f a) (k (f a) (a, (refl (f a), x)))))
         : ((b : B) → FamilyPushSum A B f X b → Y b) → (a : A) → X a → Y' (f a)))

def family_sum_adjunction (A B : Type) (f : A → B) : WildAdjunction (FamilyWild A) (FamilyWild B)
  ≔ (family_sum_functor A B f, family_sum_right_adjoint A B f)

{` ex:Sigma-Pi-adj, f^* ⊣ f_*: transposition ψ ↦ (b, y, a, p) ↦ ψ a (p⁻¹ · y),
   with inverse χ ↦ (a, y) ↦ χ (f a) y a refl. `}
def family_product_transpose (A B : Type) (f : A → B) (Y : B → Type) (X : A → Type)
  (psi : (a : A) → Y (f a) → X a) : (b : B) → Y b → FamilyPushProduct A B f X b
  ≔ b y a p ↦ psi a (transport B Y b (f a) (inverse B (f a) b p) y)

def family_product_untranspose (A B : Type) (f : A → B) (Y : B → Type) (X : A → Type)
  (chi : (b : B) → Y b → FamilyPushProduct A B f X b) : (a : A) → Y (f a) → X a
  ≔ a y ↦ chi (f a) y a (refl (f a))

def family_product_transpose_is_iso (A B : Type) (f : A → B) (Y : B → Type) (X : A → Type)
  : CatIsIso TypeWild ((a : A) → Y (f a) → X a) ((b : B) → Y b → FamilyPushProduct A B f X b)
      (family_product_transpose A B f Y X)
  ≔ let HA ≔ (a : A) → Y (f a) → X a in
    let HB ≔ (b : B) → Y b → FamilyPushProduct A B f X b in
    ((family_product_untranspose A B f Y X,
      funext HB (_ ↦ HB) (chi ↦ family_product_transpose A B f Y X (family_product_untranspose A B f Y X chi))
        (chi ↦ chi)
        (chi ↦ funext3 B Y (b _ ↦ A) (b _ a ↦ Id B (f a) b → X a)
          (family_product_transpose A B f Y X (family_product_untranspose A B f Y X chi)) chi
          (b y a ↦ funext (Id B (f a) b) (_ ↦ X a)
            (family_product_transpose A B f Y X (family_product_untranspose A B f Y X chi) b y a) (chi b y a)
            (p ↦ family_product_transport_lemma A B f Y X chi a b p y)))),
     (family_product_untranspose A B f Y X,
      funext HA (_ ↦ HA) (psi ↦ family_product_untranspose A B f Y X (family_product_transpose A B f Y X psi))
        (psi ↦ psi)
        (psi ↦ funext2 A (a ↦ Y (f a)) (a _ ↦ X a)
          (family_product_untranspose A B f Y X (family_product_transpose A B f Y X psi)) psi
          (a y ↦ refl (psi a) (family_transport_inverse_refl B Y (f a) y)))))

def family_product_right_adjoint (A B : Type) (f : A → B)
  : RightAdjointData (FamilyWild B) (FamilyWild A) (family_reindex_functor A B f)
  ≔ (right ≔ family_product_functor A B f,
     transpose ≔ family_product_transpose A B f,
     transpose_iso ≔ family_product_transpose_is_iso A B f,
     natural_left ≔ Y Y' g X ↦
       let HA ≔ (a : A) → Y (f a) → X a in
       let L : HA → (b : B) → Y' b → FamilyPushProduct A B f X b
         ≔ k b y' a p ↦ k a (transport B Y b (f a) (inverse B (f a) b p) (g b y')) in
       let R : HA → (b : B) → Y' b → FamilyPushProduct A B f X b
         ≔ k b y' a p ↦ k a (g (f a) (transport B Y' b (f a) (inverse B (f a) b p) y')) in
       funext HA (_ ↦ (b : B) → Y' b → FamilyPushProduct A B f X b) L R
         (k ↦ funext3 B Y' (b _ ↦ A) (b _ a ↦ Id B (f a) b → X a) (L k) (R k)
           (b y' a ↦ funext (Id B (f a) b) (_ ↦ X a) (L k b y' a) (R k b y' a)
             (p ↦ refl (k a) (family_transport_natural B Y Y' g b (f a) (inverse B (f a) b p) y')))),
     natural_right ≔ Y X X' h ↦
       refl ((k ↦ (b y a p ↦ h a (k a (transport B Y b (f a) (inverse B (f a) b p) y))))
         : ((a : A) → Y (f a) → X a) → (b : B) → Y b → FamilyPushProduct A B f X' b))

def family_product_adjunction (A B : Type) (f : A → B) : WildAdjunction (FamilyWild B) (FamilyWild A)
  ≔ (family_reindex_functor A B f, family_product_right_adjoint A B f)

{` The special case ! : A → 1: Σ_A ⊣ cst ⊣ Π_A between U^A and U. `}
def family_total_functor (A : Type) : WildFunctor (FamilyWild A) TypeWild
  ≔ (obj ≔ X ↦ Σ A X,
     mor ≔ X X' g ↦ t ↦ (t .fst, g (t .fst) (t .snd)),
     map_id ≔ X ↦ refl ((t ↦ t) : Σ A X → Σ A X),
     map_comp ≔ X X' X'' g g' ↦ refl ((t ↦ (t .fst, g' (t .fst) (g (t .fst) (t .snd)))) : Σ A X → Σ A X''))

def family_constant_functor (A : Type) : WildFunctor TypeWild (FamilyWild A)
  ≔ (obj ≔ Y ↦ _ ↦ Y,
     mor ≔ Y Y' g ↦ _ ↦ g,
     map_id ≔ Y ↦ refl ((_ y ↦ y) : A → Y → Y),
     map_comp ≔ Y Y' Y'' g g' ↦ refl ((_ y ↦ g' (g y)) : A → Y → Y''))

def family_pi_functor (A : Type) : WildFunctor (FamilyWild A) TypeWild
  ≔ (obj ≔ X ↦ (a : A) → X a,
     mor ≔ X X' g ↦ s a ↦ g a (s a),
     map_id ≔ X ↦ refl ((s ↦ s) : ((a : A) → X a) → (a : A) → X a),
     map_comp ≔ X X' X'' g g' ↦ refl ((s a ↦ g' a (g a (s a))) : ((a : A) → X a) → (a : A) → X'' a))

def family_total_right_adjoint (A : Type)
  : RightAdjointData (FamilyWild A) TypeWild (family_total_functor A)
  ≔ (right ≔ family_constant_functor A,
     transpose ≔ X Y k a x ↦ k (a, x),
     transpose_iso ≔ X Y ↦
       ((m t ↦ m (t .fst) (t .snd), refl ((m ↦ m) : ((a : A) → X a → Y) → (a : A) → X a → Y)),
        (m t ↦ m (t .fst) (t .snd), refl ((k ↦ k) : (Σ A X → Y) → Σ A X → Y))),
     natural_left ≔ X X' g Y ↦ refl ((k a x ↦ k (a, g a x)) : (Σ A X → Y) → (a : A) → X' a → Y),
     natural_right ≔ X Y Y' h ↦ refl ((k a x ↦ h (k (a, x))) : (Σ A X → Y) → (a : A) → X a → Y'))

def family_total_adjunction (A : Type) : WildAdjunction (FamilyWild A) TypeWild
  ≔ (family_total_functor A, family_total_right_adjoint A)

def family_pi_right_adjoint (A : Type)
  : RightAdjointData TypeWild (FamilyWild A) (family_constant_functor A)
  ≔ (right ≔ family_pi_functor A,
     transpose ≔ Y X k y a ↦ k a y,
     transpose_iso ≔ Y X ↦
       ((m a y ↦ m y a, refl ((m ↦ m) : (Y → (a : A) → X a) → Y → (a : A) → X a)),
        (m a y ↦ m y a, refl ((k ↦ k) : ((a : A) → Y → X a) → (a : A) → Y → X a))),
     natural_left ≔ Y Y' g X ↦ refl ((k y a ↦ k a (g y)) : ((a : A) → Y → X a) → Y' → (a : A) → X a),
     natural_right ≔ Y X X' h ↦ refl ((k y a ↦ h a (k a y)) : ((a : A) → Y → X a) → Y → (a : A) → X' a))

def family_pi_adjunction (A : Type) : WildAdjunction TypeWild (FamilyWild A)
  ≔ (family_constant_functor A, family_pi_right_adjoint A)

{` "These simplify to": for ! : A → 1, f^*(Y) is the constant family at
   Y(⋆) (by refl), f_!(X)(⋆) ≃ Σ_A X and f_*(X)(⋆) ≃ Π_A X, since ⋆ = ⋆ is
   contractible. `}
def family_terminal_map (A : Type) : A → Unit ≔ _ ↦ star.

def family_reindex_terminal (A : Type) (Y : Unit → Type)
  : Id (A → Type) (family_reindex_functor A Unit (family_terminal_map A) .obj Y)
      (family_constant_functor A .obj (Y star.))
  ≔ refl ((_ ↦ Y star.) : A → Type)

def family_sum_terminal_equiv (A : Type) (X : A → Type)
  : Equiv (FamilyPushSum A Unit (family_terminal_map A) X star.) (Σ A X)
  ≔ quasi_inverse_equiv (FamilyPushSum A Unit (family_terminal_map A) X star.) (Σ A X)
      (t ↦ (t .fst, t .snd .snd)) (t ↦ (t .fst, (refl (star. : Unit), t .snd)))
      (t ↦ refl ((w ↦ (t .fst, (w, t .snd .snd))) : Id Unit star. star. → FamilyPushSum A Unit (family_terminal_map A) X star.)
             (unit_set star. star. (refl (star. : Unit)) (t .snd .fst)))
      (t ↦ refl t)

def family_product_terminal_equiv (A : Type) (X : A → Type)
  : Equiv (FamilyPushProduct A Unit (family_terminal_map A) X star.) ((a : A) → X a)
  ≔ quasi_inverse_equiv (FamilyPushProduct A Unit (family_terminal_map A) X star.) ((a : A) → X a)
      (s a ↦ s a (refl (star. : Unit))) (m a _ ↦ m a)
      (s ↦ funext2 A (_ ↦ Id Unit star. star.) (a _ ↦ X a) (a _ ↦ s a (refl (star. : Unit))) s
        (a p ↦ refl (s a) (unit_set star. star. (refl (star. : Unit)) p)))
      (m ↦ refl m)

{` Litmus: for f = not : Bool → Bool, the unit of f_! ⊣ f^* sends x : X a
   to (a, refl, x), and the counit of Σ_Bool ⊣ cst evaluates. `}
def family_sum_litmus_unit (X : Bool → Type) (x : X true.)
  : Id (FamilyPushSum Bool Bool bool_not X false.)
      (adjunction_unit (FamilyWild Bool) (FamilyWild Bool) (family_sum_functor Bool Bool bool_not)
        (family_sum_right_adjoint Bool Bool bool_not) X true. x)
      (true., (refl (false. : Bool), x))
  ≔ refl ((true., (refl (false. : Bool), x)) : FamilyPushSum Bool Bool bool_not X false.)

def family_total_litmus_counit
  : Id Bool (adjunction_counit (FamilyWild Bool) TypeWild (family_total_functor Bool) (family_total_right_adjoint Bool)
      Bool (true., false.)) false.
  ≔ refl (false. : Bool)
