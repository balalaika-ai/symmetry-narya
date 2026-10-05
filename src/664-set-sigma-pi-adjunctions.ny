export "663-sigma-pi-adjunctions"

{` Chapter 6 (cats.tex), ex:Sigma-Pi-adj, the set-level version: for
   f : A → B the string of adjunctions f_! ⊣ f^* ⊣ f_* between the
   precategories Set^A and Set^B of families of sets, with
     f^*(Y) ≔ Y ∘ f,
     f_!(X)(b) ≔ ‖Σ_{a:A} (f(a) = b) × X(a)‖_0   (SetTrunc, module 43),
     f_*(X)(b) ≔ Π_{a:A} (f(a) = b) → X(a). `}

def SetPushSumCarrier (A B : Type) (f : A → B) (X : A → SetTypes) (b : B) : Type
  ≔ Σ A (a ↦ Product (Id B (f a) b) (X a .fst))

def set_family_sum_obj (A B : Type) (f : A → B) (X : A → SetTypes) : B → SetTypes
  ≔ b ↦ (SetTrunc (SetPushSumCarrier A B f X b), set_trunc_set (SetPushSumCarrier A B f X b))

def set_family_product_obj (A B : Type) (f : A → B) (X : A → SetTypes) : B → SetTypes
  ≔ b ↦ ((a : A) → Id B (f a) b → X a .fst,
         pi_set A (a ↦ Id B (f a) b → X a .fst) (a ↦ pi_set (Id B (f a) b) (_ ↦ X a .fst) (_ ↦ X a .snd)))

def set_family_reindex_functor (A B : Type) (f : A → B) : WildFunctor (FamilySetWild B) (FamilySetWild A)
  ≔ (obj ≔ Y ↦ a ↦ Y (f a),
     mor ≔ Y Y' g ↦ a ↦ g (f a),
     map_id ≔ Y ↦ refl ((a y ↦ y) : (a : A) → Y (f a) .fst → Y (f a) .fst),
     map_comp ≔ Y Y' Y'' g g' ↦ refl ((a y ↦ g' (f a) (g (f a) y)) : (a : A) → Y (f a) .fst → Y'' (f a) .fst))

def set_family_sum_mor (A B : Type) (f : A → B) (X X' : A → SetTypes) (g : (a : A) → X a .fst → X' a .fst)
  : (b : B) → SetTrunc (SetPushSumCarrier A B f X b) → SetTrunc (SetPushSumCarrier A B f X' b)
  ≔ b ↦ set_trunc_rec (SetPushSumCarrier A B f X b) (SetTrunc (SetPushSumCarrier A B f X' b))
      (set_trunc_set (SetPushSumCarrier A B f X' b))
      (t ↦ set_trunc (SetPushSumCarrier A B f X' b) (t .fst, (t .snd .fst, g (t .fst) (t .snd .snd))))

def set_family_sum_functor (A B : Type) (f : A → B) : WildFunctor (FamilySetWild A) (FamilySetWild B)
  ≔ (obj ≔ set_family_sum_obj A B f,
     mor ≔ set_family_sum_mor A B f,
     map_id ≔ X ↦
       let S ≔ SetPushSumCarrier A B f X in
       funext B (b ↦ SetTrunc (S b) → SetTrunc (S b)) (set_family_sum_mor A B f X X (a y ↦ y)) (b z ↦ z)
         (b ↦ set_trunc_rec_eta (S b) (SetTrunc (S b)) (set_trunc_set (S b)) (z ↦ z)),
     map_comp ≔ X X' X'' g g' ↦
       let S ≔ SetPushSumCarrier A B f X in
       let S'' ≔ SetPushSumCarrier A B f X'' in
       funext B (b ↦ SetTrunc (S b) → SetTrunc (S'' b))
         (set_family_sum_mor A B f X X'' (a y ↦ g' a (g a y)))
         (b z ↦ set_family_sum_mor A B f X' X'' g' b (set_family_sum_mor A B f X X' g b z))
         (b ↦ set_trunc_rec_eta (S b) (SetTrunc (S'' b)) (set_trunc_set (S'' b))
           (z ↦ set_family_sum_mor A B f X' X'' g' b (set_family_sum_mor A B f X X' g b z))))

def set_family_product_functor (A B : Type) (f : A → B) : WildFunctor (FamilySetWild A) (FamilySetWild B)
  ≔ (obj ≔ set_family_product_obj A B f,
     mor ≔ X X' g ↦ b s a p ↦ g a (s a p),
     map_id ≔ X ↦ refl ((b s ↦ s) : (b : B) → ((a : A) → Id B (f a) b → X a .fst) → (a : A) → Id B (f a) b → X a .fst),
     map_comp ≔ X X' X'' g g' ↦
       refl ((b s a p ↦ g' a (g a (s a p)))
         : (b : B) → ((a : A) → Id B (f a) b → X a .fst) → (a : A) → Id B (f a) b → X'' a .fst))

{` f_! ⊣ f^* for families of sets. The inverse transposition is defined
   on the set truncation by its recursion principle into the set Y(b). `}
def set_family_sum_transpose (A B : Type) (f : A → B) (X : A → SetTypes) (Y : B → SetTypes)
  (phi : (b : B) → SetTrunc (SetPushSumCarrier A B f X b) → Y b .fst) : (a : A) → X a .fst → Y (f a) .fst
  ≔ a x ↦ phi (f a) (set_trunc (SetPushSumCarrier A B f X (f a)) (a, (refl (f a), x)))

def set_family_sum_untranspose (A B : Type) (f : A → B) (X : A → SetTypes) (Y : B → SetTypes)
  (psi : (a : A) → X a .fst → Y (f a) .fst) : (b : B) → SetTrunc (SetPushSumCarrier A B f X b) → Y b .fst
  ≔ b ↦ set_trunc_rec (SetPushSumCarrier A B f X b) (Y b .fst) (Y b .snd)
      (t ↦ transport B (b' ↦ Y b' .fst) (f (t .fst)) b (t .snd .fst) (psi (t .fst) (t .snd .snd)))

def set_family_sum_transpose_is_iso (A B : Type) (f : A → B) (X : A → SetTypes) (Y : B → SetTypes)
  : CatIsIso TypeWild ((b : B) → SetTrunc (SetPushSumCarrier A B f X b) → Y b .fst)
      ((a : A) → X a .fst → Y (f a) .fst) (set_family_sum_transpose A B f X Y)
  ≔ let S ≔ SetPushSumCarrier A B f X in
    let HB ≔ (b : B) → SetTrunc (S b) → Y b .fst in
    let HA ≔ (a : A) → X a .fst → Y (f a) .fst in
    let Yf : B → Type ≔ b' ↦ Y b' .fst in
    ((set_family_sum_untranspose A B f X Y,
      funext HA (_ ↦ HA) (psi ↦ set_family_sum_transpose A B f X Y (set_family_sum_untranspose A B f X Y psi))
        (psi ↦ psi)
        (psi ↦ funext2 A (a ↦ X a .fst) (a _ ↦ Y (f a) .fst)
          (set_family_sum_transpose A B f X Y (set_family_sum_untranspose A B f X Y psi)) psi
          (a x ↦ transport_refl B Yf (f a) (psi a x)))),
     (set_family_sum_untranspose A B f X Y,
      funext HB (_ ↦ HB) (phi ↦ set_family_sum_untranspose A B f X Y (set_family_sum_transpose A B f X Y phi))
        (phi ↦ phi)
        (phi ↦ funext B (b ↦ SetTrunc (S b) → Y b .fst)
          (set_family_sum_untranspose A B f X Y (set_family_sum_transpose A B f X Y phi)) phi
          (b ↦ concat (SetTrunc (S b) → Y b .fst)
            (set_family_sum_untranspose A B f X Y (set_family_sum_transpose A B f X Y phi) b)
            (set_trunc_rec (S b) (Y b .fst) (Y b .snd) (t ↦ phi b (set_trunc (S b) t)))
            (phi b)
            (refl (set_trunc_rec (S b) (Y b .fst) (Y b .snd))
              (funext (S b) (_ ↦ Y b .fst)
                (t ↦ transport B Yf (f (t .fst)) b (t .snd .fst)
                       (set_family_sum_transpose A B f X Y phi (t .fst) (t .snd .snd)))
                (t ↦ phi b (set_trunc (S b) t))
                (t ↦ family_sum_transport_lemma A B f Yf (t .fst)
                       (b' p ↦ phi b' (set_trunc (S b') (t .fst, (p, t .snd .snd)))) b (t .snd .fst))))
            (set_trunc_rec_eta (S b) (Y b .fst) (Y b .snd) (phi b))))))

def set_family_sum_right_adjoint (A B : Type) (f : A → B)
  : RightAdjointData (FamilySetWild A) (FamilySetWild B) (set_family_sum_functor A B f)
  ≔ (right ≔ set_family_reindex_functor A B f,
     transpose ≔ set_family_sum_transpose A B f,
     transpose_iso ≔ set_family_sum_transpose_is_iso A B f,
     natural_left ≔ X X' g Y ↦
       refl ((k a x ↦ k (f a) (set_trunc (SetPushSumCarrier A B f X (f a)) (a, (refl (f a), g a x))))
         : ((b : B) → SetTrunc (SetPushSumCarrier A B f X b) → Y b .fst) → (a : A) → X' a .fst → Y (f a) .fst),
     natural_right ≔ X Y Y' h ↦
       refl ((k a x ↦ h (f a) (k (f a) (set_trunc (SetPushSumCarrier A B f X (f a)) (a, (refl (f a), x)))))
         : ((b : B) → SetTrunc (SetPushSumCarrier A B f X b) → Y b .fst) → (a : A) → X a .fst → Y' (f a) .fst))

def set_family_sum_adjunction (A B : Type) (f : A → B) : WildAdjunction (FamilySetWild A) (FamilySetWild B)
  ≔ (set_family_sum_functor A B f, set_family_sum_right_adjoint A B f)

{` f^* ⊣ f_* for families of sets. `}
def set_family_product_transpose (A B : Type) (f : A → B) (Y : B → SetTypes) (X : A → SetTypes)
  (psi : (a : A) → Y (f a) .fst → X a .fst) : (b : B) → Y b .fst → (a : A) → Id B (f a) b → X a .fst
  ≔ b y a p ↦ psi a (transport B (b' ↦ Y b' .fst) b (f a) (inverse B (f a) b p) y)

def set_family_product_untranspose (A B : Type) (f : A → B) (Y : B → SetTypes) (X : A → SetTypes)
  (chi : (b : B) → Y b .fst → (a : A) → Id B (f a) b → X a .fst) : (a : A) → Y (f a) .fst → X a .fst
  ≔ a y ↦ chi (f a) y a (refl (f a))

def set_family_product_transpose_is_iso (A B : Type) (f : A → B) (Y : B → SetTypes) (X : A → SetTypes)
  : CatIsIso TypeWild ((a : A) → Y (f a) .fst → X a .fst) ((b : B) → Y b .fst → (a : A) → Id B (f a) b → X a .fst)
      (set_family_product_transpose A B f Y X)
  ≔ let Yf : B → Type ≔ b' ↦ Y b' .fst in
    let Xf : A → Type ≔ a' ↦ X a' .fst in
    let HA ≔ (a : A) → Y (f a) .fst → X a .fst in
    let HB ≔ (b : B) → Y b .fst → (a : A) → Id B (f a) b → X a .fst in
    ((set_family_product_untranspose A B f Y X,
      funext HB (_ ↦ HB)
        (chi ↦ set_family_product_transpose A B f Y X (set_family_product_untranspose A B f Y X chi)) (chi ↦ chi)
        (chi ↦ funext3 B Yf (b _ ↦ A) (b _ a ↦ Id B (f a) b → X a .fst)
          (set_family_product_transpose A B f Y X (set_family_product_untranspose A B f Y X chi)) chi
          (b y a ↦ funext (Id B (f a) b) (_ ↦ X a .fst)
            (set_family_product_transpose A B f Y X (set_family_product_untranspose A B f Y X chi) b y a) (chi b y a)
            (p ↦ family_product_transport_lemma A B f Yf Xf chi a b p y)))),
     (set_family_product_untranspose A B f Y X,
      funext HA (_ ↦ HA)
        (psi ↦ set_family_product_untranspose A B f Y X (set_family_product_transpose A B f Y X psi)) (psi ↦ psi)
        (psi ↦ funext2 A (a ↦ Y (f a) .fst) (a _ ↦ X a .fst)
          (set_family_product_untranspose A B f Y X (set_family_product_transpose A B f Y X psi)) psi
          (a y ↦ refl (psi a) (family_transport_inverse_refl B Yf (f a) y)))))

def set_family_product_right_adjoint (A B : Type) (f : A → B)
  : RightAdjointData (FamilySetWild B) (FamilySetWild A) (set_family_reindex_functor A B f)
  ≔ (right ≔ set_family_product_functor A B f,
     transpose ≔ set_family_product_transpose A B f,
     transpose_iso ≔ set_family_product_transpose_is_iso A B f,
     natural_left ≔ Y Y' g X ↦
       let Yf : B → Type ≔ b' ↦ Y b' .fst in
       let Yf' : B → Type ≔ b' ↦ Y' b' .fst in
       let HA ≔ (a : A) → Y (f a) .fst → X a .fst in
       let T ≔ (b : B) → Y' b .fst → (a : A) → Id B (f a) b → X a .fst in
       let L : HA → T ≔ k b y' a p ↦ k a (transport B Yf b (f a) (inverse B (f a) b p) (g b y')) in
       let R : HA → T ≔ k b y' a p ↦ k a (g (f a) (transport B Yf' b (f a) (inverse B (f a) b p) y')) in
       funext HA (_ ↦ T) L R
         (k ↦ funext3 B Yf' (b _ ↦ A) (b _ a ↦ Id B (f a) b → X a .fst) (L k) (R k)
           (b y' a ↦ funext (Id B (f a) b) (_ ↦ X a .fst) (L k b y' a) (R k b y' a)
             (p ↦ refl (k a) (family_transport_natural B Yf Yf' g b (f a) (inverse B (f a) b p) y')))),
     natural_right ≔ Y X X' h ↦
       refl ((k b y a p ↦ h a (k a (transport B (b' ↦ Y b' .fst) b (f a) (inverse B (f a) b p) y)))
         : ((a : A) → Y (f a) .fst → X a .fst) → (b : B) → Y b .fst → (a : A) → Id B (f a) b → X' a .fst))

def set_family_product_adjunction (A B : Type) (f : A → B) : WildAdjunction (FamilySetWild B) (FamilySetWild A)
  ≔ (set_family_reindex_functor A B f, set_family_product_right_adjoint A B f)

{` Litmus: for ! : Bool → 1 and the constant family of Bool, the unit of
   f_! ⊣ f^* lands in the set truncation of the triple (a, refl, x), and
   f_* evaluated at ⋆ applied to a section returns its value. `}
def set_family_litmus_family : Bool → SetTypes ≔ _ ↦ (Bool, bool_set)

def set_family_litmus_unit (x : Bool)
  : Id (SetTrunc (SetPushSumCarrier Bool Unit (family_terminal_map Bool) set_family_litmus_family star.))
      (adjunction_unit (FamilySetWild Bool) (FamilySetWild Unit) (set_family_sum_functor Bool Unit (family_terminal_map Bool))
        (set_family_sum_right_adjoint Bool Unit (family_terminal_map Bool)) set_family_litmus_family true. x)
      (set_trunc (SetPushSumCarrier Bool Unit (family_terminal_map Bool) set_family_litmus_family star.)
        (true., (refl (star. : Unit), x)))
  ≔ refl (set_trunc (SetPushSumCarrier Bool Unit (family_terminal_map Bool) set_family_litmus_family star.)
        (true., (refl (star. : Unit), x)))

def set_family_litmus_counit
  : Id Bool (adjunction_counit (FamilySetWild Unit) (FamilySetWild Bool)
      (set_family_reindex_functor Bool Unit (family_terminal_map Bool))
      (set_family_product_right_adjoint Bool Unit (family_terminal_map Bool))
      set_family_litmus_family false. (a _ ↦ a))
      false.
  ≔ refl (false. : Bool)
