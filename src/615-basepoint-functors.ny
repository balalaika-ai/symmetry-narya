export "604-wild-pointed-types"

{` Chapter 6 (cats.tex): ex:add-remove-basepoint (the wild functors
   (-)_+ : U → U_* and (-)_÷ : U_* → U), ex:pt-unpt-unit (the natural
   transformation η : id_U → ((-)_+)_÷ given by inl) and ex:pt-unpt-adj
   (the adjunction (-)_+ ⊣ (-)_÷). A_+ = (A ⊔ 1, inr *) is plus_pointed
   of module 162. `}

{` ex:add-remove-basepoint: f_+(inl a) ≔ inl f(a), f_+(pt) ≔ pt; the
   pointing path is reflexivity. `}
def plus_map (A B : Type) (f : A → B) : Sum A Unit → Sum B Unit
  ≔ [ inl. a ↦ inl. (f a) | inr. _ ↦ inr. star. ]

def plus_pointed_map (A B : Type) (f : A → B) : BookPointedMap (plus_pointed A) (plus_pointed B)
  ≔ (plus_map A B f, refl (inr. star. : Sum B Unit))

def plus_map_id (A : Type)
  : Id (BookPointedMap (plus_pointed A) (plus_pointed A)) (plus_pointed_map A A (x ↦ x))
      (book_pointed_identity (plus_pointed A))
  ≔ let X ≔ plus_pointed A in
    equiv_inverse_map (Id (BookPointedMap X X) (plus_pointed_map A A (x ↦ x)) (book_pointed_identity X))
      (PointedHomotopy X X (plus_pointed_map A A (x ↦ x)) (book_pointed_identity X))
      (pointed_map_path_equiv X X (plus_pointed_map A A (x ↦ x)) (book_pointed_identity X))
      ([ inl. a ↦ refl (inl. a : Sum A Unit) | inr. u ↦ match u [ star. ↦ refl (inr. star. : Sum A Unit) ] ],
       concat_p1 (Sum A Unit) (inr. star.) (inr. star.) (refl (inr. star. : Sum A Unit)))

def plus_map_comp (A B C : Type) (f : A → B) (g : B → C)
  : Id (BookPointedMap (plus_pointed A) (plus_pointed C)) (plus_pointed_map A C (x ↦ g (f x)))
      (book_pointed_compose (plus_pointed A) (plus_pointed B) (plus_pointed C)
        (plus_pointed_map A B f) (plus_pointed_map B C g))
  ≔ let X ≔ plus_pointed A in
    let Z ≔ plus_pointed C in
    let lhs ≔ plus_pointed_map A C (x ↦ g (f x)) in
    let rhs ≔ book_pointed_compose X (plus_pointed B) Z (plus_pointed_map A B f) (plus_pointed_map B C g) in
    equiv_inverse_map (Id (BookPointedMap X Z) lhs rhs) (PointedHomotopy X Z lhs rhs)
      (pointed_map_path_equiv X Z lhs rhs)
      ([ inl. a ↦ refl (inl. (g (f a)) : Sum C Unit) | inr. u ↦ match u [ star. ↦ refl (inr. star. : Sum C Unit) ] ],
       refl (rhs .snd))

def PlusFunctor : WildFunctor TypeWild PointedWild
  ≔ (obj ≔ A ↦ plus_pointed A,
     mor ≔ A B f ↦ plus_pointed_map A B f,
     map_id ≔ A ↦ plus_map_id A,
     map_comp ≔ A B C f g ↦ plus_map_comp A B C f g)

{` ex:add-remove-basepoint: taking underlying types, (-)_÷ : U_* → U. `}
def ForgetBasepointFunctor : WildFunctor PointedWild TypeWild
  ≔ (obj ≔ X ↦ X .carrier,
     mor ≔ X Y f ↦ f .fst,
     map_id ≔ X ↦ refl ((x ↦ x) : X .carrier → X .carrier),
     map_comp ≔ X Y Z f g ↦ refl ((x ↦ g .fst (f .fst x)) : X .carrier → Z .carrier))

{` ex:pt-unpt-unit: η : id_U → ((-)_+)_÷ with components inl : A → A ⊔ 1;
   the naturality squares commute by reflexivity. `}
def plus_forget_unit
  : WildNatTrans TypeWild TypeWild (functor_identity TypeWild)
      (functor_compose TypeWild PointedWild TypeWild ForgetBasepointFunctor PlusFunctor)
  ≔ (component ≔ A ↦ x ↦ inl. x,
     natural ≔ A B f ↦ refl ((x ↦ inl. (f x)) : A → Sum B Unit))

def plus_forget_objects (A : Type)
  : Id Type (functor_compose TypeWild PointedWild TypeWild ForgetBasepointFunctor PlusFunctor .obj A) (Sum A Unit)
  ≔ refl (Sum A Unit)

{` ex:pt-unpt-adj: (-)_+ ⊣ (-)_÷, with α : (A_+ →* X) ≃ (A → X_÷) given by
   precomposition with inl. The book types this as "A : U_* and X : U";
   the roles are swapped: A : U and X : U_*. The inverse is the extension
   of xca:plusforgetadjoint (plus_extend, module 162). Both naturality
   conditions hold judgmentally. `}
def plus_forget_right_adjoint : RightAdjointData TypeWild PointedWild PlusFunctor
  ≔ (right ≔ ForgetBasepointFunctor,
     transpose ≔ A X g ↦ plus_restrict A X g,
     transpose_iso ≔ A X ↦
       ((plus_extend A X, refl ((h ↦ h) : (A → X .carrier) → A → X .carrier)),
        (plus_extend A X,
         funext (BookPointedMap (plus_pointed A) X) (_ ↦ BookPointedMap (plus_pointed A) X)
           (g ↦ plus_extend A X (plus_restrict A X g)) (g ↦ g) (plus_extend_restrict A X))),
     natural_left ≔ A A' f X ↦
       refl ((g ↦ x ↦ g .fst (inl. (f x))) : BookPointedMap (plus_pointed A) X → A' → X .carrier),
     natural_right ≔ A X X' h ↦
       refl ((g ↦ x ↦ h .fst (g .fst (inl. x))) : BookPointedMap (plus_pointed A) X → A → X' .carrier))

def PlusForgetAdjunction : WildAdjunction TypeWild PointedWild
  ≔ (left ≔ PlusFunctor, right_adjoint ≔ plus_forget_right_adjoint)

{` The displayed α : (A_+ →* X) ≃ (A → X_÷), for A : U and X : U_*. `}
def plus_forget_transpose_equiv (A : Type) (X : Pointed)
  : BookEquiv (BookPointedMap (plus_pointed A) X) (A → X .carrier)
  ≔ book_equivalence (BookPointedMap (plus_pointed A) X) (A → X .carrier)
      (adjunction_transpose_equiv TypeWild PointedWild PlusFunctor plus_forget_right_adjoint A X)

def plus_forget_transpose_map (A : Type) (X : Pointed)
  : Id (BookPointedMap (plus_pointed A) X → A → X .carrier) (plus_forget_transpose_equiv A X .map)
      (g ↦ a ↦ g .fst (inl. a))
  ≔ refl ((g ↦ a ↦ g .fst (inl. a)) : BookPointedMap (plus_pointed A) X → A → X .carrier)

{` The unit of the adjunction is the natural transformation η above. `}
def plus_forget_adjunction_unit (A : Type)
  : Id (A → Sum A Unit) (adjunction_unit TypeWild PointedWild PlusFunctor plus_forget_right_adjoint A)
      (plus_forget_unit .component A)
  ≔ refl ((x ↦ inl. x) : A → Sum A Unit)

{` Litmus checks: (bool_not)_+ fixes the added point and negates the
   rest; the transpose of a pointed map out of Bool_+ is its restriction. `}
def plus_map_bool_point : Id (Sum Bool Unit) (PlusFunctor .mor Bool Bool bool_not .fst (inr. star.)) (inr. star.)
  ≔ refl (inr. star. : Sum Bool Unit)

def plus_map_bool_value : Id (Sum Bool Unit) (PlusFunctor .mor Bool Bool bool_not .fst (inl. true.)) (inl. false.)
  ≔ refl (inl. false. : Sum Bool Unit)

def plus_forget_transpose_value (g : BookPointedMap (plus_pointed Bool) pointed_bool_true)
  : Id Bool (plus_forget_right_adjoint .transpose Bool pointed_bool_true g false.) (g .fst (inl. false.))
  ≔ refl (g .fst (inl. false.))
