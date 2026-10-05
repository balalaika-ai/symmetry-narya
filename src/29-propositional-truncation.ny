export "28-winding-number"

{` Impredicative propositional truncation in Narya's single native Type.
   This constructs an inhabitant of TruncationSignature. It does NOT
   implement a universe-preserving HIT in a predicative hierarchy.
   Nondependent beta is judgmental; dependent beta below is propositional. `}
def Mere (A : Type) : Type ≔ (P : Type) → isProp P → (A → P) → P

def mere (A : Type) (a : A) : Mere A ≔ P h f ↦ f a

def mere_isprop (A : Type) : isProp (Mere A)
  ≔ pi_prop Type (P ↦ isProp P → (A → P) → P)
      (P ↦ pi_prop (isProp P) (_ ↦ (A → P) → P)
        (h ↦ pi_prop (A → P) (_ ↦ P) (_ ↦ h)))

def mere_rec (A P : Type) (h : isProp P) (f : A → P) (t : Mere A) : P ≔ t P h f

def mere_rec_beta (A P : Type) (h : isProp P) (f : A → P) (a : A)
  : Id P (mere_rec A P h f (mere A a)) (f a) ≔ refl (f a)

def mere_eliminate (A : Type) (P : Mere A → Type) (h : (t : Mere A) → isProp (P t))
  (f : (a : A) → P (mere A a)) (t : Mere A) : P t
  ≔ mere_rec A (P t) (h t)
      (a ↦ transport (Mere A) P (mere A a) t (mere_isprop A (mere A a) t) (f a)) t

def mere_eliminate_beta (A : Type) (P : Mere A → Type) (h : (t : Mere A) → isProp (P t))
  (f : (a : A) → P (mere A a)) (a : A)
  : Id (P (mere A a)) (mere_eliminate A P h f (mere A a)) (f a)
  ≔ h (mere A a) (mere_eliminate A P h f (mere A a)) (f a)

def native_truncation : TruncationSignature ≔ (Mere, mere, mere_isprop, mere_eliminate)

def mere_universal_property (A P : Type) (h : isProp P)
  : BookEquiv (Mere A → P) (A → P)
  ≔ book_quasi_inverse_equiv (Mere A → P) (A → P)
      (f a ↦ f (mere A a)) (mere_rec A P h)
      (f ↦ funext (Mere A) (_ ↦ P) (mere_rec A P h (a ↦ f (mere A a))) f
        (t ↦ h (mere_rec A P h (a ↦ f (mere A a)) t) (f t)))
      (f ↦ refl f)

{` The unnumbered existence exercise following the logic definitions. `}
def mere_has_representative (A : Type) (t : Mere A)
  : Mere (Σ A (a ↦ Id (Mere A) t (mere A a)))
  ≔ mere_rec A (Mere (Σ A (a ↦ Id (Mere A) t (mere A a))))
      (mere_isprop (Σ A (a ↦ Id (Mere A) t (mere A a))))
      (a ↦ mere (Σ A (a ↦ Id (Mere A) t (mere A a))) (a, mere_isprop A t (mere A a))) t

def mere_proposition_equiv (P : Type) (h : isProp P) : Equiv P (Mere P)
  ≔ trunc_prop_equiv native_truncation P h

def Connected (A : Type) : Type ≔ IsConnected native_truncation A
def NativeComponent (A : Type) (a : A) : Type ≔ Component native_truncation A a
def Surjective (A B : Type) (f : A → B) : Type ≔ IsSurjection native_truncation A B f

def native_component_connected (A : Type) (a : A) : Connected (NativeComponent A a)
  ≔ component_connected native_truncation A a

def native_circle_connected (C : CircleSignature) : Connected (C .carrier)
  ≔ circle_is_connected native_truncation C

def native_connected_set_contractible (A : Type) (hA : Connected A) (sA : isSet A) : BookIsContr A
  ≔ connected_set_contractible native_truncation A hA sA

def native_embedding_surjection_equiv (A B : Type) (f : A → B)
  (i : IsEmbedding A B f) (s : Surjective A B f) : BookEquiv A B
  ≔ embedding_surjection_equiv native_truncation A B f i s
