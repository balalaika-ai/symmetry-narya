export "39-propositional-images"

def precompose (A B Y : Type) (p : A → B) (f : B → Y) : A → Y ≔ a ↦ f (p a)

def two_sets_path (S T : TwoSets) (p : Id Type (two_sets_carrier S) (two_sets_carrier T))
  : Id TwoSets S T
  ≔ subtype_equal SetTypes (X ↦ TwoElement (X .fst)) (X ↦ two_element_prop (X .fst)) S T
      (subtype_equal Type isSet isset_isprop (S .fst) (T .fst) p)

def two_sets_base_inclusion : Unit → TwoSets ≔ _ ↦ bool_two_set

def two_sets_base_surjective : Surjective Unit TwoSets two_sets_base_inclusion
  ≔ S ↦ trunc_map native_truncation (Id Type (Fin two) (two_sets_carrier S))
      (BookFiber Unit TwoSets two_sets_base_inclusion S)
      (p ↦ (star., two_sets_path S bool_two_set
        (concat Type (two_sets_carrier S) (Fin two) Bool
          (inverse Type (Fin two) (two_sets_carrier S) p) fin_two_path))) (S .snd)

def two_sets_constant_bool : TwoSets → Type ≔ _ ↦ Bool

def two_sets_carrier_not_constant
  (p : Id (TwoSets → Type) two_sets_carrier two_sets_constant_bool) : Empty
  ≔ two_sets_no_global_identification (S ↦ concat Type (two_sets_carrier S) Bool (Fin two)
      (p (refl S)) (inverse Type (Fin two) Bool fin_two_path))

def two_sets_restrictions_equal
  : Id (Unit → Type)
      (precompose Unit TwoSets Type two_sets_base_inclusion two_sets_carrier)
      (precompose Unit TwoSets Type two_sets_base_inclusion two_sets_constant_bool)
  ≔ refl ((_ ↦ Bool) : Unit → Type)

{` Counterexample to the printed xca:cancel-surjection (circle.tex, line 3104).
   The inclusion of the base point in TwoSets is surjective. The carrier
   family and constant Bool agree at that point but are not equal globally.
   Thus ap(precompose p) is not an equivalence for the target Y = Type. `}
def surjection_cancellation_universe_counterexample
  (e : isEquiv (Id (TwoSets → Type) two_sets_carrier two_sets_constant_bool)
      (Id (Unit → Type)
        (precompose Unit TwoSets Type two_sets_base_inclusion two_sets_carrier)
        (precompose Unit TwoSets Type two_sets_base_inclusion two_sets_constant_bool))
      (map_path (TwoSets → Type) (Unit → Type) (precompose Unit TwoSets Type two_sets_base_inclusion)
        two_sets_carrier two_sets_constant_bool)) : Empty
  ≔ two_sets_carrier_not_constant (e two_sets_restrictions_equal .center .fst)

{` The same obstruction already occurs when the target is the groupoid TwoSets. `}
def two_sets_groupoid : isGroupoid TwoSets
  ≔ hlevel_to_groupoid TwoSets
      (subtype_hlevel (suc. (suc. zero.)) SetTypes (S ↦ TwoElement (S .fst))
        (groupoid_to_hlevel SetTypes sets_groupoid) (S ↦ two_element_prop (S .fst)))

def two_sets_constant_base : TwoSets → TwoSets ≔ _ ↦ bool_two_set

def two_sets_identity_not_constant
  (q : Id (TwoSets → TwoSets) (identity TwoSets) two_sets_constant_base) : Empty
  ≔ two_sets_carrier_not_constant (refl ((f ↦ compose TwoSets TwoSets Type two_sets_carrier f)
      : (TwoSets → TwoSets) → (TwoSets → Type)) q)

def two_sets_base_restrictions_equal
  : Id (Unit → TwoSets)
      (precompose Unit TwoSets TwoSets two_sets_base_inclusion (identity TwoSets))
      (precompose Unit TwoSets TwoSets two_sets_base_inclusion two_sets_constant_base)
  ≔ refl two_sets_base_inclusion

def surjection_cancellation_counterexample
  (e : isEquiv (Id (TwoSets → TwoSets) (identity TwoSets) two_sets_constant_base)
      (Id (Unit → TwoSets)
        (precompose Unit TwoSets TwoSets two_sets_base_inclusion (identity TwoSets))
        (precompose Unit TwoSets TwoSets two_sets_base_inclusion two_sets_constant_base))
      (map_path (TwoSets → TwoSets) (Unit → TwoSets) (precompose Unit TwoSets TwoSets two_sets_base_inclusion)
        (identity TwoSets) two_sets_constant_base)) : Empty
  ≔ two_sets_identity_not_constant (e two_sets_base_restrictions_equal .center .fst)

{` A valid restricted statement: the target Y is a set. `}
def surjection_homotopy_from_restriction (A B Y : Type) (p : A → B)
  (hp : Surjective A B p) (hy : isSet Y) (f g : B → Y)
  (q : Id (A → Y) (precompose A B Y p f) (precompose A B Y p g)) (b : B) : Id Y (f b) (g b)
  ≔ mere_rec (BookFiber A B p b) (Id Y (f b) (g b)) (hy (f b) (g b))
      (w ↦ concat Y (f b) (f (p (w .fst))) (g b)
        (map_path B Y f b (p (w .fst)) (w .snd))
        (concat Y (f (p (w .fst))) (g (p (w .fst))) (g b) (q (refl (w .fst)))
          (inverse Y (g b) (g (p (w .fst))) (map_path B Y g b (p (w .fst)) (w .snd))))) (hp b)

def cancel_surjection_into_set (A B Y : Type) (p : A → B) (hp : Surjective A B p) (hy : isSet Y)
  (f g : B → Y)
  : Equiv (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g))
  ≔ iff_equiv (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g))
      (pi_set B (_ ↦ Y) (_ ↦ hy) f g)
      (pi_set A (_ ↦ Y) (_ ↦ hy) (precompose A B Y p f) (precompose A B Y p g))
      (map_path (B → Y) (A → Y) (precompose A B Y p) f g)
      (q ↦ funext B (_ ↦ Y) f g (surjection_homotopy_from_restriction A B Y p hp hy f g q))

def pi_equiv (X : Type) (P Q : X → Type) (e : (x : X) → Equiv (P x) (Q x))
  : Equiv ((x : X) → P x) ((x : X) → Q x)
  ≔ quasi_inverse_equiv ((x : X) → P x) ((x : X) → Q x)
      (f x ↦ e x .map (f x)) (g x ↦ equiv_inverse_map (P x) (Q x) (e x) (g x))
      (f ↦ funext X P (x ↦ equiv_inverse_map (P x) (Q x) (e x) (e x .map (f x))) f
        (x ↦ equiv_retraction (P x) (Q x) (e x) (f x)))
      (g ↦ funext X Q (x ↦ e x .map (equiv_inverse_map (P x) (Q x) (e x) (g x))) g
        (x ↦ equiv_counit (P x) (Q x) (e x) (g x)))

def funext_equiv (X : Type) (P : X → Type) (f g : (x : X) → P x)
  : Equiv (Homotopy X P f g) (Id ((x : X) → P x) f g)
  ≔ quasi_inverse_equiv (Homotopy X P f g) (Id ((x : X) → P x) f g)
      (funext X P f g) (happly X P f g) (funext_beta_function X P f g) (funext_eta X P f g)

{` xca:cancel-injection. This statement is valid for arbitrary types. `}
def cancel_injection (A B X : Type) (i : A → B) (hi : IsEmbedding A B i) (f g : X → A)
  : Equiv (Id (X → A) f g) (Id (X → B) (compose X A B i f) (compose X A B i g))
  ≔ let F ≔ compose X A B i f in let G ≔ compose X A B i g in
    let e ≔ compose_equiv (Id (X → A) f g) (Homotopy X (_ ↦ A) f g) (Id (X → B) F G)
      (function_extensionality X (_ ↦ A) f g)
      (compose_equiv (Homotopy X (_ ↦ A) f g) (Homotopy X (_ ↦ B) F G) (Id (X → B) F G)
        (pi_equiv X (x ↦ Id A (f x) (g x)) (x ↦ Id B (F x) (G x))
          (x ↦ native_equivalence (Id A (f x) (g x)) (Id B (F x) (G x))
            (embedding_on_paths A B i hi (f x) (g x))))
        (funext_equiv X (_ ↦ B) F G)) in
    equiv_change_map (Id (X → A) f g) (Id (X → B) F G) e
      (map_path (X → A) (X → B) (compose X A B i) f g)
      (p ↦ funext_eta X (_ ↦ B) F G (map_path (X → A) (X → B) (compose X A B i) f g p))
