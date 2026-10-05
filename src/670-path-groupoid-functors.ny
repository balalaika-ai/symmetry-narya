export "617-path-groupoid-functors"

{` Chapter 6, section 6.8 (cats.tex, thm:1types-are-groupoids, first part).
   For types A and B, the functors between the path groupoids PathWild A and
   PathWild B (ex:path-groupoid). Unfolded, such a functor is
     Σ (f : A → B) Σ (g : (x y : A) → (x = y) → (f x = f y)),
       (Π x, g(refl x) = refl (f x)) × (Π x y z p q, g(p · q) = g(p) · g(q)),
   (functor_sigma_equiv in 602; recall that q ∘ p = p · q in PathWild).
   When B is a 1-type the bracketed components are propositions
   (functor_laws_prop), g is determined by its value on reflexivities
   (path_family_refl_equiv), and the first bracketed component nails it
   down (path_functor_action_contractible), so only f remains. `}

{` The displayed unfolding of [A, B] (the book's ≡): both round trips
   are reflexivities, by eta for records. Here g(qp) is g(p · q). `}
def PathFunctorUnfolded (A B : Type) : Type
  ≔ Σ (A → B) (f ↦ Σ ((x y : A) → Id A x y → Id B (f x) (f y)) (g ↦
      Product ((x : A) → Id (Id B (f x) (f x)) (g x x (refl x)) (refl (f x)))
        ((x y z : A) (p : Id A x y) (q : Id A y z)
          → Id (Id B (f x) (f z)) (g x z (concat A x y z p q)) (concat B (f x) (f y) (f z) (g x y p) (g y z q)))))

def path_functor_unfolded_equiv (A B : Type)
  : Equiv (WildFunctor (PathWild A) (PathWild B)) (PathFunctorUnfolded A B)
  ≔ quasi_inverse_equiv (WildFunctor (PathWild A) (PathWild B)) (PathFunctorUnfolded A B)
      (F ↦ (F .obj, (F .mor, (F .map_id, F .map_comp))))
      (u ↦ (obj ≔ u .fst, mor ≔ u .snd .fst, map_id ≔ u .snd .snd .fst, map_comp ≔ u .snd .snd .snd))
      (F ↦ refl F) (u ↦ refl u)

{` The path functor of a map, ap on arrows, is path_wild_functor of
   module 617 (ex:path-gpd-nat): F(refl x) = refl (f x) holds
   definitionally and F(p · q) = F p · F q is map_path_concat. `}

{` "By path induction, g is determined by its action on reflexivity":
   evaluation at reflexivities is an equivalence
   (Π x y, (x = y) → P x y) ≃ (Π x, P x x). `}
def path_family_refl_eval (A : Type) (P : A → A → Type) (g : (x y : A) → Id A x y → P x y)
  : (x : A) → P x x
  ≔ x ↦ g x x (refl x)

def path_family_extend (A : Type) (P : A → A → Type) (h : (x : A) → P x x)
  : (x y : A) → Id A x y → P x y
  ≔ x y p ↦ J A x (y _ ↦ P x y) (h x) y p

def path_family_extend_eval (A : Type) (P : A → A → Type) (g : (x y : A) → Id A x y → P x y)
  (x y : A) (p : Id A x y)
  : Id (P x y) (path_family_extend A P (path_family_refl_eval A P g) x y p) (g x y p)
  ≔ J A x (y p ↦ Id (P x y) (path_family_extend A P (path_family_refl_eval A P g) x y p) (g x y p))
      (inverse (P x x) (g x x (refl x)) (J A x (y _ ↦ P x y) (g x x (refl x)) x (refl x))
        (Jβ A x (y _ ↦ P x y) (g x x (refl x))))
      y p

def path_family_refl_equiv (A : Type) (P : A → A → Type)
  : Equiv ((x y : A) → Id A x y → P x y) ((x : A) → P x x)
  ≔ quasi_inverse_equiv ((x y : A) → Id A x y → P x y) ((x : A) → P x x)
      (path_family_refl_eval A P) (path_family_extend A P)
      (g ↦ funext3 A (_ ↦ A) (x y ↦ Id A x y) (x y _ ↦ P x y)
        (path_family_extend A P (path_family_refl_eval A P g)) g (path_family_extend_eval A P g))
      (h ↦ funext A (x ↦ P x x) (x ↦ J A x (y _ ↦ P x y) (h x) x (refl x)) h
        (x ↦ inverse (P x x) (h x) (J A x (y _ ↦ P x y) (h x) x (refl x)) (Jβ A x (y _ ↦ P x y) (h x))))

{` "The first bracketed component nails it down": for every f, the type of
   actions g on paths together with the identity law is contractible
   (its centre is ap f). `}
def PathActionWithUnit (A B : Type) (f : A → B) : Type
  ≔ Σ ((x y : A) → Id A x y → Id B (f x) (f y))
      (g ↦ (x : A) → Id (Id B (f x) (f x)) (g x x (refl x)) (refl (f x)))

def path_functor_action_contractible (A B : Type) (f : A → B) : isContr (PathActionWithUnit A B f)
  ≔ let P : A → A → Type ≔ x y ↦ Id B (f x) (f y) in
    let Q : ((x : A) → P x x) → Type ≔ h ↦ (x : A) → Id (P x x) (h x) (refl (f x)) in
    hlevel_equiv zero. ((x : A) → Σ (P x x) (u ↦ Id (P x x) u (refl (f x)))) (PathActionWithUnit A B f)
      (compose_equiv ((x : A) → Σ (P x x) (u ↦ Id (P x x) u (refl (f x))))
        (Σ ((x : A) → P x x) Q) (PathActionWithUnit A B f)
        (choice_equiv A (x ↦ P x x) (x u ↦ Id (P x x) u (refl (f x))))
        (canonical_inverse_equiv (PathActionWithUnit A B f) (Σ ((x : A) → P x x) Q)
          (sigma_pullback_equiv ((x y : A) → Id A x y → P x y) ((x : A) → P x x)
            (path_family_refl_equiv A P) Q)))
      (pi_contractible A (x ↦ Σ (P x x) (u ↦ Id (P x x) u (refl (f x))))
        (x ↦ path_to_contractible (P x x) (refl (f x))))

{` "Here, the two bracketed components are propositions" (B a 1-type, so
   that the path groupoid of B has hom-sets). `}
def path_functor_laws_prop (A B : Type) (hB : isGroupoid B) (t : FunctorData (PathWild A) (PathWild B))
  : isProp (FunctorLaws (PathWild A) (PathWild B) t)
  ≔ functor_laws_prop (PathWild A) (PathWild B) hB t

{` Every functor between path groupoids acts on arrows by ap of its object
   part, by path induction from F(refl) = refl. `}
def path_functor_mor_ap (A B : Type) (F : WildFunctor (PathWild A) (PathWild B)) (x y : A) (p : Id A x y)
  : Id (Id B (F .obj x) (F .obj y)) (refl (F .obj) p) (F .mor x y p)
  ≔ J A x (y p ↦ Id (Id B (F .obj x) (F .obj y)) (refl (F .obj) p) (F .mor x y p))
      (inverse (Id B (F .obj x) (F .obj x)) (F .mor x x (refl x)) (refl (F .obj x)) (F .map_id x))
      y p

def path_functor_eta (A B : Type) (hB : isGroupoid B) (F : WildFunctor (PathWild A) (PathWild B))
  : Id (WildFunctor (PathWild A) (PathWild B)) (path_wild_functor A B (F .obj)) F
  ≔ functor_path (PathWild A) (PathWild B) hB (path_wild_functor A B (F .obj)) F
      (refl (F .obj),
       funext3 A (_ ↦ A) (x y ↦ Id A x y) (x y _ ↦ Id B (F .obj x) (F .obj y))
         (x y p ↦ refl (F .obj) p) (F .mor) (path_functor_mor_ap A B F))

{` thm:1types-are-groupoids, first sentence: for a 1-type B (and any A), the
   projection F ↦ F₀ from functors of path groupoids [A, B] to A → B is an
   equivalence, with inverse the path functor. `}
def path_groupoid_functors_equiv (A B : Type) (hB : isGroupoid B)
  : Equiv (WildFunctor (PathWild A) (PathWild B)) (A → B)
  ≔ quasi_inverse_equiv (WildFunctor (PathWild A) (PathWild B)) (A → B)
      (F ↦ F .obj) (path_wild_functor A B) (path_functor_eta A B hB) (f ↦ refl f)

{` The statement as printed: for 1-types A and B the projection from the
   functors [A, B] of the path groupoids to (A → B) is an equivalence (the
   hypothesis on A is not needed). `}
def one_types_functor_projection_equiv (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  : BookIsEquiv (WildFunctor (PathWild A) (PathWild B)) (A → B) (F ↦ F .obj)
  ≔ book_equivalence (WildFunctor (PathWild A) (PathWild B)) (A → B)
      (path_groupoid_functors_equiv A B hB) .equiv

{` The same, with the precategory [A, B] = FunctorPrecat of def:functor-cat:
   its objects are exactly these functors. `}
def path_precat (B : Type) (hB : isGroupoid B) : Precat ≔ (PathWild B, hB)

def one_types_functor_precat_objects
  (A B : Type) (hB : isGroupoid B)
  : Id Type (FunctorPrecat (PathWild A) (path_precat B hB) .wild .ob) (WildFunctor (PathWild A) (PathWild B))
  ≔ refl (WildFunctor (PathWild A) (PathWild B))

{` Litmus: the path functor of negation on Bool sends refl to refl and its
   object part is negation; the round trip on maps is the identity. `}
def path_functor_bool_not_obj
  : Id Bool (path_wild_functor Bool Bool bool_not .obj true.) false.
  ≔ refl (false. : Bool)

def path_functor_round_trip (A B : Type) (hB : isGroupoid B) (f : A → B)
  : Id (A → B) (path_groupoid_functors_equiv A B hB .map (path_wild_functor A B f)) f
  ≔ refl f
