export "603-adjunctions-and-equivalences"

{` Chapter 6 (cats.tex), ex:path-gpd-nat: a function f : A → B is a wild
   functor between the wild path groupoids (ex:path-groupoid, PathWild,
   composition q ∘ p = p · q) acting on arrows by ap_f, and a family of
   identifications h : ∏_x f(x) = g(x) is a wild natural transformation
   whose naturality squares are those of def:naturality-square
   (naturality, module 04). `}

def path_wild_functor (A B : Type) (f : A → B) : WildFunctor (PathWild A) (PathWild B)
  ≔ (obj ≔ f,
     mor ≔ x y p ↦ refl f p,
     map_id ≔ x ↦ refl (refl (f x)),
     map_comp ≔ x y z p q ↦ map_path_concat A B f x y z p q)

def path_wild_nat_trans (A B : Type) (f g : A → B) (h : (x : A) → Id B (f x) (g x))
  : WildNatTrans (PathWild A) (PathWild B) (path_wild_functor A B f) (path_wild_functor A B g)
  ≔ (component ≔ h,
     natural ≔ x y p ↦ inverse (Id B (f x) (g y))
       (concat B (f x) (f y) (g y) (refl f p) (h y)) (concat B (f x) (g x) (g y) (h x) (refl g p))
       (naturality A B f g h x y p))

{` Litmus checks: the functor of the identity acts trivially on paths,
   the functor of a composite is the composite of the functors on arrows
   (judgmentally), and the components of the natural transformation are
   the given identifications. `}
def path_wild_functor_identity (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (path_wild_functor A A (z ↦ z) .mor x y p) p
  ≔ refl p

def path_wild_functor_compose (A B C : Type) (f : A → B) (g : B → C) (x y : A) (p : Id A x y)
  : Id (Id C (g (f x)) (g (f y))) (path_wild_functor A C (z ↦ g (f z)) .mor x y p)
      (functor_compose (PathWild A) (PathWild B) (PathWild C) (path_wild_functor B C g) (path_wild_functor A B f)
        .mor x y p)
  ≔ refl (refl g (refl f p))

def path_wild_nat_trans_component (A B : Type) (f g : A → B) (h : (x : A) → Id B (f x) (g x)) (x : A)
  : Id (Id B (f x) (g x)) (path_wild_nat_trans A B f g h .component x) (h x)
  ≔ refl (h x)

def path_wild_bool_negation : WildFunctor (PathWild Bool) (PathWild Bool) ≔ path_wild_functor Bool Bool bool_not

def path_wild_bool_negation_involution
  : WildNatTrans (PathWild Bool) (PathWild Bool)
      (path_wild_functor Bool Bool (b ↦ bool_not (bool_not b))) (path_wild_functor Bool Bool (b ↦ b))
  ≔ path_wild_nat_trans Bool Bool (b ↦ bool_not (bool_not b)) (b ↦ b) bool_not_involutive
