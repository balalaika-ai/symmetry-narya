export "185-native-truncation-logic"

{` Companions that state the book's precise claims "this specific map is an
   equivalence" for results whose original type only says that two types are
   equivalent (BookEquiv X Y or Equiv X Y). In each case the underlying map of
   the original declaration is definitionally the book's map, so each
   companion is the original followed by .equiv; native Equiv results are first
   converted with book_equivalence, which keeps the map. The map is written out
   in each companion's type. Also: the converse of lem:inj+surj, the split
   surjection footnote of def:surjection, and the warning in the footnote of
   lem:inj-ap. `}

{` lem:inj+surj (intro-uf.tex:2907), "if" direction: the equivalence is f itself. `}
def embedding_surjection_equiv_book_map (T : TruncationSignature) (A B : Type) (f : A → B)
  (inj : IsEmbedding A B f) (surj : IsSurjection T A B f) : BookIsEquiv A B f
  ≔ embedding_surjection_equiv T A B f inj surj .equiv

def native_embedding_surjection_equiv_book_map (A B : Type) (f : A → B)
  (i : IsEmbedding A B f) (s : Surjective A B f) : BookIsEquiv A B f
  ≔ native_embedding_surjection_equiv A B f i s .equiv

{` lem:inj+surj (intro-uf.tex:2907), "only if" direction: an equivalence
   (contractible book fibers) is an injection (propositional book fibers) and a
   surjection (merely inhabited book fibers). Together with the "if" direction
   this gives the iff, as an equivalence of propositions. `}
def book_isequiv_embedding (A B : Type) (f : A → B) (e : BookIsEquiv A B f)
  : IsEmbedding A B f
  ≔ b ↦ contractible_prop (BookFiber A B f b) (native_contraction (BookFiber A B f b) (e b))

def book_isequiv_surjection (T : TruncationSignature) (A B : Type) (f : A → B)
  (e : BookIsEquiv A B f) : IsSurjection T A B f
  ≔ b ↦ T .include (BookFiber A B f b) (e b .center)

def native_book_isequiv_surjective (A B : Type) (f : A → B) (e : BookIsEquiv A B f)
  : Surjective A B f
  ≔ book_isequiv_surjection native_truncation A B f e

def embedding_surjection_iff (T : TruncationSignature) (A B : Type) (f : A → B)
  : Equiv (BookIsEquiv A B f) (Product (IsEmbedding A B f) (IsSurjection T A B f))
  ≔ iff_equiv (BookIsEquiv A B f) (Product (IsEmbedding A B f) (IsSurjection T A B f))
      (book_isequiv_isprop A B f)
      (product_prop (IsEmbedding A B f) (IsSurjection T A B f)
        (pi_prop B (b ↦ isProp (BookFiber A B f b)) (b ↦ isprop_isprop (BookFiber A B f b)))
        (pi_prop B (b ↦ T .carrier (BookFiber A B f b)) (b ↦ T .proposition (BookFiber A B f b))))
      (e ↦ (book_isequiv_embedding A B f e, book_isequiv_surjection T A B f e))
      (u ↦ embedding_surjection_equiv_book_map T A B f (u .fst) (u .snd))

def native_embedding_surjection_iff (A B : Type) (f : A → B)
  : Equiv (BookIsEquiv A B f) (Product (IsEmbedding A B f) (Surjective A B f))
  ≔ embedding_surjection_iff native_truncation A B f

{` Universal property of propositional truncation, after def:prop-trunc
   (intro-uf.tex:2702): precomposition with |–| is an equivalence
   (‖A‖ → P) ≃ (A → P) for every proposition P. `}
def mere_universal_property_book_map (A P : Type) (h : isProp P)
  : BookIsEquiv (Mere A → P) (A → P) (g ↦ compose A (Mere A) P g (mere A))
  ≔ mere_universal_property A P h .equiv

{` cor:inj+connected (intro-uf.tex:2927): the injection f itself is an equivalence. `}
def nonempty_connected_embedding_equiv_book_map (T : TruncationSignature) (A B : Type)
  (f : A → B) (hA : T .carrier A) (hB : IsConnected T B) (h : IsEmbedding A B f)
  : BookIsEquiv A B f
  ≔ nonempty_connected_embedding_equiv T A B f hA hB h .equiv

def native_nonempty_connected_embedding_equiv_book_map (A B : Type) (f : A → B)
  (hA : Mere A) (hB : Connected B) (h : IsEmbedding A B f) : BookIsEquiv A B f
  ≔ native_nonempty_connected_embedding_equiv A B f hA hB h .equiv

{` cor:fib-vs-path (intro-uf.tex:3020), clauses (3) and (4), "if" halves:
   the map f itself is an equivalence. `}
def connected_map_equiv_from_paths_book_map (T : TruncationSignature) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (hB : IsConnected T B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  : BookIsEquiv A B f
  ≔ connected_map_equiv_from_paths T A B f hA hB h .equiv

def native_connected_map_equiv_from_paths_book_map (A B : Type) (f : A → B)
  (hA : Connected A) (hB : Connected B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  : BookIsEquiv A B f
  ≔ native_connected_map_equiv_from_paths A B f hA hB h .equiv

def connected_map_equiv_from_loops_book_map (T : TruncationSignature) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (hB : IsConnected T B) (a : A)
  (h : BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
  : BookIsEquiv A B f
  ≔ connected_map_equiv_from_loops T A B f hA hB a h .equiv

def native_connected_map_equiv_from_loops_book_map (A B : Type) (f : A → B)
  (hA : Connected A) (hB : Connected B) (a : A)
  (h : BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a))
  : BookIsEquiv A B f
  ≔ native_connected_map_equiv_from_loops A B f hA hB a h .equiv

{` lem:inj-ap (intro-uf.tex:2993), "only if" half: for an injection f, the
   induced map ap_f = map_path f on identity types is an equivalence. `}
def embedding_on_paths_book_map (A B : Type) (f : A → B) (h : IsEmbedding A B f) (x y : A)
  : BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y)
  ≔ embedding_on_paths A B f h x y .equiv

{` Warning in the footnote of lem:inj-ap (intro-uf.tex:2993). When B is a set,
   all ap_f are equivalences iff f reflects paths (PathReflecting A B f, i.e.
   Π a a′ (f a = f a′ → a = a′)); only B needs to be a set, and the first
   implication holds for arbitrary B. In general path reflection is not
   sufficient: boolean_set_point : Unit → SetTypes reflects paths trivially,
   but its ap maps are not all equivalences (SetTypes is not a set). `}
def ap_equivalences_reflect_paths (A B : Type) (f : A → B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  : PathReflecting A B f
  ≔ embedding_reflects_paths A B f (path_equivalences_embedding A B f h)

def set_path_reflection_ap_equivalences (A B : Type) (setB : isSet B) (f : A → B)
  (inj : PathReflecting A B f) (x y : A)
  : BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y)
  ≔ embedding_on_paths A B f (path_reflecting_set_embedding A B setB f inj) x y .equiv

def set_ap_equivalences_path_reflection_iff (A B : Type) (setB : isSet B) (f : A → B)
  : Product
      (((x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
        → PathReflecting A B f)
      (PathReflecting A B f
        → (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  ≔ (ap_equivalences_reflect_paths A B f, set_path_reflection_ap_equivalences A B setB f)

def boolean_set_point_reflects_paths : PathReflecting Unit SetTypes boolean_set_point
  ≔ x y _ ↦ unit_prop x y

def boolean_set_point_ap_not_equivalences
  : Not ((x y : Unit)
      → BookIsEquiv (Id Unit x y) (Id SetTypes (boolean_set_point x) (boolean_set_point y))
          (map_path Unit SetTypes boolean_set_point x y))
  ≔ h ↦ boolean_set_point_not_embedding (path_equivalences_embedding Unit SetTypes boolean_set_point h)

def path_reflection_not_sufficient
  : Not ((A B : Type) (f : A → B) → PathReflecting A B f
      → (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  ≔ h ↦ boolean_set_point_ap_not_equivalences
      (h Unit SetTypes boolean_set_point boolean_set_point_reflects_paths)

{` Footnote of def:surjection (intro-uf.tex:2881). A split surjection is a
   function Π(b:B) Σ(a:A) (b = f a); this is equivalent to a section g : B → A
   with an identification f∘g = id_B. The equivalence is the composite of the
   type-theoretic choice equivalence, function extensionality and path
   inversion; its underlying map is split_surjection_to_section
   (split_surjection_section_equiv_map, by refl). `}
def SplitSurjection (A B : Type) (f : A → B) : Type ≔ (b : B) → BookFiber A B f b

def MapSection (A B : Type) (f : A → B) : Type
  ≔ Σ (B → A) (g ↦ Id (B → B) (compose B A B f g) (identity B))

def split_surjection_to_section (A B : Type) (f : A → B) (s : SplitSurjection A B f)
  : MapSection A B f
  ≔ ((b ↦ s b .fst),
      inverse (B → B) (identity B) (compose B A B f (b ↦ s b .fst))
        (funext B (_ ↦ B) (identity B) (compose B A B f (b ↦ s b .fst)) (b ↦ s b .snd)))

def section_to_split_surjection (A B : Type) (f : A → B) (t : MapSection A B f)
  : SplitSurjection A B f
  ≔ b ↦ (t .fst b,
      inverse B (f (t .fst b)) b
        (happly B (_ ↦ B) (compose B A B f (t .fst)) (identity B) (t .snd) b))

def split_surjection_section_equiv (A B : Type) (f : A → B)
  : Equiv (SplitSurjection A B f) (MapSection A B f)
  ≔ compose_equiv (SplitSurjection A B f)
      (Σ (B → A) (g ↦ (b : B) → Id B b (f (g b)))) (MapSection A B f)
      (choice_equiv B (_ ↦ A) (b a ↦ Id B b (f a)))
      (family_equiv (B → A) (g ↦ (b : B) → Id B b (f (g b)))
        (g ↦ Id (B → B) (compose B A B f g) (identity B))
        (g ↦ compose_equiv ((b : B) → Id B b (f (g b)))
          (Id (B → B) (identity B) (compose B A B f g))
          (Id (B → B) (compose B A B f g) (identity B))
          (funext_equiv B (_ ↦ B) (identity B) (compose B A B f g))
          (inverse_path_equiv (B → B) (identity B) (compose B A B f g))))

def split_surjection_section_equiv_map (A B : Type) (f : A → B)
  : Id (SplitSurjection A B f → MapSection A B f)
      (split_surjection_section_equiv A B f .map) (split_surjection_to_section A B f)
  ≔ refl (split_surjection_to_section A B f)

{` lem:freeloopspace (circle.tex:204): the evaluation ev_A(g) ≔ (g(base), g(loop))
   is an equivalence, and its inverse (the center of each book fiber) is
   ve_A, defined by the recursion principle. `}
def book_circle_universal_property_book_map (C : CircleSignature) (A : Type)
  : BookIsEquiv (C .carrier → A) (FreeLoop A) (g ↦ (g (C .base), refl g (C .loop)))
  ≔ book_circle_universal_property C A .equiv

def book_circle_universal_property_inverse (C : CircleSignature) (A : Type) (d : FreeLoop A)
  : Id (C .carrier → A) (book_circle_universal_property C A .equiv d .center .fst)
      (circle_rec C A d)
  ≔ refl (circle_rec C A d)

{` cor:circle-loopspace (circle.tex:238): (g,p) ↦ p⁻¹·g(loop)·p is an
   equivalence, for the book's pointing p : a = g(base). In concatenation
   order this is p, then g(loop), then p⁻¹. `}
def pointed_circle_universal_property_book_map (C : CircleSignature) (A : Type) (a : A)
  : BookIsEquiv (BookPointedMap (circle_pointed C) (A, a)) (Id A a a)
      (u ↦ concat A a (u .fst (C .base)) a (u .snd)
        (concat A (u .fst (C .base)) (u .fst (C .base)) a (refl (u .fst) (C .loop))
          (inverse A a (u .fst (C .base)) (u .snd))))
  ≔ book_equivalence (BookPointedMap (circle_pointed C) (A, a)) (Id A a a)
      (pointed_circle_universal_property C A a) .equiv

{` rem:dep-univ-prop-circle (circle.tex:267): the dependent evaluation
   g ↦ (g(base), apd_g(loop)) into Σ(b : P base) pathover(b, loop, b) is an
   equivalence, for every family P. `}
def circle_dependent_universal_property_book_map (C : CircleSignature) (P : C .carrier → Type)
  : BookIsEquiv ((x : C .carrier) → P x) (CircleBoundary (C .carrier) (C .base) (C .loop) P)
      (g ↦ (g (C .base), refl g (C .loop)))
  ≔ book_equivalence ((x : C .carrier) → P x) (CircleBoundary (C .carrier) (C .base) (C .loop) P)
      (circle_dependent_universal_property C P) .equiv

{` def:zet (circle.tex:363): the gluing evaluation f ↦ (f∘ι₊, f∘ι₋, apd_f(zeq))
   is an equivalence; this packages the induction principle of ℤ with its
   computation rules. Here ι₋ is int_nonpositive and zeq is int_zero_glue. `}
def integer_gluing_universal_property_book_map (P : Int → Type)
  : BookIsEquiv ((z : Int) → P z) (IntegerBoundary P)
      (f ↦ ((n ↦ f (int_of_nat n)),
        ((n ↦ f (int_nonpositive n)),
          apd Int P f (int_nonpositive zero.) (int_of_nat zero.) int_zero_glue)))
  ≔ integer_gluing_universal_property P .equiv

{` lem:univisexp (circle.tex:1105): f(z)(p) ≔ R(p)(0) is an equivalence
   (base = z) ≃ R(z) for every z. The book's judgmental R(base) ≡ ℤ is replaced
   by the enumeration e : ℤ ≃ R(base) of circle_integer_monodromy, so 0 is e(0). `}
def circle_paths_integer_family_equiv_book_map (C : CircleSignature) (z : C .carrier)
  : BookIsEquiv (Id (C .carrier) (C .base) z) (circle_integer_family C z)
      (p ↦ transport (C .carrier) (circle_integer_family C) (C .base) z p
        (circle_integer_monodromy C .enumeration .map int_zero))
  ≔ book_equivalence (Id (C .carrier) (C .base) z) (circle_integer_family C z)
      (circle_paths_integer_family_equiv C z) .equiv

{` cor:S1groupoid (circle.tex:1129): n ↦ loopⁿ is an equivalence ℤ ≃ (base = base). `}
def circle_integer_loop_equiv_book_map (C : CircleSignature)
  : BookIsEquiv Int (Id (C .carrier) (C .base) (C .base))
      (n ↦ loop_power (C .carrier) (C .base) (C .loop) n)
  ≔ circle_integer_loop_equiv C .equiv

{` def:windingnumber (circle.tex:1156): wdg ≔ f(base), i.e. p ↦ R(p)(0), is an
   equivalence (base = base) ≃ ℤ. With R(base) ≡ ℤ replaced by the
   enumeration e, this reads p ↦ e⁻¹(R(p)(e 0)). `}
def circle_loop_integer_equiv_book_map (C : CircleSignature)
  : BookIsEquiv (Id (C .carrier) (C .base) (C .base)) Int
      (p ↦ equiv_inverse_map Int (circle_integer_family C (C .base))
        (circle_integer_monodromy C .enumeration)
        (transport (C .carrier) (circle_integer_family C) (C .base) (C .base) p
          (circle_integer_monodromy C .enumeration .map int_zero)))
  ≔ circle_loop_integer_equiv C .equiv

{` lem:S1-delooping (circle.tex:1164): ě, defined by circle recursion with
   ě(base) ≔ a and ě(loop) ≔ e(loop), is an equivalence. `}
def circle_delooping_equiv_book_map (C : CircleSignature) (A : Type) (connected : Connected A)
  (a : A) (e : Equiv (Id (C .carrier) (C .base) (C .base)) (Id A a a))
  (unit : LoopMapUnit (C .carrier) A (C .base) a (e .map))
  (composition : LoopMapComposition (C .carrier) A (C .base) a (e .map))
  : BookIsEquiv (C .carrier) A (circle_rec C A (a, e .map (C .loop)))
  ≔ circle_delooping_equiv C A connected a e unit composition .equiv

{` xca:general-winding (circle.tex:1179): f_x is ě for e ≔ wdg_x⁻¹ ∘ wdg, i.e.
   the circle recursor with f_x(base) ≔ x and f_x(loop) ≔ wdg_x⁻¹(wdg(loop)). `}
def circle_translation_book_map (C : CircleSignature) (x : C .carrier)
  : BookIsEquiv (C .carrier) (C .carrier)
      (circle_rec C (C .carrier)
        (x, equiv_inverse_map (Id (C .carrier) x x) Int (circle_general_winding_equiv C x)
          (circle_winding C (C .loop))))
  ≔ circle_translation C x .equiv

{` lem:IdCisZet (circle.tex:1378): ev₀(e,!) ≔ e(0) is an equivalence. An
   identification p of endomorphisms (ℤ,s) = (X,t) has type component
   p .fst : ℤ = X, whose transport .trr is the book's underlying e. `}
def infinite_endomorphism_evaluation_book_map (t : InfiniteCycles)
  : BookIsEquiv (Id Endomorphisms integer_endomorphism (t .fst)) (t .fst .fst)
      (p ↦ p .fst .trr int_zero)
  ≔ infinite_endomorphism_evaluation t .equiv

{` xca:TTYoneda (circle.tex:1547): e_x(u) ≔ (y, p) ↦ transport_F(p)(u) is an
   equivalence F(x) ≃ Π(y:X) ((x = y) → F(y)). `}
def type_theoretic_yoneda_book_map (X : Type) (F : X → Type) (x : X)
  : BookIsEquiv (F x) (YonedaSections X F x) (u ↦ (y p ↦ transport X F x y p u))
  ≔ type_theoretic_yoneda X F x .equiv

{` thm:S1bysymmetries (circle.tex:1581): the map c of def:S1toC, the circle
   recursor with c(base) ≔ (ℤ,s) and c(loop) the predecessor symmetry, is an
   equivalence. `}
def circle_infinite_cycles_equiv_book_map (C : CircleSignature)
  : BookIsEquiv (C .carrier) InfiniteCycles
      (circle_rec C InfiniteCycles (infinite_endomorphism_point, infinite_predecessor_loop))
  ≔ circle_infinite_cycles_equiv C .equiv
