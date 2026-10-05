export "23-fiber-paths"

{` All truncation-dependent statements take its signature explicitly. `}
def mere_transport (T : TruncationSignature) (A : Type) (P : A → Type)
  (hP : (a : A) → isProp (P a)) (x y : A) (p : T .carrier (Id A x y)) (u : P x) : P y
  ≔ trunc_rec T (Id A x y) (P y) (hP y) (q ↦ transport A P x y q u) p

def connected_based_elim (T : TruncationSignature) (A : Type) (hA : IsConnected T A)
  (a : A) (P : A → Type) (hP : (x : A) → isProp (P x)) (u : P a) : (x : A) → P x
  ≔ x ↦ mere_transport T A P hP a x (hA .snd a x) u

def connected_pair_elim (T : TruncationSignature) (A : Type) (hA : IsConnected T A)
  (a : A) (P : A → A → Type) (hP : (x y : A) → isProp (P x y)) (u : P a a)
  : (x y : A) → P x y
  ≔ x y ↦ mere_transport T A (x ↦ P x y) (x ↦ hP x y) a x (hA .snd a x)
      (mere_transport T A (P a) (hP a) a y (hA .snd a y) u)

{` xca:component-connected, including the assertion about propositional
   properties, with equality in the bundled type of propositions. `}
def component_connected (T : TruncationSignature) (A : Type) (a : A)
  : IsConnected T (Component T A a)
  ≔ (T .include (Component T A a) (a, T .include (Id A a a) (refl a)), u v ↦
      let e ≔ subtype_path_equiv A (x ↦ T .carrier (Id A a x))
        (x ↦ T .proposition (Id A a x)) u v in
      trunc_map T (Id A (u .fst) (v .fst)) (Id (Component T A a) u v)
        (equiv_inverse_map (Id (Component T A a) u v) (Id A (u .fst) (v .fst)) e)
        (merely_paths_compose T A a (u .fst) (v .fst) (u .snd) (v .snd)))

def same_component_properties (T : TruncationSignature) (A : Type) (P : A → PropTypes)
  (x y : A) (p : T .carrier (Id A x y)) : Id PropTypes (P x) (P y)
  ≔ trunc_rec T (Id A x y) (Id PropTypes (P x) (P y)) (propositions_set (P x) (P y))
      (map_path A PropTypes P x y) p

def connected_set_contractible (T : TruncationSignature) (A : Type)
  (hA : IsConnected T A) (sA : isSet A) : BookIsContr A
  ≔ let propA : isProp A ≔ x y ↦ trunc_rec T (Id A x y) (Id A x y) (sA x y)
      (identity (Id A x y)) (hA .snd x y) in
    let a ≔ trunc_rec T A A propA (identity A) (hA .fst) in
    (a, propA a)

def loops_prop_set (A : Type) (h : (a : A) → isProp (Id A a a)) : isSet A
  ≔ x y p q ↦ J A x
      (y p ↦ (q : Id A x y) → Id (Id A x y) p q)
      (h x (refl x)) y p q

def connected_loops_prop_contractible (T : TruncationSignature) (A : Type)
  (hA : IsConnected T A) (h : (a : A) → isProp (Id A a a)) : BookIsContr A
  ≔ connected_set_contractible T A hA (loops_prop_set A h)

def connected_sigma (T : TruncationSignature) (A : Type) (B : A → Type)
  (hA : IsConnected T A) (hB : (a : A) → IsConnected T (B a)) : IsConnected T (Σ A B)
  ≔ (trunc_rec T A (T .carrier (Σ A B)) (T .proposition (Σ A B))
      (a ↦ trunc_map T (B a) (Σ A B) (b ↦ (a, b)) (hB a .fst)) (hA .fst),
    u v ↦ trunc_rec T (Id A (u .fst) (v .fst)) (T .carrier (Id (Σ A B) u v))
      (T .proposition (Id (Σ A B) u v))
      (p ↦ trunc_map T
        (Id (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd))
        (Id (Σ A B) u v)
        (q ↦ (p, pathover_of_eq A B (u .fst) (v .fst) p (u .snd) (v .snd) q))
        (hB (v .fst) .snd (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd)))
      (hA .snd (u .fst) (v .fst)))

def nonempty_to_connected_surjective (T : TruncationSignature) (A B : Type)
  (f : A → B) (hA : T .carrier A) (hB : IsConnected T B) : IsSurjection T A B f
  ≔ b ↦ trunc_rec T A (T .carrier (BookFiber A B f b)) (T .proposition (BookFiber A B f b))
      (a ↦ trunc_map T (Id B b (f a)) (BookFiber A B f b) (p ↦ (a, p)) (hB .snd b (f a))) hA

{` cor:inj+connected, with the weaker nonempty assumption on the source. `}
def nonempty_connected_embedding_equiv (T : TruncationSignature) (A B : Type)
  (f : A → B) (hA : T .carrier A) (hB : IsConnected T B) (h : IsEmbedding A B f)
  : BookEquiv A B
  ≔ embedding_surjection_equiv T A B f h (nonempty_to_connected_surjective T A B f hA hB)

{` lem:whenisbasespaceconnected `}
def surjection_preserves_connected (T : TruncationSignature) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (s : IsSurjection T A B f) : IsConnected T B
  ≔ (trunc_map T A B f (hA .fst), x y ↦
      trunc_rec T (BookFiber A B f x) (T .carrier (Id B x y)) (T .proposition (Id B x y))
        (u ↦ trunc_rec T (BookFiber A B f y) (T .carrier (Id B x y)) (T .proposition (Id B x y))
          (v ↦ trunc_map T (Id A (u .fst) (v .fst)) (Id B x y)
            (p ↦ concat B x (f (u .fst)) y (u .snd)
              (concat B (f (u .fst)) (f (v .fst)) y (map_path A B f (u .fst) (v .fst) p)
                (inverse B y (f (v .fst)) (v .snd))))
            (hA .snd (u .fst) (v .fst))) (s y)) (s x))

def ApFibersLevel (n : Nat) (A B : Type) (f : A → B) (x y : A) : Type
  ≔ (p : Id B (f x) (f y)) →
      HLevel n (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p)

def ap_fibers_level_prop (n : Nat) (A B : Type) (f : A → B) (x y : A)
  : isProp (ApFibersLevel n A B f x y)
  ≔ pi_prop (Id B (f x) (f y))
      (p ↦ HLevel n (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p))
      (p ↦ hlevel_isprop n (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p))

{` cor:fib-vs-path, second clause. The converse is fibers_hlevel_to_ap
   restricted to x=y=a. `}
def loop_fibers_to_all_ap (T : TruncationSignature) (n : Nat) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (a : A) (h : ApFibersLevel n A B f a a)
  : (x y : A) → ApFibersLevel n A B f x y
  ≔ connected_pair_elim T A hA a (ApFibersLevel n A B f) (ap_fibers_level_prop n A B f) h

def loop_fibers_to_fibers (T : TruncationSignature) (n : Nat) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (a : A) (h : ApFibersLevel n A B f a a)
  : (b : B) → HLevel (suc. n) (BookFiber A B f b)
  ≔ ap_hlevel_to_fibers n A B f (loop_fibers_to_all_ap T n A B f hA a h)

{` cor:fib-vs-path, third clause. `}
def connected_map_equiv_from_paths (T : TruncationSignature) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (hB : IsConnected T B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  : BookEquiv A B
  ≔ nonempty_connected_embedding_equiv T A B f (hA .fst) hB (path_equivalences_embedding A B f h)

def map_equiv_to_paths (A B : Type) (f : A → B) (h : BookIsEquiv A B f) (x y : A)
  : BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y)
  ≔ book_equivalence (Id A x y) (Id B (f x) (f y))
      (equivalence_on_paths A B (native_equivalence A B (f, h)) x y) .equiv

{` cor:fib-vs-path, fourth clause. `}
def connected_map_equiv_from_loops (T : TruncationSignature) (A B : Type) (f : A → B)
  (hA : IsConnected T A) (hB : IsConnected T B) (a : A)
  (h : BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a)) : BookEquiv A B
  ≔ let k ≔ loop_fibers_to_all_ap T zero. A B f hA a
      (p ↦ native_contraction
        (BookFiber (Id A a a) (Id B (f a) (f a)) (map_path A B f a a) p) (h p)) in
    connected_map_equiv_from_paths T A B f hA hB
      (x y p ↦ book_contraction
        (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p) (k x y p))
