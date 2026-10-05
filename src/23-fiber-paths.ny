export "22-boolean-symmetry"

def concat_left_right_inverse (A : Type) (x y z : A) (p : Id A x y) (q : Id A x z)
  : Id (Id A x z) (concat A x y z p (concat A y x z (inverse A x y p) q)) q
  ≔ calc
      concat A x y z p (concat A y x z (inverse A x y p) q)
      = concat A x x z (concat A x y x p (inverse A x y p)) q
        by concat_assoc A x y x z p (inverse A x y p) q
      = concat A x x z (refl x) q
        by refl ((r ↦ concat A x x z r q) : Id A x x → Id A x z) (concat_inverse_right A x y p)
      = q by concat_1p A x z q ∎

def concat_left_equiv (A : Type) (x y z : A) (p : Id A x y)
  : Equiv (Id A y z) (Id A x z)
  ≔ quasi_inverse_equiv (Id A y z) (Id A x z) (concat A x y z p)
      (concat A y x z (inverse A x y p))
      (concat_left_inverse A x y z p) (concat_left_right_inverse A x y z p)

def inverse_path_equiv (A : Type) (x y : A) : Equiv (Id A x y) (Id A y x)
  ≔ quasi_inverse_equiv (Id A x y) (Id A y x) (inverse A x y) (inverse A y x)
      (inverse_inverse A x y) (inverse_inverse A y x)

{` Native dependent equality in a family of paths is equivalent to the
   expected commutative triangle. The base computation is typal. `}
def pathover_mapped_paths_type (A B : Type) (f : A → B) (b : B)
  (x y : A) (r : Id A x y) (p : Id B b (f x)) (q : Id B b (f y))
  : Id Type (Id (a ↦ Id B b (f a)) r p q)
      (Id (Id B b (f y)) (concat B b (f x) (f y) p (map_path A B f x y r)) q)
  ≔ J A x
      (y r ↦ (q : Id B b (f y)) → Id Type (Id (a ↦ Id B b (f a)) r p q)
        (Id (Id B b (f y)) (concat B b (f x) (f y) p (map_path A B f x y r)) q))
      (q ↦ refl ((s ↦ Id (Id B b (f x)) s q) : Id B b (f x) → Type)
        (inverse (Id B b (f x)) (concat B b (f x) (f x) p (refl (f x))) p
          (concat_p1 B b (f x) p))) y r q

def path_difference_equiv (B : Type) (b x y : B)
  (p : Id B b x) (q : Id B b y) (r : Id B x y)
  : Equiv (Id (Id B b y) (concat B b x y p r) q)
      (Id (Id B x y) (concat B x b y (inverse B b x p) q) r)
  ≔ let L ≔ (Id B x y) in
    let s ≔ concat B x b y (inverse B b x p) (concat B b x y p r) in
    let t ≔ concat B x b y (inverse B b x p) q in
    compose_equiv (Id (Id B b y) (concat B b x y p r) q) (Id L s t) (Id L t r)
      (equivalence_on_paths (Id B b y) L (concat_left_equiv B x b y (inverse B b x p))
        (concat B b x y p r) q)
      (compose_equiv (Id L s t) (Id L r t) (Id L t r)
        (id_to_equiv (Id L s t) (Id L r t)
          (refl ((u ↦ Id L u t) : L → Type) (concat_left_inverse B b x y p r)))
        (inverse_path_equiv L r t))

def fiber_path_triangle_equiv (A B : Type) (f : A → B) (b : B)
  (x y : A) (r : Id A x y) (p : Id B b (f x)) (q : Id B b (f y))
  : Equiv (Id (a ↦ Id B b (f a)) r p q)
      (Id (Id B (f x) (f y)) (concat B (f x) b (f y) (inverse B b (f x) p) q)
        (map_path A B f x y r))
  ≔ compose_equiv (Id (a ↦ Id B b (f a)) r p q)
      (Id (Id B b (f y)) (concat B b (f x) (f y) p (map_path A B f x y r)) q)
      (Id (Id B (f x) (f y)) (concat B (f x) b (f y) (inverse B b (f x) p) q)
        (map_path A B f x y r))
      (id_to_equiv (Id (a ↦ Id B b (f a)) r p q)
        (Id (Id B b (f y)) (concat B b (f x) (f y) p (map_path A B f x y r)) q)
        (pathover_mapped_paths_type A B f b x y r p q))
      (path_difference_equiv B b (f x) (f y) p q (map_path A B f x y r))

{` con:fib-vs-path, in precisely the book's fiber orientation. `}
def fiber_path_equiv (A B : Type) (f : A → B) (b : B) (u v : BookFiber A B f b)
  : Equiv (Id (BookFiber A B f b) u v)
      (BookFiber (Id A (u .fst) (v .fst)) (Id B (f (u .fst)) (f (v .fst)))
        (map_path A B f (u .fst) (v .fst))
        (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)))
  ≔ compose_equiv (Id (BookFiber A B f b) u v) (SigmaPath A (a ↦ Id B b (f a)) u v)
      (BookFiber (Id A (u .fst) (v .fst)) (Id B (f (u .fst)) (f (v .fst)))
        (map_path A B f (u .fst) (v .fst))
        (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)))
      (canonical_inverse_equiv (SigmaPath A (a ↦ Id B b (f a)) u v)
        (Id (BookFiber A B f b) u v) (sigma_path_equiv A (a ↦ Id B b (f a)) u v))
      (family_equiv (Id A (u .fst) (v .fst))
        (r ↦ Id (a ↦ Id B b (f a)) r (u .snd) (v .snd))
        (r ↦ Id (Id B (f (u .fst)) (f (v .fst)))
          (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd))
          (map_path A B f (u .fst) (v .fst) r))
        (r ↦ fiber_path_triangle_equiv A B f b (u .fst) (v .fst) r (u .snd) (v .snd)))

def inverse_refl_concat (B : Type) (x y : B) (p : Id B x y)
  : Id (Id B x y) (concat B x x y (inverse B x x (refl x)) p) p
  ≔ concat (Id B x y) (concat B x x y (inverse B x x (refl x)) p)
      (concat B x x y (refl x) p) p
      (refl ((q ↦ concat B x x y q p) : Id B x x → Id B x y) (inverse_refl B x))
      (concat_1p B x y p)

def ap_fiber_equiv (A B : Type) (f : A → B) (x y : A) (p : Id B (f x) (f y))
  : Equiv (Id (BookFiber A B f (f x)) (x, refl (f x)) (y, p))
      (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p)
  ≔ let F ≔ BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) in
    let q ≔ concat B (f x) (f x) (f y) (inverse B (f x) (f x) (refl (f x))) p in
    compose_equiv (Id (BookFiber A B f (f x)) (x, refl (f x)) (y, p)) (F q) (F p)
      (fiber_path_equiv A B f (f x) (x, refl (f x)) (y, p))
      (id_to_equiv (F q) (F p) (refl F (inverse_refl_concat B (f x) (f y) p)))

{` cor:fib-vs-path, first clause. Index n here is the h-level of ap fibers,
   so book n-types use this theorem with index n+2. `}
def fibers_hlevel_to_ap (n : Nat) (A B : Type) (f : A → B)
  (h : (b : B) → HLevel (suc. n) (BookFiber A B f b))
  (x y : A) (p : Id B (f x) (f y))
  : HLevel n (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p)
  ≔ hlevel_equiv n (Id (BookFiber A B f (f x)) (x, refl (f x)) (y, p))
      (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p)
      (ap_fiber_equiv A B f x y p) (h (f x) (x, refl (f x)) (y, p))

def ap_hlevel_to_fibers (n : Nat) (A B : Type) (f : A → B)
  (h : (x y : A) (p : Id B (f x) (f y)) →
    HLevel n (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p))
  (b : B) : HLevel (suc. n) (BookFiber A B f b)
  ≔ u v ↦ let p ≔ concat B (f (u .fst)) b (f (v .fst))
      (inverse B b (f (u .fst)) (u .snd)) (v .snd) in
    let F ≔ BookFiber (Id A (u .fst) (v .fst)) (Id B (f (u .fst)) (f (v .fst)))
      (map_path A B f (u .fst) (v .fst)) p in
    hlevel_equiv n F (Id (BookFiber A B f b) u v)
      (canonical_inverse_equiv (Id (BookFiber A B f b) u v) F (fiber_path_equiv A B f b u v))
      (h (u .fst) (v .fst) p)

{` lem:inj-ap, both implications and the actual induced path map. `}
def embedding_on_paths (A B : Type) (f : A → B) (h : IsEmbedding A B f) (x y : A)
  : BookEquiv (Id A x y) (Id B (f x) (f y))
  ≔ (map_path A B f x y, p ↦ book_contraction
      (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p)
      (fibers_hlevel_to_ap zero. A B f (b ↦ prop_to_hlevel_one (BookFiber A B f b) (h b)) x y p))

def path_equivalences_embedding (A B : Type) (f : A → B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y))
  : IsEmbedding A B f
  ≔ b ↦ hlevel_one_to_prop (BookFiber A B f b)
      (ap_hlevel_to_fibers zero. A B f
        (x y p ↦ native_contraction
          (BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) p) (h x y p)) b)
