export "1201-loop-algebra"

{` Chapter 12, sec:univ-cover-simple (abelian.tex 231-343): simply connected
   pointed types, the universal covering Ũ_a A ≔ Σ(x : A) ‖a = x‖₀, the
   composition of set-truncated paths, eq:id-types-universal-cover and
   lemma:universal-cover-simply-connected. `}

{` Running text (abelian.tex 249): (A, a) is simply connected when both A
   and a = a are connected. `}
def SimplyConnected (X : Pointed) : Type ≔ Product (Connected (X .carrier)) (Connected (Loop X))

def simply_connected_prop (X : Pointed) : isProp (SimplyConnected X)
  ≔ product_prop (Connected (X .carrier)) (Connected (Loop X)) (connected_prop (X .carrier)) (connected_prop (Loop X))

{` Connectedness from mere paths out of one point (xca:defgroup, first part). `}
def connected_from_point (A : Type) (a : A) (k : (x : A) → Mere (Id A a x)) : Connected A
  ≔ (mere A a, x y ↦ merely_paths_compose native_truncation A a x y (k x) (k y))

{` The universal covering (definition at abelian.tex 252), pointed at
   (a, |refl a|₀), with the first projection, pointed by refl. `}
def UnivCover (A : Type) (a : A) : Type ≔ Σ A (x ↦ SetTrunc (Id A a x))

def univ_cover_point (A : Type) (a : A) : UnivCover A a ≔ (a, set_trunc (Id A a a) (refl a))

def univ_cover_pointed (A : Type) (a : A) : Pointed ≔ (UnivCover A a, univ_cover_point A a)

def univ_cover_projection (A : Type) (a : A) : BookPointedMap (univ_cover_pointed A a) (A, a)
  ≔ ((u ↦ u .fst), refl a)

{` The projection is a set bundle: its fibers are the sets ‖a = x‖₀. `}
def univ_cover_projection_covering (A : Type) (a : A) : IsCovering (UnivCover A a) A (u ↦ u .fst)
  ≔ x ↦ hlevel_two_to_set (BookFiber (UnivCover A a) A (u ↦ u .fst) x)
      (hlevel_equiv (suc. (suc. zero.)) (SetTrunc (Id A a x)) (BookFiber (UnivCover A a) A (u ↦ u .fst) x)
        (compose_equiv (SetTrunc (Id A a x)) (Fiber (UnivCover A a) A (u ↦ u .fst) x)
          (BookFiber (UnivCover A a) A (u ↦ u .fst) x)
          (canonical_inverse_equiv (Fiber (UnivCover A a) A (u ↦ u .fst) x) (SetTrunc (Id A a x))
            (projection_fiber_equiv A (y ↦ SetTrunc (Id A a y)) x))
          (fiber_conventions_equiv (UnivCover A a) A (u ↦ u .fst) x))
        (set_to_hlevel_two (SetTrunc (Id A a x)) (set_trunc_set (Id A a x))))

{` Running text (abelian.tex 269-272): for a groupoid A the set truncation is
   redundant, so Ũ_a A is (equivalent to) the singleton at a and contractible. `}
def groupoid_univ_cover_singleton_equiv (A : Type) (hA : isGroupoid A) (a : A)
  : Equiv (UnivCover A a) (Σ A (x ↦ Id A a x))
  ≔ family_equiv A (x ↦ SetTrunc (Id A a x)) (x ↦ Id A a x)
      (x ↦ set_trunc_of_set_equiv (Id A a x) (hA a x))

def groupoid_univ_cover_contractible (A : Type) (hA : isGroupoid A) (a : A) : BookIsContr (UnivCover A a)
  ≔ book_contractibility_equiv (Σ A (x ↦ Id A a x)) (UnivCover A a)
      (canonical_inverse_equiv (UnivCover A a) (Σ A (x ↦ Id A a x)) (groupoid_univ_cover_singleton_equiv A hA a))
      .map (book_pathspace_contractible A a)

{` The composition ‖y = z‖₀ × ‖x = y‖₀ → ‖x = z‖₀, |q|₀ · |p|₀ ≔ |q · p|₀
   (book order: q after p, i.e. concat p q); the defining equation holds by
   definition. `}
def trunc_path_compose (A : Type) (x y z : A) (χ : SetTrunc (Id A y z)) (π : SetTrunc (Id A x y))
  : SetTrunc (Id A x z)
  ≔ set_trunc_rec (Id A y z) (SetTrunc (Id A x y) → SetTrunc (Id A x z))
      (pi_set (SetTrunc (Id A x y)) (_ ↦ SetTrunc (Id A x z)) (_ ↦ set_trunc_set (Id A x z)))
      (q ↦ set_trunc_rec (Id A x y) (SetTrunc (Id A x z)) (set_trunc_set (Id A x z))
        (p ↦ set_trunc (Id A x z) (concat A x y z p q))) χ π

def trunc_path_compose_beta (A : Type) (x y z : A) (q : Id A y z) (p : Id A x y)
  : Id (SetTrunc (Id A x z)) (trunc_path_compose A x y z (set_trunc (Id A y z) q) (set_trunc (Id A x y) p))
      (set_trunc (Id A x z) (concat A x y z p q))
  ≔ refl (set_trunc (Id A x z) (concat A x y z p q))

def trunc_path_compose_refl (A : Type) (x y : A) (α : SetTrunc (Id A x y))
  : Id (SetTrunc (Id A x y)) (trunc_path_compose A x y y (set_trunc (Id A y y) (refl y)) α) α
  ≔ set_trunc_induction (Id A x y)
      (β ↦ Id (SetTrunc (Id A x y)) (trunc_path_compose A x y y (set_trunc (Id A y y) (refl y)) β) β)
      (β ↦ prop_is_set (Id (SetTrunc (Id A x y)) (trunc_path_compose A x y y (set_trunc (Id A y y) (refl y)) β) β)
        (set_trunc_set (Id A x y) (trunc_path_compose A x y y (set_trunc (Id A y y) (refl y)) β) β))
      (p ↦ refl (set_trunc (Id A x y)) (concat_p1 A x y p)) α

{` Running text (abelian.tex 288-290): transport in ‖a = -‖₀ along p is
   α ↦ |p|₀ · α. `}
def univ_cover_transport (A : Type) (a x y : A) (p : Id A x y) (α : SetTrunc (Id A a x))
  : Id (SetTrunc (Id A a y)) (transport A (z ↦ SetTrunc (Id A a z)) x y p α)
      (trunc_path_compose A a x y (set_trunc (Id A x y) p) α)
  ≔ J A x (y p ↦ Id (SetTrunc (Id A a y)) (transport A (z ↦ SetTrunc (Id A a z)) x y p α)
        (trunc_path_compose A a x y (set_trunc (Id A x y) p) α))
      (concat (SetTrunc (Id A a x)) (transport A (z ↦ SetTrunc (Id A a z)) x x (refl x) α) α
        (trunc_path_compose A a x x (set_trunc (Id A x x) (refl x)) α)
        (transport_refl A (z ↦ SetTrunc (Id A a z)) x α)
        (inverse (SetTrunc (Id A a x)) (trunc_path_compose A a x x (set_trunc (Id A x x) (refl x)) α) α
          (trunc_path_compose_refl A a x α)))
      y p

{` eq:id-types-universal-cover: ((x, α) = (y, β)) ≃ Σ(p : x = y) |p|₀ · α = β.
   The map sends r to (r .fst, …). `}
def UnivCoverPath (A : Type) (a : A) (u v : UnivCover A a) : Type
  ≔ Σ (Id A (u .fst) (v .fst)) (p ↦ Id (SetTrunc (Id A a (v .fst)))
      (trunc_path_compose A a (u .fst) (v .fst) (set_trunc (Id A (u .fst) (v .fst)) p) (u .snd)) (v .snd))

def univ_cover_path_equiv (A : Type) (a : A) (u v : UnivCover A a)
  : Equiv (Id (UnivCover A a) u v) (UnivCoverPath A a u v)
  ≔ let B ≔ (z ↦ SetTrunc (Id A a z)) : A → Type in
    compose_equiv (Id (UnivCover A a) u v) (SigmaPath A B u v) (UnivCoverPath A a u v)
      (canonical_inverse_equiv (SigmaPath A B u v) (Id (UnivCover A a) u v) (sigma_path_equiv A B u v))
      (family_equiv (Id A (u .fst) (v .fst)) (p ↦ Id B p (u .snd) (v .snd))
        (p ↦ Id (B (v .fst)) (trunc_path_compose A a (u .fst) (v .fst) (set_trunc (Id A (u .fst) (v .fst)) p) (u .snd))
          (v .snd))
        (p ↦ compose_equiv (Id B p (u .snd) (v .snd))
          (Id (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd))
          (Id (B (v .fst)) (trunc_path_compose A a (u .fst) (v .fst) (set_trunc (Id A (u .fst) (v .fst)) p) (u .snd))
            (v .snd))
          (pathover_transport_equiv A B (u .fst) (v .fst) p (u .snd) (v .snd))
          (concat_left_equiv (B (v .fst))
            (trunc_path_compose A a (u .fst) (v .fst) (set_trunc (Id A (u .fst) (v .fst)) p) (u .snd))
            (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd)
            (inverse (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd))
              (trunc_path_compose A a (u .fst) (v .fst) (set_trunc (Id A (u .fst) (v .fst)) p) (u .snd))
              (univ_cover_transport A a (u .fst) (v .fst) p (u .snd))))))

def univ_cover_path_from (A : Type) (a : A) (u v : UnivCover A a) (w : UnivCoverPath A a u v)
  : Id (UnivCover A a) u v
  ≔ equiv_inverse_map (Id (UnivCover A a) u v) (UnivCoverPath A a u v) (univ_cover_path_equiv A a u v) w

{` lemma:universal-cover-simply-connected, first part: Ũ_a A is connected. `}
def univ_cover_merely_from_point (A : Type) (a : A) (u : UnivCover A a)
  : Mere (Id (UnivCover A a) (univ_cover_point A a) u)
  ≔ set_trunc_induction (Id A a (u .fst)) (α ↦ Mere (Id (UnivCover A a) (univ_cover_point A a) (u .fst, α)))
      (α ↦ prop_is_set (Mere (Id (UnivCover A a) (univ_cover_point A a) (u .fst, α)))
        (mere_isprop (Id (UnivCover A a) (univ_cover_point A a) (u .fst, α))))
      (p ↦ mere (Id (UnivCover A a) (univ_cover_point A a) (u .fst, set_trunc (Id A a (u .fst)) p))
        (univ_cover_path_from A a (univ_cover_point A a) (u .fst, set_trunc (Id A a (u .fst)) p)
          (p, refl (set_trunc (Id A a (u .fst))) (concat_1p A a (u .fst) p))))
      (u .snd)

def univ_cover_connected (A : Type) (a : A) : Connected (UnivCover A a)
  ≔ connected_from_point (UnivCover A a) (univ_cover_point A a) (univ_cover_merely_from_point A a)

{` lemma:universal-cover-simply-connected, second part:
   ((a, |refl|) = (a, |refl|)) ≃ Σ(p : a = a) ‖refl = p‖, the component of
   refl in a = a. The map sends r to (r .fst, …). `}
def trunc_refl_mere_equiv (A : Type) (a : A) (p : Id A a a)
  : Equiv (Id (SetTrunc (Id A a a)) (trunc_path_compose A a a a (set_trunc (Id A a a) p) (set_trunc (Id A a a) (refl a)))
        (set_trunc (Id A a a) (refl a)))
      (Mere (Id (Id A a a) (refl a) p))
  ≔ compose_equiv
      (Id (SetTrunc (Id A a a)) (set_trunc (Id A a a) (concat A a a a (refl a) p)) (set_trunc (Id A a a) (refl a)))
      (Mere (Id (Id A a a) (concat A a a a (refl a) p) (refl a)))
      (Mere (Id (Id A a a) (refl a) p))
      (set_trunc_paths (Id A a a) (concat A a a a (refl a) p) (refl a))
      (iff_equiv (Mere (Id (Id A a a) (concat A a a a (refl a) p) (refl a))) (Mere (Id (Id A a a) (refl a) p))
        (mere_isprop (Id (Id A a a) (concat A a a a (refl a) p) (refl a))) (mere_isprop (Id (Id A a a) (refl a) p))
        (trunc_map native_truncation (Id (Id A a a) (concat A a a a (refl a) p) (refl a)) (Id (Id A a a) (refl a) p)
          (e ↦ concat (Id A a a) (refl a) (concat A a a a (refl a) p) p
            (inverse (Id A a a) (concat A a a a (refl a) p) (refl a) e) (concat_1p A a a p)))
        (trunc_map native_truncation (Id (Id A a a) (refl a) p) (Id (Id A a a) (concat A a a a (refl a) p) (refl a))
          (e ↦ concat (Id A a a) (concat A a a a (refl a) p) p (refl a) (concat_1p A a a p)
            (inverse (Id A a a) (refl a) p e))))

def univ_cover_loops_component_equiv (A : Type) (a : A)
  : Equiv (Loop (univ_cover_pointed A a)) (NativeComponent (Id A a a) (refl a))
  ≔ compose_equiv (Loop (univ_cover_pointed A a)) (UnivCoverPath A a (univ_cover_point A a) (univ_cover_point A a))
      (NativeComponent (Id A a a) (refl a))
      (univ_cover_path_equiv A a (univ_cover_point A a) (univ_cover_point A a))
      (family_equiv (Id A a a)
        (p ↦ Id (SetTrunc (Id A a a)) (trunc_path_compose A a a a (set_trunc (Id A a a) p) (set_trunc (Id A a a) (refl a)))
          (set_trunc (Id A a a) (refl a)))
        (p ↦ Mere (Id (Id A a a) (refl a) p))
        (trunc_refl_mere_equiv A a))

def univ_cover_loops_component_map (A : Type) (a : A) (r : Loop (univ_cover_pointed A a))
  : Id (Id A a a) (univ_cover_loops_component_equiv A a .map r .fst) (r .fst)
  ≔ refl (r .fst)

def univ_cover_loops_connected (A : Type) (a : A) : Connected (Loop (univ_cover_pointed A a))
  ≔ connected_equiv (NativeComponent (Id A a a) (refl a)) (Loop (univ_cover_pointed A a))
      (canonical_inverse_equiv (Loop (univ_cover_pointed A a)) (NativeComponent (Id A a a) (refl a))
        (univ_cover_loops_component_equiv A a))
      .map (native_component_connected (Id A a a) (refl a))

def univ_cover_simply_connected (A : Type) (a : A) : SimplyConnected (univ_cover_pointed A a)
  ≔ (univ_cover_connected A a, univ_cover_loops_connected A a)
