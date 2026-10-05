export "1721-blass-bounded-choice"

{` Forward orbits of an endomap f of a type with decidable equality, for the
   proof of Blass's Theorem 6. y is reachable from x if y = f^i(x) for some
   natural number i (merely). If every point is periodic, reachability is an
   equivalence relation and is decidable; for an injective endomap of a
   finite set every point is periodic (pigeonhole), and the classes of the
   relation are the orbits (cycles) of the permutation f. `}
def BsixReach (A : Type) (f : A → A) (x y : A) : Type ≔ Mere (Σ Nat (i ↦ Id A y (iterate A f i x)))

def BsixPeriod (A : Type) (f : A → A) (x : A) : Type ≔ Σ Nat (p ↦ Id A (iterate A f (suc. p) x) x)

def bsix_reach_refl (A : Type) (f : A → A) (x : A) : BsixReach A f x x
  ≔ mere (Σ Nat (i ↦ Id A x (iterate A f i x))) (zero., refl x)

def bsix_reach_step (A : Type) (f : A → A) (x : A) : BsixReach A f x (f x)
  ≔ mere (Σ Nat (i ↦ Id A (f x) (iterate A f i x))) (suc. zero., refl (f x))

def bsix_reach_trans (A : Type) (f : A → A) (x y z : A) (r : BsixReach A f x y) (s : BsixReach A f y z)
  : BsixReach A f x z
  ≔ mere_rec (Σ Nat (i ↦ Id A y (iterate A f i x))) (BsixReach A f x z) (mere_isprop (Σ Nat (i ↦ Id A z (iterate A f i x))))
      (u ↦ trunc_map native_truncation (Σ Nat (j ↦ Id A z (iterate A f j y))) (Σ Nat (i ↦ Id A z (iterate A f i x)))
        (v ↦ (add (u .fst) (v .fst),
          concat A z (iterate A f (v .fst) y) (iterate A f (add (u .fst) (v .fst)) x) (v .snd)
            (concat A (iterate A f (v .fst) y) (iterate A f (v .fst) (iterate A f (u .fst) x))
              (iterate A f (add (u .fst) (v .fst)) x)
              (map_path A A (iterate A f (v .fst)) y (iterate A f (u .fst) x) (u .snd))
              (inverse A (iterate A f (add (u .fst) (v .fst)) x) (iterate A f (v .fst) (iterate A f (u .fst) x))
                (iterate_add A f (u .fst) (v .fst) x))))) s) r

{` A witness y = f^i(x) can be shortened below a period of x: the least
   witness is at most p when f^(p+1)(x) = x. `}
def bsix_minimum_bounded (A : Type) (f : A → A) (x y : A) (p : Nat)
  (per : Id A (iterate A f (suc. p) x) x) (j : Nat) (pj : Id A y (iterate A f j x))
  (minimal : (m : Nat) → Id A y (iterate A f m x) → BookLe j m) : Le j p
  ≔ match le_decidable j p [
  | inl. h ↦ h
  | inr. no ↦
      let lt : Lt p j ≔ match le_total j p [
        | inl. h ↦ absurd (Lt p j) (no h)
        | inr. h ↦ le_not_equal_lt p j h (e ↦ no (le_from_equal j p (inverse Nat p j e))) ] in
      let w ≔ le_to_book (suc. p) j lt in
      let d ≔ w .fst in
      let pd : Id A y (iterate A f d x)
        ≔ concat A y (iterate A f j x) (iterate A f d x) pj
            (concat A (iterate A f j x) (iterate A f (add (suc. p) d) x) (iterate A f d x)
              (map_path Nat A (k ↦ iterate A f k x) j (add (suc. p) d)
                (concat Nat j (add d (suc. p)) (add (suc. p) d) (inverse Nat (add d (suc. p)) j (w .snd))
                  (add_comm d (suc. p))))
              (concat A (iterate A f (add (suc. p) d) x) (iterate A f d (iterate A f (suc. p) x)) (iterate A f d x)
                (iterate_add A f (suc. p) d x)
                (map_path A A (iterate A f d) (iterate A f (suc. p) x) x per))) in
      let jd : Le j d ≔ le_from_book j d (minimal d pd) in
      let dj : Le (suc. d) j
        ≔ transport Nat (k ↦ Le (suc. d) k) (add d (suc. p)) j (w .snd) (le_add_base d p) in
      absurd (Le j p) (lt_irrefl d (le_trans (suc. d) j d dj jd)) ]

def bsix_bounded_witness (A : Type) (dA : DecidableEquality A) (f : A → A) (x y : A) (per : BsixPeriod A f x)
  (w : Σ Nat (i ↦ Id A y (iterate A f i x)))
  : Σ Nat (j ↦ Product (Le j (per .fst)) (Id A y (iterate A f j x)))
  ≔ let m ≔ minimum_from_witness (j ↦ Id A y (iterate A f j x)) (j ↦ dA y (iterate A f j x)) (w .fst) (w .snd) in
    (m .fst, (bsix_minimum_bounded A f x y (per .fst) (per .snd) (m .fst) (m .snd .fst) (m .snd .snd), m .snd .fst))

{` Symmetry, using a (mere) period of the starting point. `}
def bsix_reach_symm (A : Type) (dA : DecidableEquality A) (f : A → A) (x y : A) (mper : Mere (BsixPeriod A f x))
  (r : BsixReach A f x y) : BsixReach A f y x
  ≔ mere_rec (BsixPeriod A f x) (BsixReach A f y x) (mere_isprop (Σ Nat (i ↦ Id A x (iterate A f i y))))
      (per ↦ mere_rec (Σ Nat (i ↦ Id A y (iterate A f i x))) (BsixReach A f y x)
        (mere_isprop (Σ Nat (i ↦ Id A x (iterate A f i y))))
        (w ↦ let b ≔ bsix_bounded_witness A dA f x y per w in
          let j ≔ b .fst in
          let c ≔ le_to_book j (suc. (per .fst)) (le_step j (per .fst) (b .snd .fst)) in
          mere (Σ Nat (i ↦ Id A x (iterate A f i y))) (c .fst,
            inverse A (iterate A f (c .fst) y) x
              (concat A (iterate A f (c .fst) y) (iterate A f (c .fst) (iterate A f j x)) x
                (map_path A A (iterate A f (c .fst)) y (iterate A f j x) (b .snd .snd))
                (concat A (iterate A f (c .fst) (iterate A f j x)) (iterate A f (add j (c .fst)) x) x
                  (inverse A (iterate A f (add j (c .fst)) x) (iterate A f (c .fst) (iterate A f j x))
                    (iterate_add A f j (c .fst) x))
                  (concat A (iterate A f (add j (c .fst)) x) (iterate A f (suc. (per .fst)) x) x
                    (map_path Nat A (k ↦ iterate A f k x) (add j (c .fst)) (suc. (per .fst))
                      (concat Nat (add j (c .fst)) (add (c .fst) j) (suc. (per .fst)) (add_comm j (c .fst)) (c .snd)))
                    (per .snd))))))
        r) mper

{` Decidability by bounded search up to the period. `}
def bsix_bounded_exists (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (p : Nat)
  : Decidable (Σ Nat (j ↦ Product (Le j p) (P j)))
  ≔ let s ≔ bounded_search P d (suc. p) in
    match lt_decidable (s .value) (suc. p) [
    | inl. h ↦ inl. (s .value, (h, s .found h))
    | inr. no ↦ inr. (w ↦ no (le_trans (s .value) (w .fst) p (s .minimal (w .fst) (w .snd .snd)) (w .snd .fst))) ]

def bsix_reach_decidable (A : Type) (dA : DecidableEquality A) (f : A → A) (x y : A) (mper : Mere (BsixPeriod A f x))
  : Decidable (BsixReach A f x y)
  ≔ mere_rec (BsixPeriod A f x) (Decidable (BsixReach A f x y))
      (decidability_prop (BsixReach A f x y) (mere_isprop (Σ Nat (i ↦ Id A y (iterate A f i x)))))
      (per ↦ match bsix_bounded_exists (j ↦ Id A y (iterate A f j x)) (j ↦ dA y (iterate A f j x)) (per .fst) [
        | inl. w ↦ inl. (mere (Σ Nat (i ↦ Id A y (iterate A f i x))) (w .fst, w .snd .snd))
        | inr. no ↦ inr. (mere_rec (Σ Nat (i ↦ Id A y (iterate A f i x))) Empty empty_prop
            (w ↦ no (bsix_bounded_witness A dA f x y per w))) ])
      mper

def bsix_reach_relation (A : Type) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A)
  : EquivalenceRelation A
  ≔ ((x y ↦ (BsixReach A f x y, mere_isprop (Σ Nat (i ↦ Id A y (iterate A f i x))))),
      bsix_reach_refl A f,
      (x y r ↦ bsix_reach_symm A dA f x y (mper x) r),
      bsix_reach_trans A f)

def bsix_reach_relation_decidable (A : Type) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x))
  (dA : DecidableEquality A) : DecidableRelation A (bsix_reach_relation A f mper dA)
  ≔ x y ↦ bsix_reach_decidable A dA f x y (mper x)

{` Every point of an injective endomap of Fin N is periodic (pigeonhole on
   the N+1 iterates x, f(x), …, f^N(x)). `}
def bsix_iterate_injective (A : Type) (f : A → A) (inj : PathReflecting A A f) (m : Nat)
  : PathReflecting A A (iterate A f m)
  ≔ match m [
  | zero. ↦ a b e ↦ e
  | suc. k ↦ a b e ↦ bsix_iterate_injective A f inj k a b (inj (iterate A f k a) (iterate A f k b) e) ]

def bsix_period_from_difference (A : Type) (f : A → A) (inj : PathReflecting A A f) (x : A) (a d : Nat)
  (nz : Id Nat d zero. → Empty) (e : Id A (iterate A f a x) (iterate A f (add d a) x)) : BsixPeriod A f x
  ≔ match d [
  | zero. ↦ absurd (BsixPeriod A f x) (nz (refl (zero. : Nat)))
  | suc. q ↦ (q, bsix_iterate_injective A f inj a (iterate A f (suc. q) x) x
      (inverse A (iterate A f a x) (iterate A f a (iterate A f (suc. q) x))
        (concat A (iterate A f a x) (iterate A f (add (suc. q) a) x) (iterate A f a (iterate A f (suc. q) x))
          e (iterate_add A f (suc. q) a x)))) ]

def bsix_period_from_collision (A : Type) (f : A → A) (inj : PathReflecting A A f) (x : A) (a b : Nat)
  (ne : Id Nat a b → Empty) (e : Id A (iterate A f a x) (iterate A f b x)) : BsixPeriod A f x
  ≔ match le_total a b [
  | inl. h ↦ let w ≔ le_to_book a b h in
      bsix_period_from_difference A f inj x a (w .fst)
        (z ↦ ne (concat Nat a (add zero. a) b (inverse Nat (add zero. a) a (add_zero_left a))
          (transport Nat (k ↦ Id Nat (add k a) b) (w .fst) zero. z (w .snd))))
        (concat A (iterate A f a x) (iterate A f b x) (iterate A f (add (w .fst) a) x) e
          (map_path Nat A (k ↦ iterate A f k x) b (add (w .fst) a) (inverse Nat (add (w .fst) a) b (w .snd))))
  | inr. h ↦ let w ≔ le_to_book b a h in
      bsix_period_from_difference A f inj x b (w .fst)
        (z ↦ ne (inverse Nat b a (concat Nat b (add zero. b) a (inverse Nat (add zero. b) b (add_zero_left b))
          (transport Nat (k ↦ Id Nat (add k b) a) (w .fst) zero. z (w .snd)))))
        (concat A (iterate A f b x) (iterate A f a x) (iterate A f (add (w .fst) b) x)
          (inverse A (iterate A f a x) (iterate A f b x) e)
          (map_path Nat A (k ↦ iterate A f k x) a (add (w .fst) b) (inverse Nat (add (w .fst) b) a (w .snd)))) ]

def bsix_fin_period (N : Nat) (f : Fin N → Fin N) (inj : PathReflecting (Fin N) (Fin N) f) (x : Fin N)
  : BsixPeriod (Fin N) f x
  ≔ let c ≔ fin_pigeonhole N (i ↦ iterate (Fin N) f (fin_index (suc. N) i) x) in
    bsix_period_from_collision (Fin N) f inj x (fin_index (suc. N) (c .left)) (fin_index (suc. N) (c .right))
      (e ↦ c .distinct (fin_index_injective (suc. N) (c .left) (c .right) e)) (c .same)

def BsixPeriodic (B : Type) : Type ≔ (f : B → B) → PathReflecting B B f → (x : B) → BsixPeriod B f x

def bsix_mere_periods (N : Nat) (A : Type) (p : Mere (Id Type (Fin N) A)) (f : A → A)
  (inj : PathReflecting A A f) (x : A) : Mere (BsixPeriod A f x)
  ≔ trunc_map native_truncation (Id Type (Fin N) A) (BsixPeriod A f x)
      (q ↦ transport Type BsixPeriodic (Fin N) A q (bsix_fin_period N) f inj x) p

{` Litmus: on Fin 3 the successor cycle has period 3 at every point; the
   swap (0 1) of Fin 2 reaches 1 from 0 in one step. `}
def bsix_fin_two_swap : Fin (suc. (suc. zero.)) → Fin (suc. (suc. zero.))
  ≔ [ inl. a ↦ inr. star. | inr. u ↦ inl. (inr. star.) ]

def bsix_fin_two_swap_period : Id (Fin (suc. (suc. zero.))) (iterate (Fin (suc. (suc. zero.))) bsix_fin_two_swap (suc. (suc. zero.)) (inr. star.)) (inr. star.)
  ≔ refl (inr. star. : Fin (suc. (suc. zero.)))
