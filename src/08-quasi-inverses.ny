export "06-equivalences"

{` lem:weq-iso for general types, with no set-truncation hypothesis, proved
   with native Id, J and the path algebra of module 04 only. The unit is
   improved to eta' a = eta (g (f a))⁻¹ · (ap g (epsilon (f a)) · eta a),
   the formula of the HoTT book's Theorem 4.2.3 with f and g exchanged, and
   the triangle ap f (eta' a) = epsilon (f a) is proved directly. Each fibre
   over b is then a retract of the contractible type Σ A (x ↦ Id A x (g b));
   its centre is (g b, epsilon b), so equiv_inverse_map and equiv_counit of
   the resulting equivalence compute to g and epsilon. `}

{` Right cancellation: p · r = q · r implies p = q. `}
def concat_cancel_right (A : Type) (x y z : A) (p q : Id A x y)
  (r : Id A y z)
  (e : Id (Id A x z) (concat A x y z p r) (concat A x y z q r))
  : Id (Id A x y) p q
  ≔ J A y
      (z r ↦
       Id (Id A x z) (concat A x y z p r) (concat A x y z q r)
       → Id (Id A x y) p q)
      (e0 ↦ calc
        p
        = concat A x y y p (refl y) by concat_p1 A x y p
        = concat A x y y q (refl y) by e0
        = q by concat_p1 A x y q ∎) z r e

{` p⁻¹ · (p · q) = q. `}
def concat_left_inverse_cancel (A : Type) (x y z : A) (p : Id A x y)
  (q : Id A y z)
  : Id (Id A y z) (concat A y x z (inverse A x y p) (concat A x y z p q)) q
  ≔ calc
      concat A y x z (inverse A x y p) (concat A x y z p q)
      = concat A y y z (concat A y x y (inverse A x y p) p) q
        by concat_assoc A y x y z (inverse A x y p) p q
      = concat A y y z (refl y) q
        by refl ((r ↦ concat A y y z r q) : Id A y y → Id A y z)
             (concat_inverse_left A x y p)
      = q by concat_1p A y z q ∎

{` A homotopy h from k to the identity commutes with k:
   ap k (h x) = h (k x) (HoTT book Lemma 2.4.3 with Corollary 2.4.4). `}
def homotopy_ap_self (A : Type) (k : A → A) (h : (x : A) → Id A (k x) x)
  (x : A)
  : Id (Id A (k (k x)) (k x)) (refl k (h x)) (h (k x))
  ≔ concat_cancel_right A (k (k x)) (k x) x (refl k (h x)) (h (k x)) (h x)
      (naturality A A k (y ↦ y) h (k x) x (h x))

{` The improved unit eta' a = eta (g (f a))⁻¹ · (ap g (epsilon (f a)) · eta a). `}
def quasi_inverse_unit (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) (a : A)
  : Id A (g (f a)) a
  ≔ concat A (g (f a)) (g (f (g (f a)))) a
      (inverse A (g (f (g (f a)))) (g (f a)) (eta (g (f a))))
      (concat A (g (f (g (f a)))) (g (f a)) a (refl g (epsilon (f a)))
         (eta a))

{` The half-adjoint triangle: ap f (eta' a) = epsilon (f a). `}
def quasi_inverse_coherence (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) (a : A)
  : Id (Id B (f (g (f a))) (f a))
      (refl f (quasi_inverse_unit A B f g eta epsilon a)) (epsilon (f a))
  ≔ let a1 ≔ g (f a) in
    let a2 ≔ g (f (g (f a))) in
    let b1 ≔ f (g (f a)) in
    let b2 ≔ f (g (f (g (f a)))) in
    let n1 ≔ refl f (eta a1) in
    calc
      refl f (quasi_inverse_unit A B f g eta epsilon a)
      = concat B b1 b2 (f a) (refl f (inverse A a2 a1 (eta a1)))
          (refl f (concat A a2 a1 a (refl g (epsilon (f a))) (eta a)))
        by map_path_concat A B f a1 a2 a (inverse A a2 a1 (eta a1))
             (concat A a2 a1 a (refl g (epsilon (f a))) (eta a))
      = concat B b1 b2 (f a) (inverse B b2 b1 n1)
          (refl f (concat A a2 a1 a (refl g (epsilon (f a))) (eta a)))
        by refl
             ((r ↦
               concat B b1 b2 (f a) r
                 (refl f (concat A a2 a1 a (refl g (epsilon (f a))) (eta a))))
              : Id B b1 b2 → Id B b1 (f a))
             (map_path_inverse A B f a2 a1 (eta a1))
      = concat B b1 b2 (f a) (inverse B b2 b1 n1)
          (concat B b2 b1 (f a) (refl f (refl g (epsilon (f a))))
             (refl f (eta a)))
        by refl (concat B b1 b2 (f a) (inverse B b2 b1 n1))
             (map_path_concat A B f a2 a1 a (refl g (epsilon (f a))) (eta a))
      = concat B b1 b2 (f a) (inverse B b2 b1 n1)
          (concat B b2 b1 (f a) (epsilon b1) (refl f (eta a)))
        by refl (concat B b1 b2 (f a) (inverse B b2 b1 n1))
             (refl
                ((r ↦ concat B b2 b1 (f a) r (refl f (eta a)))
                 : Id B b2 b1 → Id B b2 (f a))
                (homotopy_ap_self B (y ↦ f (g y)) epsilon (f a)))
      = concat B b1 b2 (f a) (inverse B b2 b1 n1)
          (concat B b2 b1 (f a) (refl (y ↦ f (g y)) (refl f (eta a)))
             (epsilon (f a)))
        by refl (concat B b1 b2 (f a) (inverse B b2 b1 n1))
             (naturality B B (y ↦ f (g y)) (y ↦ y) epsilon b1 (f a)
                (refl f (eta a)))
      = concat B b1 b2 (f a) (inverse B b2 b1 n1)
          (concat B b2 b1 (f a) n1 (epsilon (f a)))
        by refl (concat B b1 b2 (f a) (inverse B b2 b1 n1))
             (refl
                ((r ↦ concat B b2 b1 (f a) r (epsilon (f a)))
                 : Id B b2 b1 → Id B b2 (f a))
                (refl ((r ↦ refl f r) : Id A a2 a1 → Id B b2 b1)
                   (homotopy_ap_self A (x ↦ g (f x)) eta a)))
      = epsilon (f a)
        by concat_left_inverse_cancel B b2 b1 (f a) n1 (epsilon (f a)) ∎

{` A fibre point (a, q) gives the path eta' a⁻¹ · ap g q from a to g b. `}
def quasi_inverse_fiber_section (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) (b : B) (t : Fiber A B f b)
  : Σ A (x ↦ Id A x (g b))
  ≔ (t .fst,
     concat A (t .fst) (g (f (t .fst))) (g b)
       (inverse A (g (f (t .fst))) (t .fst)
          (quasi_inverse_unit A B f g eta epsilon (t .fst))) (refl g (t .snd)))

{` A path p from a to g b gives the fibre point (a, ap f p · epsilon b). `}
def quasi_inverse_fiber_retraction (A B : Type) (f : A → B) (g : B → A)
  (epsilon : (b : B) → Id B (f (g b)) b) (b : B)
  (u : Σ A (x ↦ Id A x (g b)))
  : Fiber A B f b
  ≔ (u .fst, concat B (f (u .fst)) (f (g b)) b (refl f (u .snd)) (epsilon b))

{` The retraction undoes the section on the path component; J on q, whose
   reflexive case is the half-adjoint triangle. `}
def quasi_inverse_fiber_path (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) (a : A) (b : B)
  (q : Id B (f a) b)
  : Id (Id B (f a) b)
      (concat B (f a) (f (g b)) b
         (refl f
            (concat A a (g (f a)) (g b)
               (inverse A (g (f a)) a (quasi_inverse_unit A B f g eta epsilon a))
               (refl g q))) (epsilon b)) q
  ≔ let fa ≔ f a in
    let b1 ≔ f (g (f a)) in
    let u ≔ quasi_inverse_unit A B f g eta epsilon a in
    J B fa
      (y q ↦
       Id (Id B fa y)
         (concat B fa (f (g y)) y
            (refl f
               (concat A a (g fa) (g y) (inverse A (g fa) a u) (refl g q)))
            (epsilon y)) q)
      (calc
        concat B fa b1 fa
          (refl f
             (concat A a (g fa) (g fa) (inverse A (g fa) a u) (refl (g fa))))
          (epsilon fa)
        = concat B fa b1 fa (refl f (inverse A (g fa) a u)) (epsilon fa)
          by refl
               ((r ↦ concat B fa b1 fa (refl f r) (epsilon fa))
                : Id A a (g fa) → Id B fa fa)
               (concat_p1 A a (g fa) (inverse A (g fa) a u))
        = concat B fa b1 fa (inverse B b1 fa (refl f u)) (epsilon fa)
          by refl
               ((r ↦ concat B fa b1 fa r (epsilon fa))
                : Id B fa b1 → Id B fa fa)
               (map_path_inverse A B f (g fa) a u)
        = concat B fa b1 fa (inverse B b1 fa (refl f u)) (refl f u)
          by refl (concat B fa b1 fa (inverse B b1 fa (refl f u)))
               (quasi_inverse_coherence A B f g eta epsilon a)
        = refl fa by concat_inverse_left B b1 fa (refl f u) ∎) b q

{` Each fibre is contractible, with centre (g b, epsilon b): a retract of
   the contractible type Σ A (x ↦ Id A x (g b)), recentred by concat_1p. `}
def quasi_inverse_fiber_contractible (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) (b : B)
  : isContr (Fiber A B f b)
  ≔ let c ≔
      contractible_retract (Σ A (x ↦ Id A x (g b))) (Fiber A B f b)
        (path_to_contractible A (g b))
        (quasi_inverse_fiber_retraction A B f g epsilon b)
        (quasi_inverse_fiber_section A B f g eta epsilon b)
        (t ↦
         (refl (t .fst),
          quasi_inverse_fiber_path A B f g eta epsilon (t .fst) b (t .snd))) in
    ((g b, epsilon b),
     t ↦
     concat (Fiber A B f b) t (c .center) (g b, epsilon b) (c .contract t)
       (refl (g b), concat_1p B (f (g b)) b (epsilon b)))

{` lem:weq-iso, general types, with no set-truncation hypothesis. `}
def quasi_inverse_equiv (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a)
  (epsilon : (b : B) → Id B (f (g b)) b) : Equiv A B
  ≔ (f, b ↦ quasi_inverse_fiber_contractible A B f g eta epsilon b)
