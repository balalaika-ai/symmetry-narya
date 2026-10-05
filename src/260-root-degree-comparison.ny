export "224-constructed-circle-checks"
export "244-k-cycle-count"
export "232-n-image-universal-property"
export "211-exponential-fibers"

def infinite_pointed : Pointed ≔ (InfiniteCycles, infinite_endomorphism_point)

{` Evaluation of a path of infinite cycles on the underlying carriers. `}
def infinite_path_evaluate (s t : InfiniteCycles) (p : Id InfiniteCycles s t) (x : s .fst .fst) : t .fst .fst
  ≔ carrier_path_evaluate InfiniteCycles (u ↦ u .fst .fst) s t p x

def infinite_conjugate_evaluate (a x : InfiniteCycles) (p : Id InfiniteCycles a x) (l : Id InfiniteCycles x x)
  (y : a .fst .fst)
  : Id (a .fst .fst) (infinite_path_evaluate a a (pointed_loop_conjugate InfiniteCycles a x p l) y)
      (infinite_path_evaluate x a (inverse InfiniteCycles a x p)
        (infinite_path_evaluate x x l (infinite_path_evaluate a x p y)))
  ≔ concat (a .fst .fst) (infinite_path_evaluate a a (pointed_loop_conjugate InfiniteCycles a x p l) y)
      (infinite_path_evaluate x a (concat InfiniteCycles x x a l (inverse InfiniteCycles a x p)) (infinite_path_evaluate a x p y))
      (infinite_path_evaluate x a (inverse InfiniteCycles a x p)
        (infinite_path_evaluate x x l (infinite_path_evaluate a x p y)))
      (carrier_path_evaluate_concat InfiniteCycles (u ↦ u .fst .fst) a x a p
        (concat InfiniteCycles x x a l (inverse InfiniteCycles a x p)) y)
      (carrier_path_evaluate_concat InfiniteCycles (u ↦ u .fst .fst) x x a l (inverse InfiniteCycles a x p)
        (infinite_path_evaluate a x p y))

def infinite_inverse_roundtrip (s t : InfiniteCycles) (p : Id InfiniteCycles s t) (y : s .fst .fst)
  : Id (s .fst .fst) (infinite_path_evaluate t s (inverse InfiniteCycles s t p) (infinite_path_evaluate s t p y)) y
  ≔ transport_inverse_roundtrip InfiniteCycles (u ↦ u .fst .fst) s t p y

{` The first component of ap_{cdg_m}(e,!) is id × e: evaluation of the
   image of a path under the m-th root is the identity on the Fin m factor. `}
def root_infinite_ap_evaluate (n : Nat) (s t : InfiniteCycles) (q : Id InfiniteCycles s t)
  (k : Fin (suc. n)) (x : s .fst .fst)
  : Id (Product (Fin (suc. n)) (t .fst .fst))
      (infinite_path_evaluate (formal_root_infinite_component n s) (formal_root_infinite_component n t)
        (refl (formal_root_infinite_component n) q) (k, x))
      (k, infinite_path_evaluate s t q x)
  ≔ J InfiniteCycles s
      (t q ↦ Id (Product (Fin (suc. n)) (t .fst .fst))
        (infinite_path_evaluate (formal_root_infinite_component n s) (formal_root_infinite_component n t)
          (refl (formal_root_infinite_component n) q) (k, x))
        (k, infinite_path_evaluate s t q x))
      (concat (Product (Fin (suc. n)) (s .fst .fst))
        (infinite_path_evaluate (formal_root_infinite_component n s) (formal_root_infinite_component n s)
          (refl (formal_root_infinite_component n s)) (k, x))
        (k, x) (k, infinite_path_evaluate s s (refl s) x)
        (transport_refl Type (X ↦ X) (Product (Fin (suc. n)) (s .fst .fst)) (k, x))
        (refl k, inverse (s .fst .fst) (infinite_path_evaluate s s (refl s) x) x
          (transport_refl Type (X ↦ X) (s .fst .fst) x)))
      t q

{` The identification phi : (Fin m × Z, root s) = (Z, s) evaluates as k + mz. `}
def root_infinite_path_evaluation (n : Nat) (w : Product (Fin (suc. n)) Int)
  : Id Int (cycle_path_evaluate (cycle_root n infinite_cycle) infinite_cycle (root_infinite_cycle_path n) w)
      (integer_radix_value (suc. n) w)
  ≔ inverse_evaluation_agreement (Id Cycles (cycle_root n infinite_cycle) infinite_cycle)
      (PermutationIsomorphisms (cycle_root n infinite_cycle .fst) (infinite_cycle .fst)) Int
      (cycle_paths_equiv (cycle_root n infinite_cycle) infinite_cycle)
      (p ↦ cycle_path_evaluate (cycle_root n infinite_cycle) infinite_cycle p w) (h ↦ h .fst .map w)
      (p ↦ refl (cycle_path_evaluate (cycle_root n infinite_cycle) infinite_cycle p w))
      (native_equivalence (Product (Fin (suc. n)) Int) Int
        (integer_radix_equiv (suc. n) (lt_to_book zero. (suc. n) star.)), integer_root_radix_commutes n)

{` The pointing path pt = cdg_m(pt) of formal_root_infinite_pointed. `}
def root_pointing (n : Nat)
  : Id InfiniteCycles infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
  ≔ formal_root_infinite_pointed n .snd

def root_pointing_underlying (n : Nat)
  : Id (Id Endomorphisms integer_endomorphism (formal_root n integer_endomorphism)) (root_pointing n .fst)
      (inverse Endomorphisms (formal_root n integer_endomorphism) integer_endomorphism (formal_root_integer_path n))
  ≔ equiv_counit (Id InfiniteCycles infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point))
      (Id Endomorphisms integer_endomorphism (formal_root n integer_endomorphism))
      (subtype_path_equiv Endomorphisms (u ↦ Mere (Id Endomorphisms integer_endomorphism u))
        (u ↦ mere_isprop (Id Endomorphisms integer_endomorphism u))
        infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point))
      (inverse Endomorphisms (formal_root n integer_endomorphism) integer_endomorphism (formal_root_integer_path n))

def root_pointing_radix (n : Nat) (y : Int)
  : Id Int (integer_radix_value (suc. n)
      (infinite_path_evaluate infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
        (root_pointing n) y)) y
  ≔ let E ≔ ((e ↦ e .fst) : Endomorphisms → Type) in
    let R ≔ formal_root n integer_endomorphism in
    let frip ≔ formal_root_integer_path n in
    let w ≔ infinite_path_evaluate infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
      (root_pointing n) y in
    calc
      integer_radix_value (suc. n) w
      = transport Endomorphisms E R integer_endomorphism frip w
        by inverse Int (transport Endomorphisms E R integer_endomorphism frip w) (integer_radix_value (suc. n) w)
          (root_infinite_path_evaluation n w)
      = transport Endomorphisms E R integer_endomorphism frip
          (transport Endomorphisms E integer_endomorphism R (inverse Endomorphisms R integer_endomorphism frip) y)
        by refl (transport Endomorphisms E R integer_endomorphism frip)
          (refl ((P ↦ transport Endomorphisms E integer_endomorphism R P y)
            : Id Endomorphisms integer_endomorphism R → R .fst) (root_pointing_underlying n))
      = transport Endomorphisms E R integer_endomorphism
          (inverse Endomorphisms integer_endomorphism R (inverse Endomorphisms R integer_endomorphism frip))
          (transport Endomorphisms E integer_endomorphism R (inverse Endomorphisms R integer_endomorphism frip) y)
        by refl ((P ↦ transport Endomorphisms E R integer_endomorphism P
            (transport Endomorphisms E integer_endomorphism R (inverse Endomorphisms R integer_endomorphism frip) y))
            : Id Endomorphisms R integer_endomorphism → Int)
          (inverse (Id Endomorphisms R integer_endomorphism)
            (inverse Endomorphisms integer_endomorphism R (inverse Endomorphisms R integer_endomorphism frip)) frip
            (inverse_inverse Endomorphisms R integer_endomorphism frip))
      = y by transport_inverse_roundtrip Endomorphisms E integer_endomorphism R
          (inverse Endomorphisms R integer_endomorphism frip) y ∎

def root_radix_injective (n : Nat) (u v : Product (Fin (suc. n)) Int)
  (p : Id Int (integer_radix_value (suc. n) u) (integer_radix_value (suc. n) v)) : Id (Product (Fin (suc. n)) Int) u v
  ≔ equivalence_injective (Product (Fin (suc. n)) Int) Int
      (native_equivalence (Product (Fin (suc. n)) Int) Int (integer_radix_equiv (suc. n) (lt_to_book zero. (suc. n) star.)))
      u v p

def root_pointing_zero (n : Nat)
  : Id (Product (Fin (suc. n)) Int)
      (infinite_path_evaluate infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
        (root_pointing n) int_zero)
      (inr. star., int_zero)
  ≔ root_radix_injective n
      (infinite_path_evaluate infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
        (root_pointing n) int_zero)
      (inr. star., int_zero) (root_pointing_radix n int_zero)

def root_pointing_inverse (n : Nat) (w : Product (Fin (suc. n)) Int)
  : Id Int
      (infinite_path_evaluate (formal_root_infinite_component n infinite_endomorphism_point) infinite_endomorphism_point
        (inverse InfiniteCycles infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
          (root_pointing n)) w)
      (integer_radix_value (suc. n) w)
  ≔ let pt ≔ infinite_endomorphism_point in let r ≔ formal_root_infinite_component n pt in
    let v ≔ infinite_path_evaluate pt r (root_pointing n) (integer_radix_value (suc. n) w) in
    let back ≔ ((u ↦ infinite_path_evaluate r pt (inverse InfiniteCycles pt r (root_pointing n)) u)
      : Product (Fin (suc. n)) Int → Int) in
    calc
      back w = back v
        by refl back (inverse (Product (Fin (suc. n)) Int) v w
          (root_radix_injective n v w (root_pointing_radix n (integer_radix_value (suc. n) w))))
      = integer_radix_value (suc. n) w
        by infinite_inverse_roundtrip pt r (root_pointing n) (integer_radix_value (suc. n) w) ∎

{` Conjugation of a loop by the pointing path pt = cdg_m(pt) multiplies the
   loop coordinate by m: the transport of id × e along phi(k,z) = k + mz. `}
def root_loop_coordinate (n : Nat)
  (l : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
  : Id Int (infinite_cycle_loop_coordinate
      (pointed_loop_conjugate InfiniteCycles infinite_endomorphism_point
        (formal_root_infinite_component n infinite_endomorphism_point) (root_pointing n)
        (refl (formal_root_infinite_component n) l)))
      (int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate l))
  ≔ let pt ≔ infinite_endomorphism_point in let r ≔ formal_root_infinite_component n pt in
    let back ≔ ((u ↦ infinite_path_evaluate r pt (inverse InfiniteCycles pt r (root_pointing n)) u)
      : Product (Fin (suc. n)) Int → Int) in
    let lift ≔ ((u ↦ infinite_path_evaluate r r (refl (formal_root_infinite_component n) l) u)
      : Product (Fin (suc. n)) Int → Product (Fin (suc. n)) Int) in
    calc
      infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt r (root_pointing n)
        (refl (formal_root_infinite_component n) l))
      = back (lift (infinite_path_evaluate pt r (root_pointing n) int_zero))
        by infinite_conjugate_evaluate pt r (root_pointing n) (refl (formal_root_infinite_component n) l) int_zero
      = back (lift (inr. star., int_zero)) by refl ((u ↦ back (lift u)) : Product (Fin (suc. n)) Int → Int) (root_pointing_zero n)
      = back (inr. star., infinite_cycle_loop_coordinate l)
        by refl back (root_infinite_ap_evaluate n pt pt l (inr. star.) int_zero)
      = int_add (pos. zero.) (int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate l))
        by root_pointing_inverse n (inr. star., infinite_cycle_loop_coordinate l)
      = int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate l)
        by int_add_zero_left (int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate l)) ∎

def conjugate_refl (A : Type) (a : A) (l : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l
  ≔ calc
      pointed_loop_conjugate A a a (refl a) l = concat A a a a l (inverse A a a (refl a))
        by concat_1p A a a (concat A a a a l (inverse A a a (refl a)))
      = concat A a a a l (refl a) by refl (concat A a a a l) (inverse_refl A a)
      = l by concat_p1 A a a l ∎

{` The loop of a composite pointed map is the image of the loop of the
   first map, conjugated by the pointing path of the second. `}
def pointed_conjugate_compose (A B : Type) (a : A) (b : B) (g : B → A) (pg : Id A a (g b))
  (x : B) (p : Id B b x) (l : Id B x x)
  : Id (Id A a a) (pointed_loop_conjugate A a (g x) (concat A a (g b) (g x) pg (refl g p)) (refl g l))
      (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b x p l)))
  ≔ J B b
      (x p ↦ (l : Id B x x) → Id (Id A a a)
        (pointed_loop_conjugate A a (g x) (concat A a (g b) (g x) pg (refl g p)) (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b x p l))))
      (l ↦ concat (Id A a a)
        (pointed_loop_conjugate A a (g b) (concat A a (g b) (g b) pg (refl (g b))) (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g l))
        (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b b (refl b) l)))
        (refl ((q ↦ pointed_loop_conjugate A a (g b) q (refl g l)) : Id A a (g b) → Id A a a) (concat_p1 A a (g b) pg))
        (inverse (Id A a a) (pointed_loop_conjugate A a (g b) pg (refl g (pointed_loop_conjugate B b b (refl b) l)))
          (pointed_loop_conjugate A a (g b) pg (refl g l))
          (refl ((w ↦ pointed_loop_conjugate A a (g b) pg (refl g w)) : Id B b b → Id A a a) (conjugate_refl B b l))))
      x p l

def conjugate_inverse_transport (A : Type) (a x : A) (q : Id A x a) (l : Id A x x)
  : Id (Id A a a) (pointed_loop_conjugate A a x (inverse A x a q) l) (transport A (z ↦ Id A z z) x a q l)
  ≔ concat (Id A a a) (pointed_loop_conjugate A a x (inverse A x a q) l) (loop_conjugate A x a q l)
      (transport A (z ↦ Id A z z) x a q l)
      (refl (concat A a x a (inverse A x a q)) (refl (concat A x x a l) (inverse_inverse A x a q)))
      (inverse (Id A a a) (transport A (z ↦ Id A z z) x a q l) (loop_conjugate A x a q l)
        (loop_transport_conjugate A x a q l))

{` The pointed maps c : S¹ →* InfCyc (predecessor generator) and dg_m. `}
def circle_infinite_pointed_map (C : CircleSignature) : BookPointedMap (circle_pointed C) infinite_pointed
  ≔ pointed_circle_loop_rec C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop

def circle_degree_pointed_map (C : CircleSignature) (m : Nat) : BookPointedMap (circle_pointed C) (circle_pointed C)
  ≔ pointed_circle_loop_rec C (C .carrier) (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m)

def root_after_circle (C : CircleSignature) (n : Nat) : BookPointedMap (circle_pointed C) infinite_pointed
  ≔ book_pointed_compose (circle_pointed C) infinite_pointed infinite_pointed (circle_infinite_pointed_map C)
      (formal_root_infinite_pointed n)

def circle_after_degree (C : CircleSignature) (n : Nat) : BookPointedMap (circle_pointed C) infinite_pointed
  ≔ book_pointed_compose (circle_pointed C) (circle_pointed C) infinite_pointed (circle_degree_pointed_map C (suc. n))
      (circle_infinite_pointed_map C)

def root_after_circle_coordinate (C : CircleSignature) (n : Nat)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (root_after_circle C n))) (neg. n)
  ≔ let pt ≔ infinite_endomorphism_point in
    let cdg ≔ formal_root_infinite_component n in
    let c ≔ circle_infinite_pointed_map C in
    calc
      infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (root_after_circle C n))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (cdg pt) (root_pointing n)
          (refl cdg (pointed_circle_loop_eval C InfiniteCycles pt c)))
        by refl infinite_cycle_loop_coordinate
          (pointed_conjugate_compose InfiniteCycles InfiniteCycles pt pt cdg (root_pointing n)
            (c .fst (C .base)) (c .snd) (refl (c .fst) (C .loop)))
      = int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt c))
        by root_loop_coordinate n (pointed_circle_loop_eval C InfiniteCycles pt c)
      = int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate infinite_predecessor_loop)
        by refl ((l ↦ int_mul (pos. (suc. n)) (infinite_cycle_loop_coordinate l))
            : Id InfiniteCycles pt pt → Int)
          (pointed_circle_loop_rec_beta C InfiniteCycles pt infinite_predecessor_loop)
      = int_mul (pos. (suc. n)) (neg. zero.)
        by refl (int_mul (pos. (suc. n))) infinite_predecessor_loop_coordinate
      = neg. n by refl (neg. n : Int) ∎

def circle_after_degree_coordinate (C : CircleSignature) (n : Nat)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (circle_after_degree C n))) (neg. n)
  ≔ let pt ≔ infinite_endomorphism_point in
    let c ≔ circle_infinite_pointed_map C in
    let d ≔ circle_degree_pointed_map C (suc. n) in
    let lm ≔ loop_power_nat (C .carrier) (C .base) (C .loop) (suc. n) in
    calc
      infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (circle_after_degree C n))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base)) (c .snd)
          (refl (c .fst) (pointed_circle_loop_eval C (C .carrier) (C .base) d)))
        by refl infinite_cycle_loop_coordinate
          (pointed_conjugate_compose InfiniteCycles (C .carrier) pt (C .base) (c .fst) (c .snd)
            (d .fst (C .base)) (d .snd) (refl (d .fst) (C .loop)))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base)) (c .snd)
          (refl (c .fst) lm))
        by refl ((l ↦ infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base))
            (c .snd) (refl (c .fst) l))) : Id (C .carrier) (C .base) (C .base) → Int)
          (pointed_circle_loop_rec_beta C (C .carrier) (C .base) lm)
      = infinite_cycle_loop_coordinate (circle_infinite_cycle_based_action C lm)
        by refl infinite_cycle_loop_coordinate
          (conjugate_inverse_transport InfiniteCycles pt (c .fst (C .base))
            (circle_rec_beta C InfiniteCycles (pt, infinite_predecessor_loop) .fst) (refl (c .fst) lm))
      = int_neg (circle_winding C lm) by circle_infinite_cycle_action_coordinate C lm
      = int_neg (pos. (suc. n)) by refl int_neg (circle_winding_power C (pos. (suc. n)))
      = neg. n by refl (neg. n : Int) ∎

def root_degree_loops_equal (C : CircleSignature) (n : Nat)
  : Id (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (root_after_circle C n))
      (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (circle_after_degree C n))
  ≔ equivalence_injective (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) Int
      infinite_cycle_loop_coordinate_equiv
      (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (root_after_circle C n))
      (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (circle_after_degree C n))
      (concat Int (infinite_cycle_loop_coordinate
          (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (root_after_circle C n)))
        (neg. n)
        (infinite_cycle_loop_coordinate
          (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (circle_after_degree C n)))
        (root_after_circle_coordinate C n)
        (inverse Int (infinite_cycle_loop_coordinate
            (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point (circle_after_degree C n)))
          (neg. n) (circle_after_degree_coordinate C n)))

{` xca:pointed-maps-circle: cdg_m ∘ c = c ∘ dg_m as pointed maps S¹ →* InfCyc,
   with m = suc n. `}
def root_degree_pointed (C : CircleSignature) (n : Nat)
  : Id (BookPointedMap (circle_pointed C) infinite_pointed) (root_after_circle C n) (circle_after_degree C n)
  ≔ equivalence_injective (BookPointedMap (circle_pointed C) infinite_pointed)
      (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (pointed_circle_universal_property C InfiniteCycles infinite_endomorphism_point)
      (root_after_circle C n) (circle_after_degree C n) (root_degree_loops_equal C n)

{` The unpointed identification cdg_m ∘ c = c ∘ dg_m : S¹ → InfCyc. `}
def root_degree_maps (C : CircleSignature) (n : Nat)
  : Id (C .carrier → InfiniteCycles)
      (x ↦ formal_root_infinite_component n (circle_infinite_cycle_map C x))
      (x ↦ circle_infinite_cycle_map C (circle_degree_map C (suc. n) x))
  ≔ refl ((u ↦ u .fst) : BookPointedMap (circle_pointed C) infinite_pointed → (C .carrier → InfiniteCycles))
      (root_degree_pointed C n)
