export "1337-loops-of-pointed-maps"
export "418-cyclic-group-images"
export "282-explicit-power-degree"

{` Chapter 13 (fields.tex 638-691), exa:allS1*-swap:
   M ≔ (S¹ →* (S¹ →* BB ℤ)) with ℤ = circle_group C (for an arbitrary
   CircleSignature C, so Bℤ ≡ (S¹, base) judgmentally) and
   BB ℤ = Σ (X : Type) ‖S¹ = X‖₀ (module 1204). `}

{` Homomorphisms of loop spaces preserve powers. `}
def loop_power_nat_hom (A B : Type) (a : A) (b : B) (φ : Id A a a → Id B b b)
  (pu : Id (Id B b b) (φ (refl a)) (refl b))
  (pc : (g h : Id A a a) → Id (Id B b b) (φ (concat A a a a g h)) (concat B b b b (φ g) (φ h)))
  (l : Id A a a) (n : Nat)
  : Id (Id B b b) (φ (loop_power_nat A a l n)) (loop_power_nat B b (φ l) n)
  ≔ match n [
  | zero. ↦ pu
  | suc. n ↦ concat (Id B b b) (φ (concat A a a a (loop_power_nat A a l n) l))
      (concat B b b b (φ (loop_power_nat A a l n)) (φ l)) (concat B b b b (loop_power_nat B b (φ l) n) (φ l))
      (pc (loop_power_nat A a l n) l)
      (refl ((w ↦ concat B b b b w (φ l)) : Id B b b → Id B b b) (loop_power_nat_hom A B a b φ pu pc l n)) ]

def loop_power_hom (A B : Type) (a : A) (b : B) (φ : Id A a a → Id B b b)
  (pu : Id (Id B b b) (φ (refl a)) (refl b))
  (pc : (g h : Id A a a) → Id (Id B b b) (φ (concat A a a a g h)) (concat B b b b (φ g) (φ h)))
  (pi : (g : Id A a a) → Id (Id B b b) (φ (inverse A a a g)) (inverse B b b (φ g)))
  (l : Id A a a) (z : Int)
  : Id (Id B b b) (φ (loop_power A a l z)) (loop_power B b (φ l) z)
  ≔ match z [
  | pos. n ↦ loop_power_nat_hom A B a b φ pu pc l n
  | neg. n ↦ concat (Id B b b) (φ (loop_power_nat A a (inverse A a a l) (suc. n)))
      (loop_power_nat B b (φ (inverse A a a l)) (suc. n)) (loop_power_nat B b (inverse B b b (φ l)) (suc. n))
      (loop_power_nat_hom A B a b φ pu pc (inverse A a a l) (suc. n))
      (refl ((w ↦ loop_power_nat B b w (suc. n)) : Id B b b → Id B b b) (pi l)) ]

def map_path_power (A B : Type) (F : A → B) (a : A) (l : Id A a a) (z : Int)
  : Id (Id B (F a) (F a)) (refl F (loop_power A a l z)) (loop_power B (F a) (refl F l) z)
  ≔ loop_power_hom A B a (F a) (w ↦ refl F w) (refl (refl (F a)))
      (g h ↦ map_path_concat A B F a a a g h) (g ↦ map_path_inverse A B F a a g) l z

{` The example over an arbitrary pointed Y with Ω Y ≃* S¹ (E); the
   instances at Y = BB ℤ are at the end of the module. `}
def example_M (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) : Type
  ≔ BookPointedMap (circle_pointed C) (pointed_maps_pointed (circle_pointed C) Y)

def example_post_ev (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C))
  : Equiv (example_M C Y E) (BookPointedMap (circle_pointed C) (Omega (Y)))
  ≔ ((k ↦ book_pointed_compose (circle_pointed C) (circle_pointed_maps C (Y)) (Omega (Y)) k
        (pointed_circle_ev_pointed C (Y))),
     pointed_postcompose_is_equiv (circle_pointed C) (circle_pointed_maps C (Y)) (Omega (Y))
       (pointed_circle_ev_pointed_equiv C (Y)))

def example_post_e (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C))
  : Equiv (BookPointedMap (circle_pointed C) (Omega (Y))) (BookPointedMap (circle_pointed C) (circle_pointed C))
  ≔ ((k ↦ book_pointed_compose (circle_pointed C) (Omega (Y)) (circle_pointed C) k (E .fst)),
     pointed_postcompose_is_equiv (circle_pointed C) (Omega (Y)) (circle_pointed C) (E))

{` M ≃ ΩΩ(BB ℤ) (using ev twice). `}
def example_M_double_loops (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) : Equiv (example_M C Y E) (Loop (Omega (Y)))
  ≔ compose_equiv (example_M C Y E) (BookPointedMap (circle_pointed C) (Omega (Y))) (Loop (Omega (Y)))
      (example_post_ev C Y E)
      (pointed_circle_universal_property C (Loop (Y)) (refl (Y .point)))

{` M ≃ ℤ. `}
def example_M_integers (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) : Equiv (example_M C Y E) Int
  ≔ let S ≔ circle_pointed C in
    compose_equiv (example_M C Y E) (BookPointedMap S (Omega (Y))) Int (example_post_ev C Y E)
      (compose_equiv (BookPointedMap S (Omega (Y))) (BookPointedMap S S) Int (example_post_e C Y E)
        (compose_equiv (BookPointedMap S S) (Id (C .carrier) (C .base) (C .base)) Int
          (pointed_circle_universal_property C (C .carrier) (C .base))
          (canonical_inverse_equiv Int (Id (C .carrier) (C .base) (C .base))
            (native_equivalence Int (Id (C .carrier) (C .base) (C .base)) (circle_integer_loop_equiv C)))))

{` Ω(S¹ →* BB ℤ) ≃ (S¹ →* S¹), by ptw_* (rem:loops-at-ptd-cst) and Ω(BB ℤ) ≃ S¹. `}
def example_loops_maps_circle (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C))
  : Equiv (Loop (pointed_maps_pointed (circle_pointed C) (Y))) (BookPointedMap (circle_pointed C) (circle_pointed C))
  ≔ compose_equiv (Loop (pointed_maps_pointed (circle_pointed C) (Y)))
      (BookPointedMap (circle_pointed C) (Omega (Y))) (BookPointedMap (circle_pointed C) (circle_pointed C))
      (constant_loops_pointed_equiv (circle_pointed C) (Y)) (example_post_e C Y E)

{` The degree k map dg_k : S¹ →* S¹ (circle recursion with loop ↦ loopᵏ)
   and dg'_k : S¹ →* Ω(BB ℤ). The book builds dg'_k(loop) from function
   extensionality and loopᵏ; here dg'_k is the preimage of dg_k under
   postcomposition with Ω(BB ℤ) ≃* S¹, characterized by E ∘ dg'_k = dg_k. `}
def example_degree_map (C : CircleSignature) (k : Int) : BookPointedMap (circle_pointed C) (circle_pointed C)
  ≔ pointed_circle_ev_inverse C (circle_pointed C) (loop_power (C .carrier) (C .base) (C .loop) k)

def example_degree_loops (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k : Int) : BookPointedMap (circle_pointed C) (Omega (Y))
  ≔ equiv_inverse_map (BookPointedMap (circle_pointed C) (Omega (Y))) (BookPointedMap (circle_pointed C) (circle_pointed C))
      (example_post_e C Y E) (example_degree_map C k)

def example_degree_loops_spec (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k : Int)
  : Id (BookPointedMap (circle_pointed C) (circle_pointed C)) (example_post_e C Y E .map (example_degree_loops C Y E k)) (example_degree_map C k)
  ≔ equiv_counit (BookPointedMap (circle_pointed C) (Omega (Y))) (BookPointedMap (circle_pointed C) (circle_pointed C))
      (example_post_e C Y E) (example_degree_map C k)

{` m_k : M with m_k(base) = cst, m_k(loop) = ptw_*⁻¹(dg'_k); since circle
   recursion computes propositionally, m_k is pointed by the inverse base
   computation rule instead of refl, and m_k(loop) = ptw_*⁻¹(dg'_k) holds
   after conjugation by that pointing, i.e. ev(m_k) = ptw_*⁻¹(dg'_k). `}
def example_m (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k : Int) : example_M C Y E
  ≔ pointed_circle_ev_inverse C (pointed_maps_pointed (circle_pointed C) (Y))
      (equiv_inverse_map (Loop (pointed_maps_pointed (circle_pointed C) (Y)))
        (BookPointedMap (circle_pointed C) (Omega (Y)))
        (constant_loops_pointed_equiv (circle_pointed C) (Y)) (example_degree_loops C Y E k))

def example_m_loop (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k : Int)
  : Id (BookPointedMap (circle_pointed C) (Omega (Y)))
      (constant_loops_pointed_equiv (circle_pointed C) (Y) .map
        (pointed_circle_ev C (pointed_maps_pointed (circle_pointed C) (Y)) (example_m C Y E k)))
      (example_degree_loops C Y E k)
  ≔ let L ≔ Loop (pointed_maps_pointed (circle_pointed C) (Y)) in
    let P ≔ BookPointedMap (circle_pointed C) (Omega (Y)) in
    let e ≔ constant_loops_pointed_equiv (circle_pointed C) (Y) in
    concat P (e .map (pointed_circle_ev C (pointed_maps_pointed (circle_pointed C) (Y)) (example_m C Y E k)))
      (e .map (equiv_inverse_map L P e (example_degree_loops C Y E k))) (example_degree_loops C Y E k)
      (refl (e .map) (pointed_circle_ev_inverse_beta C (pointed_maps_pointed (circle_pointed C) (Y))
        (equiv_inverse_map L P e (example_degree_loops C Y E k))))
      (equiv_counit L P e (example_degree_loops C Y E k))

{` "Applying ptw_*(m_k(loop)) = dg'_k to loopʲ gives the jk-loop": under
   Ω(BB ℤ) ≃ S¹, Ω(E ∘ dg'_k)(loopʲ) = (loopᵏ)ʲ. `}
def example_degree_loops_power (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k j : Int)
  : Id (Loop (circle_pointed C))
      (loops_map (circle_pointed C) (circle_pointed C) (example_post_e C Y E .map (example_degree_loops C Y E k))
        (loop_power (C .carrier) (C .base) (C .loop) j))
      (loop_power (C .carrier) (C .base) (loop_power (C .carrier) (C .base) (C .loop) k) j)
  ≔ let S ≔ circle_pointed C in
    let lj ≔ loop_power (C .carrier) (C .base) (C .loop) j in
    let lk ≔ loop_power (C .carrier) (C .base) (C .loop) k in
    calc
      loops_map S S (example_post_e C Y E .map (example_degree_loops C Y E k)) lj = loops_map S S (example_degree_map C k) lj
        by refl ((f ↦ loops_map S S f lj) : BookPointedMap S S → Loop S) (example_degree_loops_spec C Y E k)
      = loop_power (C .carrier) (C .base) (loops_map S S (example_degree_map C k) (C .loop)) j
        by loops_map_power S S (example_degree_map C k) (C .loop) j
      = loop_power (C .carrier) (C .base) lk j
        by refl ((w ↦ loop_power (C .carrier) (C .base) w j) : Loop S → Loop S)
          (pointed_circle_ev_inverse_beta C S lk) ∎

{` Using that ptw_* is evaluation (rem:loops-at-ptd-cst) and preserves
   composition (con:ptd-homotopy-compo): ptw_*(m_k(loopⁱ)) is the pointwise
   i-th power of dg'_k (m_k(loopⁱ) read as Ω(m_k)(loopⁱ)). `}
def example_m_power (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k i : Int) (x : C .carrier)
  : Id (Loop (Y))
      (constant_loops_pointed_equiv (circle_pointed C) (Y) .map
        (loops_map (circle_pointed C) (pointed_maps_pointed (circle_pointed C) (Y)) (example_m C Y E k)
          (loop_power (C .carrier) (C .base) (C .loop) i)) .fst x)
      (loop_power (Y .carrier) (Y .point) (example_degree_loops C Y E k .fst x) i)
  ≔ let S ≔ circle_pointed C in let P ≔ pointed_maps_pointed S (Y) in
    let Ev ≔ (f ↦ f .fst x) : BookPointedMap S (Y) → Y .carrier in
    let e ≔ constant_loops_pointed_equiv S (Y) in
    let r ≔ pointed_circle_ev C P (example_m C Y E k) in
    calc
      e .map (loops_map S P (example_m C Y E k) (loop_power (C .carrier) (C .base) (C .loop) i)) .fst x
        = refl Ev (loop_power (P .carrier) (P .point) r i)
        by refl ((w ↦ refl Ev w) : Loop P → Loop (Y)) (loops_map_power S P (example_m C Y E k) (C .loop) i)
      = loop_power (Y .carrier) (Y .point) (refl Ev r) i
        by map_path_power (P .carrier) (Y .carrier) Ev (P .point) r i
      = loop_power (Y .carrier) (Y .point) (example_degree_loops C Y E k .fst x) i
        by refl ((w ↦ loop_power (Y .carrier) (Y .point) w i) : Loop (Y) → Loop (Y))
          (refl ((g ↦ g .fst x) : BookPointedMap S (Omega (Y)) → Loop (Y)) (example_m_loop C Y E k)) ∎

{` TBD2, first step: postcomposing swap(m_k) with ev gives dg'_k
   (con:ptw-swap-ptd-doms), i.e. under the equivalence M ≃ (S¹ →* Ω BB ℤ)
   by postcomposition with ev, swap(m_k) corresponds to dg'_k. `}
def example_swap_m (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k : Int)
  : Id (BookPointedMap (circle_pointed C) (Omega (Y)))
      (example_post_ev C Y E .map (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (Y) (example_m C Y E k)))
      (example_degree_loops C Y E k)
  ≔ concat (BookPointedMap (circle_pointed C) (Omega (Y)))
      (example_post_ev C Y E .map (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (Y) (example_m C Y E k)))
      (constant_loops_pointed_equiv (circle_pointed C) (Y) .map
        (pointed_circle_ev C (pointed_maps_pointed (circle_pointed C) (Y)) (example_m C Y E k)))
      (example_degree_loops C Y E k)
      (ptw_swap_pointed_domains C (circle_pointed C) (Y) (example_m C Y E k))
      (example_m_loop C Y E k)

{` Pointwise form of the left composite of fig:ulrik. `}
def ulrik_left_pointwise (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y)) (p : Loop X)
  : Id (Id (Id (Y .carrier) (Y .point) (Y .point)) (refl (Y .point)) (refl (Y .point)))
      (ulrik_left X Y q .fst p)
      (pointed_loop_conjugate (Id (Y .carrier) (Y .point) (Y .point)) (refl (Y .point))
        (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point)) (refl (Y .point)))
        (refl ((φ ↦ φ .fst p) : BookPointedMap (Omega X) (Omega Y) → Loop Y) (loops_functor_point X Y))
        (refl ((f ↦ loops_map X Y f p) : BookPointedMap X Y → Loop Y) q))
  ≔ ulrik_map_conjugate (BookPointedMap (Omega X) (Omega Y)) (Loop Y) (φ ↦ φ .fst p)
      (book_pointed_constant (Omega X) (Omega Y)) (loops_pointed_map X Y (book_pointed_constant X Y))
      (loops_functor_point X Y) (refl (loops_pointed_map X Y) q)

{` The evaluation ev_{BB ℤ} applied along a loop q of S¹ →* BB ℤ is the
   inverse of Ω(ptw_*(q))(loop): fig:ulrik (ulrik_square) at p = loop,
   with the conjugating paths exchanged by Eckmann-Hilton. `}
def example_ev_along (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (q : Loop (pointed_maps_pointed (circle_pointed C) (Y)))
  : Id (Loop (Omega (Y)))
      (loops_map (circle_pointed_maps C (Y)) (Omega (Y)) (pointed_circle_ev_pointed C (Y)) q)
      (inverse (Loop (Y)) (refl (Y .point)) (refl (Y .point))
        (loops_map (circle_pointed C) (Omega (Y))
          (constant_loops_pointed_equiv (circle_pointed C) (Y) .map q) (C .loop)))
  ≔ let S ≔ circle_pointed C in 
    let B ≔ Y .carrier in let y ≔ Y .point in let T ≔ Id B y y in let r ≔ refl y in
    let R0 ≔ pointed_loop_conjugate B y y r r in
    let PΩ ≔ BookPointedMap (Omega S) (Omega Y) in
    let G ≔ (φ ↦ φ .fst (C .loop)) : PΩ → T in
    let ω ≔ refl G (loops_functor_point S Y) in
    let R ≔ (f ↦ loops_map S Y f (C .loop)) : BookPointedMap S Y → T in
    calc
      loops_map (circle_pointed_maps C Y) (Omega Y) (pointed_circle_ev_pointed C Y) q
        = pointed_loop_conjugate T r R0 ω (refl R q)
        by ulrik_conjugate_independent B y R0 (pointed_circle_ev_pointing C Y (C .base) (C .loop)) ω (refl R q)
      = ulrik_left S Y q .fst (C .loop)
        by inverse (Id T r r) (ulrik_left S Y q .fst (C .loop)) (pointed_loop_conjugate T r R0 ω (refl R q))
          (ulrik_left_pointwise S Y q (C .loop))
      = ulrik_right S Y q .fst (C .loop)
        by refl ((F ↦ F .fst (C .loop)) : BookPointedMap (Omega S) (Omega (Omega Y)) → Loop (Omega Y)) (ulrik_square S Y q) ∎

{` TBD2 (open in the book): swap(m_k) = m_j whenever loopʲ = (loopᵏ)⁻¹,
   e.g. j = −k. So swap(m_k) is m_{-k}, not m_k (for k ≠ 0). Proof: both
   sides are compared after the equivalences M ≃ (S¹ →* Ω BB ℤ)
   (postcomposition with ev), (S¹ →* Ω BB ℤ) ≃ (S¹ →* S¹) and ev; swap(m_k)
   goes to loopᵏ by con:ptw-swap-ptd-doms, m_j to (loopʲ)⁻¹ by fig:ulrik
   (path reversal). `}
def example_swap_m_inverse (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k j : Int)
  (hj : Id (Loop (circle_pointed C)) (loop_power (C .carrier) (C .base) (C .loop) j)
          (inverse (C .carrier) (C .base) (C .base) (loop_power (C .carrier) (C .base) (C .loop) k)))
  : Id (example_M C Y E) (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (Y) (example_m C Y E k)) (example_m C Y E j)
  ≔ let S ≔ circle_pointed C in 
    let P ≔ pointed_maps_pointed S Y in
    let MΩ ≔ BookPointedMap S (Omega Y) in let MS ≔ BookPointedMap S S in
    let L ≔ Loop S in
    let lp ≔ (z ↦ loop_power (C .carrier) (C .base) (C .loop) z) : Int → L in
    let e ≔ constant_loops_pointed_equiv S Y in
    let E0 ≔ E .fst in
    let ev ≔ pointed_circle_ev_pointed C Y in
    let mj ≔ example_m C Y E j in
    let qj ≔ equiv_inverse_map (Loop P) MΩ e (example_degree_loops C Y E j) in
    let evS ≔ pointed_circle_universal_property C (C .carrier) (C .base) in
    let x1 ≔ example_post_e C Y E .map (example_post_ev C Y E .map mj) in
    let x2 ≔ example_post_e C Y E .map (example_degree_loops C Y E k) in
    let l1 : Id L (evS .map x1) (lp k)
      ≔ calc
          evS .map x1 = loops_map (Omega Y) S E0 (loops_map (circle_pointed_maps C Y) (Omega Y) ev (loops_map S P mj (C .loop)))
            by concat L (evS .map x1) (loops_map (Omega Y) S E0 (loops_map S (Omega Y) (example_post_ev C Y E .map mj) (C .loop)))
                (loops_map (Omega Y) S E0 (loops_map (circle_pointed_maps C Y) (Omega Y) ev (loops_map S P mj (C .loop))))
              (loops_map_compose_pointwise S (Omega Y) S (example_post_ev C Y E .map mj) E0 (C .loop))
              (refl (loops_map (Omega Y) S E0) (loops_map_compose_pointwise S P (Omega Y) mj ev (C .loop)))
          = loops_map (Omega Y) S E0 (loops_map (circle_pointed_maps C Y) (Omega Y) ev qj)
            by refl ((w ↦ loops_map (Omega Y) S E0 (loops_map (circle_pointed_maps C Y) (Omega Y) ev w)) : Loop P → L)
              (pointed_circle_ev_inverse_beta C P qj)
          = loops_map (Omega Y) S E0 (inverse (Loop Y) (refl (Y .point)) (refl (Y .point)) (loops_map S (Omega Y) (e .map qj) (C .loop)))
            by refl (loops_map (Omega Y) S E0) (example_ev_along C Y E qj)
          = inverse (C .carrier) (C .base) (C .base) (loops_map (Omega Y) S E0 (loops_map S (Omega Y) (e .map qj) (C .loop)))
            by loops_map_inverse (Omega Y) S E0 (loops_map S (Omega Y) (e .map qj) (C .loop))
          = inverse (C .carrier) (C .base) (C .base) (loops_map (Omega Y) S E0 (loops_map S (Omega Y) (example_degree_loops C Y E j) (C .loop)))
            by refl ((g ↦ inverse (C .carrier) (C .base) (C .base) (loops_map (Omega Y) S E0 (loops_map S (Omega Y) g (C .loop)))) : MΩ → L)
              (equiv_counit (Loop P) MΩ e (example_degree_loops C Y E j))
          = inverse (C .carrier) (C .base) (C .base) (loops_map S S (example_post_e C Y E .map (example_degree_loops C Y E j)) (C .loop))
            by refl (inverse (C .carrier) (C .base) (C .base))
              (inverse L (loops_map S S (example_post_e C Y E .map (example_degree_loops C Y E j)) (C .loop))
                (loops_map (Omega Y) S E0 (loops_map S (Omega Y) (example_degree_loops C Y E j) (C .loop)))
                (loops_map_compose_pointwise S (Omega Y) S (example_degree_loops C Y E j) E0 (C .loop)))
          = inverse (C .carrier) (C .base) (C .base) (loops_map S S (example_degree_map C j) (C .loop))
            by refl ((g ↦ inverse (C .carrier) (C .base) (C .base) (loops_map S S g (C .loop))) : MS → L)
              (example_degree_loops_spec C Y E j)
          = inverse (C .carrier) (C .base) (C .base) (lp j)
            by refl (inverse (C .carrier) (C .base) (C .base)) (pointed_circle_ev_inverse_beta C S (lp j))
          = inverse (C .carrier) (C .base) (C .base) (inverse (C .carrier) (C .base) (C .base) (lp k))
            by refl (inverse (C .carrier) (C .base) (C .base)) hj
          = lp k by inverse_inverse (C .carrier) (C .base) (C .base) (lp k) ∎ in
    let l2 : Id L (evS .map x2) (lp k)
      ≔ concat L (evS .map x2) (evS .map (example_degree_map C k)) (lp k)
          (refl (evS .map) (example_degree_loops_spec C Y E k)) (pointed_circle_ev_inverse_beta C S (lp k)) in
    let s1 : Id MΩ (example_post_ev C Y E .map mj) (example_degree_loops C Y E k)
      ≔ equivalence_injective MΩ MS (example_post_e C Y E) (example_post_ev C Y E .map mj) (example_degree_loops C Y E k)
          (equivalence_injective MS L evS x1 x2 (concat L (evS .map x1) (lp k) (evS .map x2) l1 (inverse L (evS .map x2) (lp k) l2))) in
    equivalence_injective (example_M C Y E) MΩ (example_post_ev C Y E)
      (swap_pointed_domains_map S S Y (example_m C Y E k)) mj
      (concat MΩ (example_post_ev C Y E .map (swap_pointed_domains_map S S Y (example_m C Y E k))) (example_degree_loops C Y E k)
        (example_post_ev C Y E .map mj) (example_swap_m C Y E k) (inverse MΩ (example_post_ev C Y E .map mj) (example_degree_loops C Y E k) s1))

{` Instances at the example's BB ℤ (ℤ = circle_group C): Ω(BB ℤ) ≃* Bℤ ≡ S¹
   (ℤ is abelian; thm:abelian-groups-weq-sc2types). `}
def example_bbz (C : CircleSignature) : Pointed ≔ BB (circle_group C)

def example_bbz_loops (C : CircleSignature) : BookPointedEquiv (Omega (example_bbz C)) (circle_pointed C)
  ≔ abelian_bb_loops_pointed_equiv (circle_group C) (circle_group_abelian C)

def example_M_bbz_integers (C : CircleSignature) : Equiv (example_M C (example_bbz C) (example_bbz_loops C)) Int
  ≔ example_M_integers C (example_bbz C) (example_bbz_loops C)

def example_M_bbz_double_loops (C : CircleSignature)
  : Equiv (example_M C (example_bbz C) (example_bbz_loops C)) (Loop (Omega (example_bbz C)))
  ≔ example_M_double_loops C (example_bbz C) (example_bbz_loops C)

def example_swap_m_bbz (C : CircleSignature) (k j : Int)
  (hj : Id (Loop (circle_pointed C)) (loop_power (C .carrier) (C .base) (C .loop) j)
          (inverse (C .carrier) (C .base) (C .base) (loop_power (C .carrier) (C .base) (C .loop) k)))
  : Id (example_M C (example_bbz C) (example_bbz_loops C))
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (example_m C (example_bbz C) (example_bbz_loops C) k))
      (example_m C (example_bbz C) (example_bbz_loops C) j)
  ≔ example_swap_m_inverse C (example_bbz C) (example_bbz_loops C) k j hj

{` loop^{-k} = (loopᵏ)⁻¹ (for any loop). `}
def loop_power_negate (A : Type) (a : A) (l : Id A a a) (z : Int)
  : Id (Id A a a) (loop_power A a l (int_neg z)) (inverse A a a (loop_power A a l z))
  ≔ match z [
  | pos. zero. ↦ inverse (Id A a a) (inverse A a a (refl a)) (refl a) (inverse_refl A a)
  | pos. (suc. n) ↦ inverse (Id A a a) (inverse A a a (loop_power_nat A a l (suc. n))) (loop_power_nat A a (inverse A a a l) (suc. n))
      (loop_power_nat_inverse A a l (suc. n))
  | neg. n ↦ calc
      loop_power_nat A a l (suc. n) = loop_power_nat A a (inverse A a a (inverse A a a l)) (suc. n)
        by refl ((w ↦ loop_power_nat A a w (suc. n)) : Id A a a → Id A a a)
          (inverse (Id A a a) (inverse A a a (inverse A a a l)) l (inverse_inverse A a a l))
      = inverse A a a (loop_power_nat A a (inverse A a a l) (suc. n))
        by inverse (Id A a a) (inverse A a a (loop_power_nat A a (inverse A a a l) (suc. n)))
          (loop_power_nat A a (inverse A a a (inverse A a a l)) (suc. n)) (loop_power_nat_inverse A a (inverse A a a l) (suc. n)) ∎ ]

{` TBD2 answered: swap(m_k) = m_{-k} (at BB ℤ). `}
def example_swap_m_negative (C : CircleSignature) (k : Int)
  : Id (example_M C (example_bbz C) (example_bbz_loops C))
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (example_m C (example_bbz C) (example_bbz_loops C) k))
      (example_m C (example_bbz C) (example_bbz_loops C) (int_neg k))
  ≔ example_swap_m_bbz C k (int_neg k) (loop_power_negate (C .carrier) (C .base) (C .loop) k)
