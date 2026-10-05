export "1338-integer-double-loops-example"
export "1310-integer-ring"

{` Chapter 13 (fields.tex:679, exa:allS1*-swap): "applying ptw_*(m_k(loopⁱ)) to loopʲ gives the
   ijk-loop around id_S¹". Applying a pointed map F : S¹ →* Ω Y to a loop p is Ω(F)(p) (def:loops-map).
   For any pointed X, Y and p : Ω X, the map q ↦ Ω(ptw_*(q))(p) : Ω(X →* Y) → Ω²Y preserves powers
   (loops_eval_along_power): by fig:ulrik (ulrik_square) it is q ↦ (ap_{φ ↦ φ(p)}(Ω(Ω)(q)))⁻¹, a composite
   of group homomorphisms followed by inversion, which preserves powers in Ω²Y (Eckmann-Hilton). Hence
   Ω(ptw_*(m_k(loopⁱ)))(loopʲ) = (Ω(dg'_k)(loopʲ))ⁱ (example_m_power_along), and under Ω E for
   E : Ω Y ≃* S¹ this is ((loopᵏ)ʲ)ⁱ = loop^{(i·j)·k} (example_m_power_along_circle), the ijk-loop. `}

{` Inversion preserves powers in Ω²Y. `}
def double_loop_inverse_power (B : Type) (y : B) (l : Id (Id B y y) (refl y) (refl y)) (z : Int)
  : Id (Id (Id B y y) (refl y) (refl y))
      (inverse (Id B y y) (refl y) (refl y) (loop_power (Id B y y) (refl y) l z))
      (loop_power (Id B y y) (refl y) (inverse (Id B y y) (refl y) (refl y) l) z)
  ≔ let T ≔ Id B y y in let r ≔ refl y in let L ≔ Id T r r in
    loop_power_hom T T r r (w ↦ inverse T r r w) (inverse_refl T r)
      (g h ↦ concat L (inverse T r r (concat T r r r g h)) (concat T r r r (inverse T r r h) (inverse T r r g))
               (concat T r r r (inverse T r r g) (inverse T r r h))
               (inverse_concat T r r r g h)
               (eckmann_hilton B y (inverse T r r h) (inverse T r r g)))
      (g ↦ refl (inverse T r r (inverse T r r g)))
      l z

{` Evaluation of ptw_*(q) along p : Ω X. `}
def loops_eval_along (X Y : Pointed) (p : Loop X) (q : Loop (pointed_maps_pointed X Y)) : Loop (Omega Y)
  ≔ loops_map X (Omega Y) (constant_loops_pointed_equiv X Y .map q) p

{` By fig:ulrik: Ω(ptw_*(q))(p) = (ap_{φ ↦ φ(p)}(Ω(Ω)(q)))⁻¹. `}
def loops_eval_along_ulrik (X Y : Pointed) (p : Loop X) (q : Loop (pointed_maps_pointed X Y))
  : Id (Loop (Omega Y)) (loops_eval_along X Y p q)
      (inverse (Loop Y) (refl (Y .point)) (refl (Y .point))
        (refl ((φ ↦ φ .fst p) : BookPointedMap (Omega X) (Omega Y) → Loop Y) (loops_of_loops_functor X Y q)))
  ≔ let r ≔ refl (Y .point) in let L ≔ Id (Loop Y) r r in
    let Φq ≔ loops_eval_along X Y p q in
    let ψq ≔ refl ((φ ↦ φ .fst p) : BookPointedMap (Omega X) (Omega Y) → Loop Y) (loops_of_loops_functor X Y q) in
    let v : Id L ψq (inverse (Loop Y) r r Φq)
      ≔ refl ((k ↦ k .fst p) : BookPointedMap (Omega X) (Omega (Omega Y)) → L) (ulrik_square X Y q) in
    concat L Φq (inverse (Loop Y) r r (inverse (Loop Y) r r Φq)) (inverse (Loop Y) r r ψq)
      (inverse L (inverse (Loop Y) r r (inverse (Loop Y) r r Φq)) Φq (inverse_inverse (Loop Y) r r Φq))
      (refl ((w ↦ inverse (Loop Y) r r w) : L → L) (inverse L ψq (inverse (Loop Y) r r Φq) v))

{` q ↦ Ω(ptw_*(q))(p) preserves powers. `}
def loops_eval_along_power (X Y : Pointed) (p : Loop X) (q : Loop (pointed_maps_pointed X Y)) (i : Int)
  : Id (Loop (Omega Y))
      (loops_eval_along X Y p (loop_power (BookPointedMap X Y) (book_pointed_constant X Y) q i))
      (loop_power (Loop Y) (refl (Y .point)) (loops_eval_along X Y p q) i)
  ≔ let r ≔ refl (Y .point) in let L ≔ Id (Loop Y) r r in
    let P ≔ pointed_maps_pointed X Y in let P' ≔ pointed_maps_pointed (Omega X) (Omega Y) in
    let ev ≔ (φ ↦ φ .fst p) : BookPointedMap (Omega X) (Omega Y) → Loop Y in
    let qi ≔ loop_power (BookPointedMap X Y) (book_pointed_constant X Y) q i in
    let lq ≔ loops_of_loops_functor X Y q in
    let ψ ≔ (w ↦ refl ev w) : Loop P' → L in
    let ψ_power : Id L (ψ (loops_of_loops_functor X Y qi)) (loop_power (Loop Y) r (ψ lq) i)
      ≔ concat L (ψ (loops_of_loops_functor X Y qi)) (ψ (loop_power (P' .carrier) (P' .point) lq i))
          (loop_power (Loop Y) r (ψ lq) i)
          (refl ψ (loops_map_power P P' (loops_functor_pointed X Y) q i))
          (map_path_power (P' .carrier) (Loop Y) ev (P' .point) lq i) in
    calc
      loops_eval_along X Y p qi
        = inverse (Loop Y) r r (ψ (loops_of_loops_functor X Y qi)) by loops_eval_along_ulrik X Y p qi
      = inverse (Loop Y) r r (loop_power (Loop Y) r (ψ lq) i)
        by refl ((w ↦ inverse (Loop Y) r r w) : L → L) ψ_power
      = loop_power (Loop Y) r (inverse (Loop Y) r r (ψ lq)) i by double_loop_inverse_power (Y .carrier) (Y .point) (ψ lq) i
      = loop_power (Loop Y) r (loops_eval_along X Y p q) i
        by refl ((w ↦ loop_power (Loop Y) r w i) : L → L)
          (inverse L (loops_eval_along X Y p q) (inverse (Loop Y) r r (ψ lq)) (loops_eval_along_ulrik X Y p q)) ∎

{` fields.tex:679: Ω(ptw_*(m_k(loopⁱ)))(loopʲ) = (Ω(dg'_k)(loopʲ))ⁱ. `}
def example_m_power_along (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k i j : Int)
  : Id (Loop (Omega Y))
      (loops_eval_along (circle_pointed C) Y (loop_power (C .carrier) (C .base) (C .loop) j)
        (loops_map (circle_pointed C) (pointed_maps_pointed (circle_pointed C) Y) (example_m C Y E k)
          (loop_power (C .carrier) (C .base) (C .loop) i)))
      (loop_power (Loop Y) (refl (Y .point))
        (loops_map (circle_pointed C) (Omega Y) (example_degree_loops C Y E k) (loop_power (C .carrier) (C .base) (C .loop) j)) i)
  ≔ let S ≔ circle_pointed C in let P ≔ pointed_maps_pointed S Y in
    let r ≔ refl (Y .point) in let L ≔ Id (Loop Y) r r in
    let lj ≔ loop_power (C .carrier) (C .base) (C .loop) j in
    let Φ ≔ loops_eval_along S Y lj in
    let mk ≔ example_m C Y E k in
    calc
      Φ (loops_map S P mk (loop_power (C .carrier) (C .base) (C .loop) i))
        = Φ (loop_power (P .carrier) (P .point) (loops_map S P mk (C .loop)) i)
        by refl Φ (loops_map_power S P mk (C .loop) i)
      = loop_power (Loop Y) r (Φ (loops_map S P mk (C .loop))) i by loops_eval_along_power S Y lj (loops_map S P mk (C .loop)) i
      = loop_power (Loop Y) r (loops_map S (Omega Y) (example_degree_loops C Y E k) lj) i
        by refl ((F ↦ loop_power (Loop Y) r (loops_map S (Omega Y) F lj) i) : BookPointedMap S (Omega Y) → L)
          (example_m_loop C Y E k) ∎

{` Powers of powers of loop in S¹. `}
def circle_loop_power_power (C : CircleSignature) (a b : Int)
  : Id (Loop (circle_pointed C))
      (loop_power (C .carrier) (C .base) (loop_power (C .carrier) (C .base) (C .loop) a) b)
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul a b))
  ≔ let pw ≔ (n : Int) ↦ loop_power (C .carrier) (C .base) (C .loop) n in
    let x ≔ loop_power (C .carrier) (C .base) (pw a) b in
    concat (Loop (circle_pointed C)) x (pw (circle_winding C x)) (pw (int_mul a b))
      (inverse (Loop (circle_pointed C)) (pw (circle_winding C x)) x (circle_power_winding C x))
      (refl pw (concat Int (circle_winding C x) (int_mul (circle_winding C (pw a)) b) (int_mul a b)
        (circle_winding_power_arbitrary C (pw a) b)
        (refl ((n ↦ int_mul n b) : Int → Int) (circle_winding_power C a))))

def int_mul_kji_ijk (i j k : Int) : Id Int (int_mul (int_mul k j) i) (int_mul (int_mul i j) k)
  ≔ calc
      int_mul (int_mul k j) i = int_mul i (int_mul k j) by int_mul_comm (int_mul k j) i
      = int_mul i (int_mul j k) by refl (int_mul i) (int_mul_comm k j)
      = int_mul (int_mul i j) k by int_mul_assoc i j k ∎

{` Under E : Ω Y ≃* S¹ the value is the ijk-loop: Ω E(Ω(ptw_*(m_k(loopⁱ)))(loopʲ)) = loop^{(i·j)·k}. `}
def example_m_power_along_circle (C : CircleSignature) (Y : Pointed) (E : BookPointedEquiv (Omega Y) (circle_pointed C)) (k i j : Int)
  : Id (Loop (circle_pointed C))
      (loops_map (Omega Y) (circle_pointed C) (E .fst)
        (loops_eval_along (circle_pointed C) Y (loop_power (C .carrier) (C .base) (C .loop) j)
          (loops_map (circle_pointed C) (pointed_maps_pointed (circle_pointed C) Y) (example_m C Y E k)
            (loop_power (C .carrier) (C .base) (C .loop) i))))
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul i j) k))
  ≔ let S ≔ circle_pointed C in
    let pw ≔ (n : Int) ↦ loop_power (C .carrier) (C .base) (C .loop) n in
    let lj ≔ pw j in
    let dg ≔ example_degree_loops C Y E k in
    let ΩE ≔ loops_map (Omega Y) S (E .fst) in
    calc
      ΩE (loops_eval_along S Y lj (loops_map S (pointed_maps_pointed S Y) (example_m C Y E k) (pw i)))
        = ΩE (loop_power (Loop Y) (refl (Y .point)) (loops_map S (Omega Y) dg lj) i)
        by refl ΩE (example_m_power_along C Y E k i j)
      = loop_power (C .carrier) (C .base) (ΩE (loops_map S (Omega Y) dg lj)) i
        by loops_map_power (Omega Y) S (E .fst) (loops_map S (Omega Y) dg lj) i
      = loop_power (C .carrier) (C .base) (loops_map S S (example_post_e C Y E .map dg) lj) i
        by refl ((w ↦ loop_power (C .carrier) (C .base) w i) : Loop S → Loop S)
          (inverse (Loop S) (loops_map S S (example_post_e C Y E .map dg) lj) (ΩE (loops_map S (Omega Y) dg lj))
            (loops_map_compose_pointwise S (Omega Y) S dg (E .fst) lj))
      = loop_power (C .carrier) (C .base) (loop_power (C .carrier) (C .base) (pw k) j) i
        by refl ((w ↦ loop_power (C .carrier) (C .base) w i) : Loop S → Loop S) (example_degree_loops_power C Y E k j)
      = loop_power (C .carrier) (C .base) (pw (int_mul k j)) i
        by refl ((w ↦ loop_power (C .carrier) (C .base) w i) : Loop S → Loop S) (circle_loop_power_power C k j)
      = pw (int_mul (int_mul k j) i) by circle_loop_power_power C (int_mul k j) i
      = pw (int_mul (int_mul i j) k) by refl pw (int_mul_kji_ijk i j k) ∎

{` The instance at Y = BB ℤ. `}
def example_m_power_along_bbz (C : CircleSignature) (k i j : Int)
  : Id (Loop (circle_pointed C))
      (loops_map (Omega (example_bbz C)) (circle_pointed C) (example_bbz_loops C .fst)
        (loops_eval_along (circle_pointed C) (example_bbz C) (loop_power (C .carrier) (C .base) (C .loop) j)
          (loops_map (circle_pointed C) (pointed_maps_pointed (circle_pointed C) (example_bbz C))
            (example_m C (example_bbz C) (example_bbz_loops C) k) (loop_power (C .carrier) (C .base) (C .loop) i))))
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul i j) k))
  ≔ example_m_power_along_circle C (example_bbz C) (example_bbz_loops C) k i j
