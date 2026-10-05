export "528-burnside-finiteness"

{` Chapter 5, proof of lem:burnside: the chain of equivalences

     Σ_{g : USym G} X^g ≡ Σ_g Σ_{x : X(sh_G)} (g · x = x)
       ≃ Σ_x Σ_g (g · x = x)
       ≃ Σ_x USym G_x
       ≃ Σ_{O : X/G} Σ_x ((O = [x]) × USym G_x)
       ≃ Σ_{O : X/G} Σ_{x : X_O(sh_G)} USym G_x

   (no finiteness is needed for it), and the per-orbit application of
   cor:lagrange-dep-sum: for a point x_O : X_O(sh_G) and a choice function
   f_O : Π_{y : X_O(sh_G)} Σ_g (g · y = x_O), USym G ≃ Σ_{y : X_O(sh_G)} USym G_y.
   USym G_x ≃ Σ_g (g · x = x) is stabilizer_usym_equiv (module 523).
   In the last two types G_x is the stabilizer of the underlying point x in
   X, as in the book (for y : X_O(sh_G) it is G_{y.1}). `}

{` Σ_g Σ_x (g · x = x) ≃ Σ_x Σ_g (g · x = x) (rearranging sums). `}
def burnside_swap_equiv (G : Group) (X : GSet G)
  : Equiv (BurnsideSum G X)
      (Σ (gset_underlying G X) (x ↦ Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)))
  ≔ let Xs ≔ gset_underlying G X in
    let F ≔ (x ↦ Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g x) x)) : Xs → Type in
    quasi_inverse_equiv (BurnsideSum G X) (Σ Xs F)
      (t ↦ (t .snd .fst, (t .fst, t .snd .snd))) (t ↦ (t .snd .fst, (t .fst, t .snd .snd)))
      (t ↦ refl t) (t ↦ refl t)

{` Σ_x Σ_g (g · x = x) ≃ Σ_x USym G_x. `}
def burnside_stabilizer_sum_equiv (G : Group) (X : GSet G)
  : Equiv (Σ (gset_underlying G X) (x ↦ Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)))
      (Σ (gset_underlying G X) (x ↦ USym (stabilizer_group G X x)))
  ≔ let Xs ≔ gset_underlying G X in
    family_equiv Xs (x ↦ Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g x) x)) (x ↦ USym (stabilizer_group G X x))
      (x ↦ canonical_inverse_equiv (USym (stabilizer_group G X x)) (Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g x) x))
        (stabilizer_usym_equiv G X x))

{` Writing A as the sum of the fibers of f : A → B, for any family P over A:
   Σ_a P(a) ≃ Σ_{b : B} Σ_a ((b = f a) × P(a)) (lem:sum-of-fibers). `}
def burnside_fiber_regroup_equiv (A B : Type) (f : A → B) (P : A → Type)
  : Equiv (Σ A P) (Σ B (b ↦ Σ A (a ↦ Product (Id B b (f a)) (P a))))
  ≔ let W ≔ Σ B (b ↦ BookFiber A B f b) in
    let e ≔ sum_of_fibers_equiv A B f in
    compose_equiv (Σ A P) (Σ W (w ↦ P (e .map w))) (Σ B (b ↦ Σ A (a ↦ Product (Id B b (f a)) (P a))))
      (canonical_inverse_equiv (Σ W (w ↦ P (e .map w))) (Σ A P) (sigma_pullback_equiv W A e P))
      (quasi_inverse_equiv (Σ W (w ↦ P (e .map w))) (Σ B (b ↦ Σ A (a ↦ Product (Id B b (f a)) (P a))))
        (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd, t .snd))))
        (t ↦ ((t .fst, (t .snd .fst, t .snd .snd .fst)), t .snd .snd .snd))
        (t ↦ refl t) (t ↦ refl t))

{` The last type of the chain: Σ_{O : X/G} Σ_{x : X_O(sh_G)} USym G_x. `}
def BurnsideOrbitSum (G : Group) (X : GSet G) : Type
  ≔ Σ (Orbits G X) (O ↦ Σ (gset_underlying G (gsubset_gset G X (O .fst))) (y ↦ USym (stabilizer_group G X (y .fst))))

{` Σ_x ((O = [x]) × USym G_x) ≃ Σ_{x : X_O(sh_G)} USym G_x, since O = [x]
   is equivalent to O(sh_G, x) (definition of X_O). `}
def burnside_orbit_member_equiv (G : Group) (X : GSet G) (O : Orbits G X)
  : Equiv (Σ (gset_underlying G X) (x ↦ Product (Id (Orbits G X) O (orbit_of_point G X x)) (USym (stabilizer_group G X x))))
      (Σ (gset_underlying G (gsubset_gset G X (O .fst))) (y ↦ USym (stabilizer_group G X (y .fst))))
  ≔ let Xs ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    let M ≔ (x ↦ OrbitMember G X O (shape G, x)) : Xs → Type in
    let S ≔ (x ↦ USym (stabilizer_group G X x)) : Xs → Type in
    compose_equiv (Σ Xs (x ↦ Product (Id Or O (orbit_of_point G X x)) (S x))) (Σ Xs (x ↦ Product (M x) (S x)))
      (Σ (Σ Xs M) (y ↦ S (y .fst)))
      (family_equiv Xs (x ↦ Product (Id Or O (orbit_of_point G X x)) (S x)) (x ↦ Product (M x) (S x))
        (x ↦ product_equiv (Id Or O (orbit_of_point G X x)) (S x) (M x) (S x)
          (canonical_inverse_equiv (M x) (Id Or O (orbit_of_point G X x)) (orbit_member_path_equiv G X O (shape G, x)))
          (identity_equiv (S x))))
      (quasi_inverse_equiv (Σ Xs (x ↦ Product (M x) (S x))) (Σ (Σ Xs M) (y ↦ S (y .fst)))
        (t ↦ ((t .fst, t .snd .fst), t .snd .snd)) (t ↦ (t .fst .fst, (t .fst .snd, t .snd)))
        (t ↦ refl t) (t ↦ refl t))

{` The whole chain: Σ_{g : USym G} X^g ≃ Σ_{O : X/G} Σ_{x : X_O(sh_G)} USym G_x. `}
def burnside_chain_equiv (G : Group) (X : GSet G) : Equiv (BurnsideSum G X) (BurnsideOrbitSum G X)
  ≔ let Xs ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    let S ≔ (x ↦ USym (stabilizer_group G X x)) : Xs → Type in
    let F ≔ (x ↦ Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g x) x)) : Xs → Type in
    let R ≔ (O ↦ Σ Xs (x ↦ Product (Id Or O (orbit_of_point G X x)) (S x))) : Or → Type in
    compose_equiv (BurnsideSum G X) (Σ Xs F) (BurnsideOrbitSum G X)
      (burnside_swap_equiv G X)
      (compose_equiv (Σ Xs F) (Σ Xs S) (BurnsideOrbitSum G X)
        (burnside_stabilizer_sum_equiv G X)
        (compose_equiv (Σ Xs S) (Σ Or R) (BurnsideOrbitSum G X)
          (burnside_fiber_regroup_equiv Xs Or (orbit_of_point G X) S)
          (family_equiv Or R
            (O ↦ Σ (gset_underlying G (gsubset_gset G X (O .fst))) (y ↦ S (y .fst)))
            (O ↦ burnside_orbit_member_equiv G X O))))

{` For y : X_O(sh_G), the stabilizers of y in X_O and of y.1 in X have
   equivalent symmetry sets: g ·_{X_O} y has first component g · y.1 (by
   definition) and the second component is a proposition. `}
def burnside_orbit_stabilizer_bridge (G : Group) (X : GSet G) (O : Orbits G X)
  (y : gset_underlying G (gsubset_gset G X (O .fst)))
  : Equiv (USym (stabilizer_group G (gsubset_gset G X (O .fst)) y)) (USym (stabilizer_group G X (y .fst)))
  ≔ let Y ≔ gsubset_gset G X (O .fst) in
    let Xs ≔ gset_underlying G X in
    let Ys ≔ gset_underlying G Y in
    let M ≔ (x ↦ OrbitMember G X O (shape G, x)) : Xs → Type in
    compose_equiv (USym (stabilizer_group G Y y)) (Σ (USym G) (g ↦ Id Ys (gset_usym_act G Y g y) y))
      (USym (stabilizer_group G X (y .fst)))
      (stabilizer_usym_equiv G Y y)
      (compose_equiv (Σ (USym G) (g ↦ Id Ys (gset_usym_act G Y g y) y))
        (Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g (y .fst)) (y .fst)))
        (USym (stabilizer_group G X (y .fst)))
        (family_equiv (USym G) (g ↦ Id Ys (gset_usym_act G Y g y) y)
          (g ↦ Id Xs (gset_usym_act G X g (y .fst)) (y .fst))
          (g ↦ subtype_path_equiv Xs M (x ↦ orbit_member_prop G X O (shape G, x)) (gset_usym_act G Y g y) y))
        (canonical_inverse_equiv (USym (stabilizer_group G X (y .fst)))
          (Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g (y .fst)) (y .fst)))
          (stabilizer_usym_equiv G X (y .fst))))

{` The data the book uses for an orbit O: a point x_O : X_O(sh_G) and
   f_O : Π_{y : X_O(sh_G)} Σ_g (g ·_{X_O} y = x_O) (con:lagrange). `}
def BurnsideOrbitChoice (G : Group) (X : GSet G) (O : Orbits G X) : Type
  ≔ Σ (gset_underlying G (gsubset_gset G X (O .fst))) (xO ↦ LagrangeChoice G (gsubset_gset G X (O .fst)) xO)

{` cor:lagrange-dep-sum applied to (X_O, x_O, f_O):
   USym G ≃ Σ_{y : X_O(sh_G)} USym G_y. `}
def burnside_orbit_lagrange_equiv (G : Group) (X : GSet G) (O : Orbits G X) (c : BurnsideOrbitChoice G X O)
  : Equiv (USym G) (Σ (gset_underlying G (gsubset_gset G X (O .fst))) (y ↦ USym (stabilizer_group G X (y .fst))))
  ≔ let Y ≔ gsubset_gset G X (O .fst) in
    let Ys ≔ gset_underlying G Y in
    compose_equiv (USym G) (Σ Ys (y ↦ USym (stabilizer_group G Y y)))
      (Σ Ys (y ↦ USym (stabilizer_group G X (y .fst))))
      (lagrange_dep_sum_stabilizers G Y (c .fst) (c .snd))
      (family_equiv Ys (y ↦ USym (stabilizer_group G Y y)) (y ↦ USym (stabilizer_group G X (y .fst)))
        (y ↦ burnside_orbit_stabilizer_bridge G X O y))
