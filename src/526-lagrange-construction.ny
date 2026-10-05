export "520-orbit-relations"

{` Chapter 5, The Lagrange construction: con:lagrange and
   cor:lagrange-dep-sum. Both are stated for an arbitrary G-set X with a
   point pt and a choice function f : Π_{x : X(sh_G)} Σ_{g : USym G}
   (g · x = pt) (transitivity is not used by the construction), and then
   for a subgroup (X, pt) : Sub(G) with underlying group H, where
   USym H ≡ ((sh_G, pt) = (sh_G, pt)) by definition. `}

{` The premiss of con:lagrange. `}
def LagrangeChoice (G : Group) (X : GSet G) (pt : gset_underlying G X) : Type
  ≔ (x : gset_underlying G X) → Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) pt)

{` "Applying xca:AC-in-TT to this premiss, we obtain a function
   g : X(sh_G) → USym G such that g(x) · x = pt". `}
def lagrange_choice_function_equiv (G : Group) (X : GSet G) (pt : gset_underlying G X)
  : Equiv (LagrangeChoice G X pt)
      (Σ (gset_underlying G X → USym G)
        (g ↦ (x : gset_underlying G X) → Id (gset_underlying G X) (gset_usym_act G X (g x) x) pt))
  ≔ let S ≔ gset_underlying G X in
    quasi_inverse_equiv (LagrangeChoice G X pt)
      (Σ (S → USym G) (g ↦ (x : S) → Id S (gset_usym_act G X (g x) x) pt))
      (f ↦ (x ↦ f x .fst, x ↦ f x .snd)) (h x ↦ (h .fst x, h .snd x))
      (f ↦ refl f) (h ↦ refl h)

{` [g] ≔ g · pt. `}
def lagrange_class (G : Group) (X : GSet G) (pt : gset_underlying G X) (g : USym G) : gset_underlying G X
  ≔ gset_usym_act G X g pt

{` The fiber of [-] at x, Σ_{g} (x = g · pt), is equivalent to
   (sh_G, pt) = (sh_G, x). `}
def lagrange_fiber_path_equiv (G : Group) (X : GSet G) (pt : gset_underlying G X) (x : gset_underlying G X)
  : Equiv (BookFiber (USym G) (gset_underlying G X) (lagrange_class G X pt) x)
      (Id (ActionType G X) (shape G, pt) (shape G, x))
  ≔ let S ≔ gset_underlying G X in
    let T ≔ ActionType G X in
    compose_equiv (BookFiber (USym G) S (lagrange_class G X pt) x) (ActionTypePath G X (shape G, pt) (shape G, x))
      (Id T (shape G, pt) (shape G, x))
      (family_equiv (USym G) (g ↦ Id S x (gset_usym_act G X g pt)) (g ↦ Id S (gset_usym_act G X g pt) x)
        (g ↦ inverse_path_equiv S x (gset_usym_act G X g pt)))
      (canonical_inverse_equiv (Id T (shape G, pt) (shape G, x)) (ActionTypePath G X (shape G, pt) (shape G, x))
        (action_type_path_equiv G X (shape G, pt) (shape G, x)))

{` USym G ≃ Σ_{x : X(sh_G)} ((sh_G, pt) = (sh_G, x)) (lem:sum-of-fibers). `}
def lagrange_sum_equiv (G : Group) (X : GSet G) (pt : gset_underlying G X)
  : Equiv (USym G) (Σ (gset_underlying G X) (x ↦ Id (ActionType G X) (shape G, pt) (shape G, x)))
  ≔ let S ≔ gset_underlying G X in
    let F ≔ (x ↦ BookFiber (USym G) S (lagrange_class G X pt) x) : S → Type in
    compose_equiv (USym G) (Σ S F) (Σ S (x ↦ Id (ActionType G X) (shape G, pt) (shape G, x)))
      (canonical_inverse_equiv (Σ S F) (USym G) (sum_of_fibers_equiv (USym G) S (lagrange_class G X pt)))
      (family_equiv S F (x ↦ Id (ActionType G X) (shape G, pt) (shape G, x)) (lagrange_fiber_path_equiv G X pt))

{` (g(x), !) : (sh_G, x) = (sh_G, pt). `}
def lagrange_choice_path (G : Group) (X : GSet G) (pt : gset_underlying G X) (f : LagrangeChoice G X pt)
  (x : gset_underlying G X) : Id (ActionType G X) (shape G, x) (shape G, pt)
  ≔ action_type_path G X (shape G) (shape G) x pt (f x .fst) (f x .snd)

{` Postconcatenation with a fixed path is an equivalence. `}
def lagrange_concat_right_equiv (A : Type) (a y z : A) (p : Id A y z) : Equiv (Id A a y) (Id A a z)
  ≔ quasi_inverse_equiv (Id A a y) (Id A a z) (t ↦ concat A a y z t p) (t ↦ concat A a z y t (inverse A y z p))
      (t ↦ concat (Id A a y) (concat A a z y (concat A a y z t p) (inverse A y z p))
          (concat A a y y t (concat A y z y p (inverse A y z p))) t
          (concat_assoc A a y z y t p (inverse A y z p))
          (concat (Id A a y) (concat A a y y t (concat A y z y p (inverse A y z p))) (concat A a y y t (refl y)) t
            (refl (concat A a y y t) (concat_inverse_right A y z p)) (concat_p1 A a y t)))
      (t ↦ concat (Id A a z) (concat A a y z (concat A a z y t (inverse A y z p)) p)
          (concat A a z z t (concat A z y z (inverse A y z p) p)) t
          (concat_assoc A a z y z t (inverse A y z p) p)
          (concat (Id A a z) (concat A a z z t (concat A z y z (inverse A y z p) p)) (concat A a z z t (refl z)) t
            (refl (concat A a z z t) (concat_inverse_left A y z p)) (concat_p1 A a z t)))

{` con:lagrange for a pointed G-set: L(f) : USym G ≃ X(sh_G) × ((sh_G, pt) = (sh_G, pt)),
   replacing x by pt by postconcatenation with (g(x), !). `}
def lagrange_equiv (G : Group) (X : GSet G) (pt : gset_underlying G X) (f : LagrangeChoice G X pt)
  : Equiv (USym G) (Product (gset_underlying G X) (Id (ActionType G X) (shape G, pt) (shape G, pt)))
  ≔ let S ≔ gset_underlying G X in
    let T ≔ ActionType G X in
    compose_equiv (USym G) (Σ S (x ↦ Id T (shape G, pt) (shape G, x))) (Product S (Id T (shape G, pt) (shape G, pt)))
      (lagrange_sum_equiv G X pt)
      (family_equiv S (x ↦ Id T (shape G, pt) (shape G, x)) (_ ↦ Id T (shape G, pt) (shape G, pt))
        (x ↦ lagrange_concat_right_equiv T (shape G, pt) (shape G, x) (shape G, pt) (lagrange_choice_path G X pt f x)))

{` The first component of L(f)(g) is [g] = g · pt. `}
def lagrange_equiv_fst (G : Group) (X : GSet G) (pt : gset_underlying G X) (f : LagrangeChoice G X pt) (g : USym G)
  : Id (gset_underlying G X) (lagrange_equiv G X pt f .map g .fst) (gset_usym_act G X g pt)
  ≔ refl (gset_usym_act G X g pt)

{` con:lagrange. For a subgroup (X, pt) with underlying group H, a choice
   f gives L_H(f) : USym G ≃ X(sh_G) × USym H. `}
def lagrange_construction (G : Group) (S : Subgroups G) (f : LagrangeChoice G (S .gset) (S .point))
  : Equiv (USym G) (Product (gset_underlying G (S .gset)) (USym (subgroup_group G S)))
  ≔ lagrange_equiv G (S .gset) (S .point) f

{` cor:lagrange-dep-sum for a pointed G-set: L'(f) : USym G ≃
   Σ_{x : X(sh_G)} ((sh_G, x) = (sh_G, x)), by preconcatenation with
   (g(x), !) (ft:lagrange-dep-sum). `}
def lagrange_dep_sum_equiv (G : Group) (X : GSet G) (pt : gset_underlying G X) (f : LagrangeChoice G X pt)
  : Equiv (USym G) (Σ (gset_underlying G X) (x ↦ Id (ActionType G X) (shape G, x) (shape G, x)))
  ≔ let S ≔ gset_underlying G X in
    let T ≔ ActionType G X in
    compose_equiv (USym G) (Σ S (x ↦ Id T (shape G, pt) (shape G, x))) (Σ S (x ↦ Id T (shape G, x) (shape G, x)))
      (lagrange_sum_equiv G X pt)
      (family_equiv S (x ↦ Id T (shape G, pt) (shape G, x)) (x ↦ Id T (shape G, x) (shape G, x))
        (x ↦ concat_left_equiv T (shape G, x) (shape G, pt) (shape G, x) (lagrange_choice_path G X pt f x)))

def lagrange_dep_sum_construction (G : Group) (S : Subgroups G) (f : LagrangeChoice G (S .gset) (S .point))
  : Equiv (USym G)
      (Σ (gset_underlying G (S .gset)) (x ↦ Id (ActionType G (S .gset)) (shape G, x) (shape G, x)))
  ≔ lagrange_dep_sum_equiv G (S .gset) (S .point) f

{` The same with (sh_G, x) = (sh_G, x) read as USym(G_x) (component_path_equiv). `}
def lagrange_dep_sum_stabilizers (G : Group) (X : GSet G) (pt : gset_underlying G X) (f : LagrangeChoice G X pt)
  : Equiv (USym G) (Σ (gset_underlying G X) (x ↦ USym (stabilizer_group G X x)))
  ≔ let S ≔ gset_underlying G X in
    let T ≔ ActionType G X in
    compose_equiv (USym G) (Σ S (x ↦ Id T (shape G, x) (shape G, x))) (Σ S (x ↦ USym (stabilizer_group G X x)))
      (lagrange_dep_sum_equiv G X pt f)
      (family_equiv S (x ↦ Id T (shape G, x) (shape G, x)) (x ↦ USym (stabilizer_group G X x))
        (x ↦ canonical_inverse_equiv (USym (stabilizer_group G X x)) (Id T (shape G, x) (shape G, x))
          (component_path_equiv T (shape G, x) (component_point T (shape G, x)) (component_point T (shape G, x)))))
