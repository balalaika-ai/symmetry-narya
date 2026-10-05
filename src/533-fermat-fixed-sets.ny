export "532-fermat-gset"
import "508-stabilizer-subgroups"

{` Chapter 5, proof of Fermat's Little Theorem, the fixed sets: for p = m+1
   prime, X^g is all of X(sh) for g = refl, and exactly the n constant
   functions for each of the other p − 1 symmetries g. As in the book:
   apply xca:lagrange (lagrange_cardinality) to the subgroup given by the
   orbit of f with the point f, whose underlying group is the stabilizer
   (C_p)_f (rem:subgrp-is-stabsubgr); since p = Card(C_p) is prime, either
   the orbit has one element (then every symmetry fixes f and f is
   constant) or the stabilizer has one element (then no g ≠ refl fixes f). `}

{` The subgroup (X_[f], f) of C_p (orbit_subgroup of module 508). `}
def fermat_orbit_subgroup (m n : Nat) (f : Fin (suc. m) → Fin n) : Subgroups (fermat_group m)
  ≔ orbit_subgroup (fermat_group m) (fermat_gset m n) f

def fermat_orbit_finite (m n : Nat) (f : Fin (suc. m) → Fin n)
  : IsFiniteGSet (fermat_group m) (fermat_orbit_subgroup m n f .gset)
  ≔ burnside_orbit_underlying_finite (fermat_group m) (fermat_group_finite m) (fermat_gset m n) (fermat_gset_finite m n)
      (orbit_of_point (fermat_group m) (fermat_gset m n) f)

{` xca:lagrange for (X_[f], f): p = Card(X_[f]) × Card((C_p)_f). `}
def fermat_lagrange (m n : Nat) (f : Fin (suc. m) → Fin n)
  : Id Nat (suc. m)
      (mul (gset_card (fermat_group m) (fermat_orbit_subgroup m n f .gset) (fermat_orbit_finite m n f))
        (group_card (subgroup_group (fermat_group m) (fermat_orbit_subgroup m n f))
          (lagrange_subgroup_finite (fermat_group m) (fermat_orbit_subgroup m n f) (fermat_group_finite m)
            (fermat_orbit_finite m n f))))
  ≔ let G ≔ fermat_group m in
    let S ≔ fermat_orbit_subgroup m n f in
    let hS ≔ fermat_orbit_finite m n f in
    concat Nat (suc. m) (group_card G (fermat_group_finite m))
      (mul (gset_card G (S .gset) hS) (group_card (subgroup_group G S) (lagrange_subgroup_finite G S (fermat_group_finite m) hS)))
      (inverse Nat (group_card G (fermat_group_finite m)) (suc. m) (fermat_group_card m))
      (lagrange_cardinality G S (fermat_group_finite m) (fermat_orbit_finite m n f))

{` If the orbit of f has one element, every symmetry fixes f. `}
def fermat_orbit_one_fixed (m n : Nat) (f : Fin (suc. m) → Fin n)
  (a1 : Id Nat (gset_card (fermat_group m) (fermat_orbit_subgroup m n f .gset) (fermat_orbit_finite m n f)) (suc. zero.))
  (h : USym (fermat_group m))
  : Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) h f) f
  ≔ let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let S ≔ fermat_orbit_subgroup m n f in
    let Ys ≔ gset_underlying G (S .gset) in
    let hf ≔ gset_usym_act G X h f in
    let hprop : isProp Ys ≔ fermat_cardinality_one_prop Ys (fermat_orbit_finite m n f) a1 in
    let y : Ys ≔ (hf, mere (Id (ActionType G X) (shape G, f) (shape G, hf))
                     (action_type_path G X (shape G) (shape G) f hf h (refl hf))) in
    hprop y (S .point) .fst

{` If the stabilizer of f has one element, only refl fixes f. `}
def fermat_stabilizer_one_unit (m n : Nat) (f : Fin (suc. m) → Fin n)
  (b1 : Id Nat (group_card (subgroup_group (fermat_group m) (fermat_orbit_subgroup m n f))
          (lagrange_subgroup_finite (fermat_group m) (fermat_orbit_subgroup m n f) (fermat_group_finite m)
            (fermat_orbit_finite m n f))) (suc. zero.))
  (g : USym (fermat_group m))
  (fix : Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f)
  : Id (USym (fermat_group m)) g (usym_unit (fermat_group m))
  ≔ let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let Xs ≔ gset_underlying G X in
    let S ≔ fermat_orbit_subgroup m n f in
    let Y ≔ S .gset in
    let Ys ≔ gset_underlying G Y in
    let pt ≔ S .point in
    let H ≔ subgroup_group G S in
    let hH ≔ lagrange_subgroup_finite G S (fermat_group_finite m) (fermat_orbit_finite m n f) in
    let Fx ≔ Σ (USym G) (k ↦ Id Ys (gset_usym_act G Y k pt) pt) in
    let E ≔ subgroup_usym_fixing_equiv G S in
    let M ≔ (y ↦ Mere (Id (ActionType G X) (shape G, f) (shape G, y))) : Xs → Type in
    let lift : (k : USym G) → Id Xs (gset_usym_act G X k f) f → Fx
      ≔ k q ↦ (k, subtype_equal Xs M (y ↦ mere_isprop (Id (ActionType G X) (shape G, f) (shape G, y)))
                    (gset_usym_act G Y k pt) pt q) in
    let u ≔ lift g fix in
    let v ≔ lift (usym_unit G) (gset_act_unit G X f) in
    let hprop : isProp (USym H) ≔ fermat_cardinality_one_prop (USym H) hH b1 in
    let iu ≔ equiv_inverse_map (USym H) Fx E u in
    let iv ≔ equiv_inverse_map (USym H) Fx E v in
    let r : Id Fx u v
      ≔ concat Fx u (E .map iu) v (inverse Fx (E .map iu) u (equiv_counit (USym H) Fx E u))
          (concat Fx (E .map iu) (E .map iv) v (refl (E .map) (hprop iu iv)) (equiv_counit (USym H) Fx E v)) in
    r .fst

{` For p prime: if g ≠ refl fixes f, then f is constant. `}
def fermat_fixed_nonidentity_constant (m n : Nat) (hp : NatIsPrime (suc. m))
  (g : USym (fermat_group m)) (ng : Not (Id (USym (fermat_group m)) g (usym_unit (fermat_group m))))
  (f : Fin (suc. m) → Fin n)
  (fix : Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f)
  : FermatConstant m n f
  ≔ let G ≔ fermat_group m in
    let S ≔ fermat_orbit_subgroup m n f in
    let a ≔ gset_card G (S .gset) (fermat_orbit_finite m n f) in
    let b ≔ group_card (subgroup_group G S)
              (lagrange_subgroup_finite G S (fermat_group_finite m) (fermat_orbit_finite m n f)) in
    let pe : Id Nat (suc. m) (mul a b) ≔ fermat_lagrange m n f in
    let da : NatDivides a (suc. m)
      ≔ nat_divides_intro a (suc. m) b (concat Nat (suc. m) (mul a b) (mul b a) pe (mul_comm a b)) in
    match hp .snd a da [
    | inl. a1 ↦ fermat_fixed_by_all_constant m n f (fermat_orbit_one_fixed m n f a1)
    | inr. ap ↦
      absurd (FermatConstant m n f)
        (ng (fermat_stabilizer_one_unit m n f
          (fermat_mul_cancel_one m b
            (transport Nat (j ↦ Id Nat (suc. m) (mul j b)) a (suc. m) ap pe)) g fix)) ]

{` X^g for g ≠ refl is the set of constant functions, a copy of Fin n. `}
def fermat_fixed_by_nonidentity_equiv (m n : Nat) (hp : NatIsPrime (suc. m))
  (g : USym (fermat_group m)) (ng : Not (Id (USym (fermat_group m)) g (usym_unit (fermat_group m))))
  : Equiv (FixedBy (fermat_group m) (fermat_gset m n) g) (Fin n)
  ≔ let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let Xs ≔ Fin (suc. m) → Fin n in
    compose_equiv (FixedBy G X g) (Σ Xs (f ↦ FermatConstant m n f)) (Fin n)
      (family_equiv Xs (f ↦ Id Xs (gset_usym_act G X g f) f) (f ↦ FermatConstant m n f)
        (f ↦ iff_equiv (Id Xs (gset_usym_act G X g f) f) (FermatConstant m n f)
          (gset_underlying_set G X (gset_usym_act G X g f) f) (fermat_constant_prop m n f)
          (fermc ↦ fermat_fixed_nonidentity_constant m n hp g ng f fermc)
          (c ↦ fermat_constant_fixed_by m n f c g)))
      (fermat_constants_equiv m n)

{` X^refl is all of X(sh_G) (for any G-set). `}
def fixed_by_unit_equiv (G : Group) (X : GSet G) : Equiv (FixedBy G X (usym_unit G)) (gset_underlying G X)
  ≔ let Xs ≔ gset_underlying G X in
    quasi_inverse_equiv (FixedBy G X (usym_unit G)) Xs (u ↦ u .fst) (x ↦ (x, gset_act_unit G X x))
      (u ↦ subtype_equal Xs (x ↦ Id Xs (gset_usym_act G X (usym_unit G) x) x)
        (x ↦ gset_underlying_set G X (gset_usym_act G X (usym_unit G) x) x)
        (u .fst, gset_act_unit G X (u .fst)) u (refl (u .fst)))
      (x ↦ refl x)
