{` Blind statements for chapter 5 (actions.tex), section "Invariant maps and orbits". `}
export "02-subgroups"

{` def:actiontype (1). X_hG ≔ Σ_{z:BG} X(z). `}
def BlindActionType (G : Group) (X : BlindGSet G) : Type ≔ BlindTot G X

{` def:actiontype (2). X^hG ≔ Π_{z:BG} X(z). `}
def BlindInvariantMaps (G : Group) (X : BlindGSet G) : Type ≔ (z : BlindBG G) → X z .fst

def blind_istrans_prop (G : Group) (X : BlindGSet G) : isProp (BlindIsTrans G X)
  ≔ mere_isprop (Σ (X (shape G) .fst)
      (x ↦ (y : X (shape G) .fst) → Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) x (blind_usym_act G X g y)))))

{` def:actiontype (3). X/G ≔ Σ_{P : Sub_G(X)} istrans(X_P). `}
def BlindOrbits (G : Group) (X : BlindGSet G) : Type
  ≔ Σ (BlindSubG G X) (P ↦ BlindIsTrans G (blind_gsubset_underlying G X P))

def blind_orbits_set (G : Group) (X : BlindGSet G) : isSet (BlindOrbits G X)
  ≔ sigma_set (BlindSubG G X) (P ↦ BlindIsTrans G (blind_gsubset_underlying G X P))
      (pi_set (BlindBG G) (z ↦ X z .fst → PropTypes) (z ↦ pi_set (X z .fst) (_ ↦ PropTypes) (_ ↦ propositions_set)))
      (P ↦ prop_is_set (BlindIsTrans G (blind_gsubset_underlying G X P)) (blind_istrans_prop G (blind_gsubset_underlying G X P)))

{` def:actiontype, footnote: an invariant map f satisfies f(z) = g · f(z) for g : z = z. `}
def blind_invariant_map_fixed : Type
  ≔ (G : Group) (X : BlindGSet G) (f : BlindInvariantMaps G X) (z : BlindBG G) (g : Id (BlindBG G) z z)
    → Id (X z .fst) (f z) (blind_act G X z z g (f z))

{` def:actiontype, footnote: princ Z has no invariant maps. `}
def blind_princ_Z_no_invariant_maps : Type
  ≔ (C : CircleSignature) → Not (BlindInvariantMaps (circle_group C) (blind_princ (circle_group C)))

{` rem:path-in-action-type (and its truncated version). `}
def blind_path_in_action_type : Type
  ≔ (G : Group) (X : BlindGSet G) (z w : BlindBG G) (x : X z .fst) (y : X w .fst)
    → Product
        (Equiv (Id (BlindActionType G X) (z, x) (w, y)) (Σ (Id (BlindBG G) z w) (g ↦ Id (X w .fst) (blind_act G X z w g x) y)))
        (Equiv (Mere (Id (BlindActionType G X) (z, x) (w, y)))
           (Mere (Σ (Id (BlindBG G) z w) (g ↦ Id (X w .fst) (blind_act G X z w g x) y))))

{` def:orbit-map. [u]_0 sends z to x ↦ ‖u = (z, x)‖. `}
def blind_orbit_class0 (G : Group) (X : BlindGSet G) (u : BlindActionType G X) : BlindSubG G X
  ≔ z x ↦ (Mere (Id (BlindActionType G X) u (z, x)), mere_isprop (Id (BlindActionType G X) u (z, x)))

{` lem:[]0-maps-to-X/G: the underlying G-set of every [u]_0 is transitive. `}
def BlindOrbitWitness (G : Group) (X : BlindGSet G) : Type
  ≔ (u : BlindActionType G X) → BlindIsTrans G (blind_gsubset_underlying G X (blind_orbit_class0 G X u))

def blind_orbit_class0_transitive : Type ≔ (G : Group) (X : BlindGSet G) → BlindOrbitWitness G X

{` lem:[]0-maps-to-X/G: hence [-]_0 : X_hG → X/G. The map depends on the (propositional, unique) witness τ;
   the statements below quantify over τ, whose existence is blind_orbit_class0_transitive. `}
def blind_orbit_class (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (u : BlindActionType G X) : BlindOrbits G X
  ≔ (blind_orbit_class0 G X u, τ u)

{` lem:X/G=setTruncX_hG: [-]_0 is surjective, and (X/G, [-]_0) = (‖X_hG‖_0, |-|_0) uniquely in Σ_{S:Set}(X_hG → S). `}
def blind_X_G_setTrunc : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X)
    → Product (Surjective (BlindActionType G X) (BlindOrbits G X) (blind_orbit_class G X τ))
        (BookIsContr (Id (Σ SetTypes (S ↦ BlindActionType G X → S .fst))
           ((BlindOrbits G X, blind_orbits_set G X), blind_orbit_class G X τ)
           ((SetTrunc (BlindActionType G X), set_trunc_set (BlindActionType G X)), set_trunc (BlindActionType G X))))

{` cor:orbit-equiv. [x] ≔ [(sh_G, x)]_0. `}
def blind_orbit_of (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst) : BlindOrbits G X
  ≔ blind_orbit_class G X τ (shape G, x)

def BlindSameOrbitRel (G : Group) (X : BlindGSet G) (x y : X (shape G) .fst) : Type
  ≔ Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) (blind_usym_act G X g x) y))

{` cor:orbit-equiv: [x] = [y] ≃ ∃g (g·x = y); [-] surjective; [-] factors uniquely by an equivalence through the
   quotient of X(sh_G) by that relation (any equivalence relation R with this predicate). `}
def blind_orbit_equiv : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X)
    → Product
        ((x y : X (shape G) .fst) → Equiv (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (BlindSameOrbitRel G X x y))
      (Product
        (Surjective (X (shape G) .fst) (BlindOrbits G X) (blind_orbit_of G X τ))
        ((R : EquivalenceRelation (X (shape G) .fst))
         (hR : (x y : X (shape G) .fst) → Id Type (R .predicate x y .fst) (BlindSameOrbitRel G X x y))
         → Σ (BookIsContr (Σ (Quotient (X (shape G) .fst) R → BlindOrbits G X)
                (f ↦ (x : X (shape G) .fst) → Id (BlindOrbits G X) (f (quotient_class (X (shape G) .fst) R x)) (blind_orbit_of G X τ x))))
             (c ↦ BookIsEquiv (Quotient (X (shape G) .fst) R) (BlindOrbits G X) (c .center .fst))))

{` rem:SubGX=Sub(X/G). `}
def blind_SubGX_Sub_orbits : Type
  ≔ (G : Group) (X : BlindGSet G) → Equiv (BlindSubG G X) (Subtypes (BlindOrbits G X))

{` xca:transX-just1orbit. `}
def blind_transX_just1orbit : Type
  ≔ (G : Group) (X : BlindGSet G) → BlindIff (BookIsContr (BlindOrbits G X)) (BlindIsTrans G X)

{` rem:equivalents-of-[x]=[y]: all six propositions are equivalent (to the first). `}
def blind_equivalents_xy : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x y : X (shape G) .fst)
    → Product
        (BlindIff (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (Id (X (shape G) .fst → PropTypes) (blind_orbit_of G X τ x .fst (shape G)) (blind_orbit_of G X τ y .fst (shape G))))
      (Product
        (BlindIff (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y)) (BlindSameOrbitRel G X x y))
      (Product
        (BlindIff (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (Mere (Id (BlindActionType G X) (shape G, x) (shape G, y))))
      (Product
        (BlindIff (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (blind_orbit_of G X τ x .fst (shape G) y .fst))
        (BlindIff (Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (blind_orbit_of G X τ y .fst (shape G) x .fst)))))

{` def:orbit-stabilizer (1). G_x ≔ Aut_{X_hG}(sh_G, x). `}
def blind_stabilizer (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : Group
  ≔ automorphism_group (BlindActionType G X) (blind_tot_groupoid G X) (shape G, x)

{` def:orbit-stabilizer (1). i_x ≔ mkgroup(fst), pointed trivially. `}
def blind_stabilizer_incl (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : GroupHom (blind_stabilizer G X x) G
  ≔ mkhom (blind_stabilizer G X x) G ((u ↦ u .fst .fst), refl (shape G))

{` def:orbit-stabilizer (1): fst : BG_x → BG is a set bundle. `}
def blind_stabilizer_covering : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst)
    → IsCovering (BlindBG (blind_stabilizer G X x)) (BlindBG G) (u ↦ u .fst .fst)

{` def:orbit-stabilizer (1): (G_x, i_x) is a monomorphism. `}
def blind_stabilizer_mono : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst)
    → BlindIsMono (blind_stabilizer G X x) G (blind_stabilizer_incl G X x)

{` def:orbit-stabilizer (1): for (X, pt) : Sub(G), (G_pt, i_pt) is the corresponding monomorphism. `}
def blind_stabilizer_of_subgroup : Type
  ≔ (G : Group) (S : BlindSubgroups G)
    → Id (BlindHomInto G) (blind_stabilizer G (S .fst) (S .snd .fst), blind_stabilizer_incl G (S .fst) (S .snd .fst)) (blind_F0 G S)

{` def:orbit-stabilizer (2). G · x ≔ {y : X(sh_G) | [x] = [y]}. `}
def BlindOrbitSet (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst) : Type
  ≔ Σ (X (shape G) .fst) (y ↦ Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))

def blind_tot_step (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) (g : USym G)
  : Id (BlindActionType G X) (shape G, x) (shape G, blind_usym_act G X g x)
  ≔ (g, pathover_of_eq (BlindBG G) (u ↦ X u .fst) (shape G) (shape G) g x (blind_usym_act G X g x) (refl (blind_usym_act G X g x)))

{` The map (- · x) : USym G → G · x. `}
def blind_orbit_map (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst) (g : USym G)
  : BlindOrbitSet G X τ x
  ≔ (blind_usym_act G X g x, refl (blind_orbit_class G X τ) (blind_tot_step G X x g))

{` rem:orbit-fibs. X_[x](z) ≔ Σ_{y : X(z)} ‖(sh_G, x) = (z, y)‖ (the printed X(sh_G) read as X(z)). `}
def blind_orbit_underlying (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : BlindGSet G
  ≔ blind_gsubset_underlying G X (blind_orbit_class0 G X (shape G, x))

{` rem:orbit-fibs: (X_[x])_hG pointed at (sh_G, x) is BG_x; the underlying set of X_[x] is G · x. `}
def blind_orbit_fibs : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst)
    → Product
        (BookPointedEquiv
           (BlindTot G (blind_orbit_underlying G X x),
            (shape G, (x, mere (Id (BlindActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x)))))
           (BG (blind_stabilizer G X x)))
        (Equiv (blind_orbit_underlying G X x (shape G) .fst) (BlindOrbitSet G X τ x))

{` xca:[x]=[y]-implies-||Gx=Gy||. `}
def blind_same_orbit_stabilizers : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x y : X (shape G) .fst)
    → Id (BlindOrbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y)
    → Mere (Id Group (blind_stabilizer G X x) (blind_stabilizer G X y))

{` rem:subgrp-is-stabsubgr. `}
def blind_subgrp_is_stabsubgr : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst)
    → Product
        (Id (BlindHomInto G)
           (blind_F0 G (blind_orbit_underlying G X x,
              ((x, mere (Id (BlindActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x))), τ (shape G, x))))
           (blind_stabilizer G X x, blind_stabilizer_incl G X x))
        ((t : BlindIsTrans G X)
         → Id (BlindHomInto G) (blind_stabilizer G X x, blind_stabilizer_incl G X x) (blind_F0 G (X, (x, t))))

{` lem:splitting into orbits. `}
def blind_splitting_into_orbits : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X)
    → BookIsEquiv (Σ (BlindOrbits G X) (O ↦ BookFiber (X (shape G) .fst) (BlindOrbits G X) (blind_orbit_of G X τ) O))
        (X (shape G) .fst) (u ↦ u .snd .fst)

{` def:fixed-free. `}
def BlindFixed (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : Type
  ≔ IsGroupIso (blind_stabilizer G X x) G (blind_stabilizer_incl G X x)

def BlindFree (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : Type
  ≔ Id Group (blind_stabilizer G X x) trivial_group

def BlindGSetFree (G : Group) (X : BlindGSet G) : Type ≔ (x : X (shape G) .fst) → BlindFree G X x

{` exa:fixed-free-neither. `}
def blind_triv_fixed : Type ≔ (G : Group) (S : SetTypes) (s : S .fst) → BlindFixed G (blind_triv G S) s

def blind_princ_free : Type ≔ (G : Group) (g : USym G) → BlindFree G (blind_princ G) g

def blind_princ_tot_contractible : Type ≔ (G : Group) → BookIsContr (BlindTot G (blind_princ G))

{` The C₄-set of exa:prep-burnside: (A, f) ↦ (A → 2). `}
def blind_four : Nat ≔ suc. three

def blind_C4 : Group ≔ cyclic_group_fin three

def blind_c4_set : BlindGSet blind_C4
  ≔ c ↦ (c .fst .fst .fst .fst → Fin two, pi_set (c .fst .fst .fst .fst) (_ ↦ Fin two) (_ ↦ fin_set two))

def blind_c4_s (x : Fin blind_four) : Fin blind_four ≔ finite_fin_successor three .map x
def blind_c4_e0 : Fin blind_four ≔ inr. star.
def blind_c4_e1 : Fin blind_four ≔ blind_c4_s blind_c4_e0
def blind_c4_e2 : Fin blind_four ≔ blind_c4_s blind_c4_e1
def blind_c4_e3 : Fin blind_four ≔ blind_c4_s blind_c4_e2

def blind_bool_of_dec (A : Type) (d : Decidable A) : Bool ≔ match d [ inl. _ ↦ true. | inr. _ ↦ false. ]
def blind_and (a b : Bool) : Bool ≔ match a [ true. ↦ b | false. ↦ false. ]
def blind_fin2_eq (a b : Fin two) : Bool ≔ blind_bool_of_dec (Id (Fin two) a b) (fin_decidable_equality two a b)

def blind_c4_constant (f : Fin blind_four → Fin two) : Bool
  ≔ blind_and (blind_fin2_eq (f blind_c4_e0) (f blind_c4_e1))
      (blind_and (blind_fin2_eq (f blind_c4_e1) (f blind_c4_e2)) (blind_fin2_eq (f blind_c4_e2) (f blind_c4_e3)))

def blind_c4_period2 (f : Fin blind_four → Fin two) : Bool
  ≔ blind_and (blind_fin2_eq (f blind_c4_e0) (f blind_c4_e2)) (blind_fin2_eq (f blind_c4_e1) (f blind_c4_e3))

def blind_select (c p : Bool) (a b d : Nat) : Nat ≔ match c [ true. ↦ a | false. ↦ match p [ true. ↦ b | false. ↦ d ] ]

{` fig:C4-action-on-4-bits: stabilizer sizes 4 (constant), 2 (0101, 1010), 1 (otherwise); orbit sizes 1, 2, 4. `}
def blind_c4_stab_card (f : Fin blind_four → Fin two) : Nat
  ≔ blind_select (blind_c4_constant f) (blind_c4_period2 f) blind_four two (suc. zero.)

def blind_c4_orbit_card (f : Fin blind_four → Fin two) : Nat
  ≔ blind_select (blind_c4_constant f) (blind_c4_period2 f) (suc. zero.) two blind_four

{` exa:fixed-free-neither: in the C₄-set, x is fixed iff constant, free iff not of period 2. `}
def blind_c4_fixed_free : Type
  ≔ (f : Fin blind_four → Fin two)
    → Product (BlindIff (BlindFixed blind_C4 blind_c4_set f) (Id Bool (blind_c4_constant f) true.))
        (BlindIff (BlindFree blind_C4 blind_c4_set f) (Id Bool (blind_c4_period2 f) false.))

{` xca:fixed-free-neither: G_s = G for triv S; BG_g contractible for princ G; the stabilizers of the C₄-set. `}
def blind_xca_fixed_free_neither : Type
  ≔ Product ((G : Group) (S : SetTypes) (s : S .fst) → Id Group (blind_stabilizer G (blind_triv G S) s) G)
    (Product ((G : Group) (g : USym G) → BookIsContr (BlindBG (blind_stabilizer G (blind_princ G) g)))
      ((f : Fin blind_four → Fin two)
       → Σ (IsFiniteGroup (blind_stabilizer blind_C4 blind_c4_set f))
           (h ↦ Id Nat (group_card (blind_stabilizer blind_C4 blind_c4_set f) h) (blind_c4_stab_card f))))

{` lem:free-pt-char: (- · x) : USym G → G · x is surjective, and it is injective iff x is free. `}
def blind_free_pt_char : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst)
    → Product (Surjective (USym G) (BlindOrbitSet G X τ x) (blind_orbit_map G X τ x))
        (BlindIff (BlindFree G X x) (IsEmbedding (USym G) (BlindOrbitSet G X τ x) (blind_orbit_map G X τ x)))

{` lem:X_hG-set-iff-Xfree. `}
def blind_X_hG_set_iff_free : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X)
    → Product
        (BlindIff (isSet (BlindActionType G X)) (BookIsEquiv (BlindActionType G X) (BlindOrbits G X) (blind_orbit_class G X τ)))
        (BlindIff (isSet (BlindActionType G X)) (BlindGSetFree G X))

{` lem:fixed-char. `}
def blind_fixed_char : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst)
    → Product (BlindIff (BlindFixed G X x) (BookIsContr (BlindOrbitSet G X τ x)))
        (BlindIff (BlindFixed G X x) ((g : USym G) → Id (X (shape G) .fst) x (blind_usym_act G X g x)))

{` lem:fixpts-are-fixed. ev : X^hG → X(sh_G) is injective with image the fixed elements. `}
def blind_fixpts_are_fixed : Type
  ≔ (G : Group) (X : BlindGSet G)
    → Product (IsEmbedding (BlindInvariantMaps G X) (X (shape G) .fst) (f ↦ f (shape G)))
        ((x : X (shape G) .fst)
         → BlindIff (Mere (BookFiber (BlindInvariantMaps G X) (X (shape G) .fst) (f ↦ f (shape G)) x)) (BlindFixed G X x))

{` xca:Gset-A->B. G = Σ₂ × Σ₂, X(A, B) ≔ (A → B), and the easier cases. `}
def blind_S2xS2 : Group ≔ product_group (symmetric_group two) (symmetric_group two)

def blind_AB_set : BlindGSet blind_S2xS2
  ≔ u ↦ (u .fst .fst .fst → u .snd .fst .fst, pi_set (u .fst .fst .fst) (_ ↦ u .snd .fst .fst) (_ ↦ u .snd .fst .snd))

def blind_const22_set : BlindGSet blind_S2xS2
  ≔ blind_triv blind_S2xS2 (Product (Fin two) (Fin two), product_set (Fin two) (Fin two) (fin_set two) (fin_set two))

def blind_A2_set : BlindGSet (symmetric_group two)
  ≔ A ↦ (A .fst .fst → Fin two, pi_set (A .fst .fst) (_ ↦ Fin two) (_ ↦ fin_set two))

def blind_2B_set : BlindGSet (symmetric_group two)
  ≔ B ↦ (Fin two → B .fst .fst, pi_set (Fin two) (_ ↦ B .fst .fst) (_ ↦ B .fst .snd))

{` xca:Gset-A->B: (σ, τ) · f = τ ∘ f ∘ σ⁻¹. `}
def blind_AB_action : Type
  ≔ (g : USym blind_S2xS2) (f : Fin two → Fin two) (a : Fin two)
    → Id (Fin two) (blind_usym_act blind_S2xS2 blind_AB_set g f a)
        (permutation_action (standard_set two) (g .snd)
           (f (permutation_action (standard_set two) (usym_inv (symmetric_group two) (g .fst)) a)))

{` xca:Gset-A->B: two orbits (constants, bijections), no invariant maps. `}
def blind_AB_orbits_invariants : Type
  ≔ Product (Equiv (BlindOrbits blind_S2xS2 blind_AB_set) (Fin two)) (Not (BlindInvariantMaps blind_S2xS2 blind_AB_set))

{` xca:Gset-A->B: the constant G-set 2 × 2: four orbits, four invariant maps. `}
def blind_const22_orbits_invariants : Type
  ≔ Product (Equiv (BlindOrbits blind_S2xS2 blind_const22_set) (Product (Fin two) (Fin two)))
      (Equiv (BlindInvariantMaps blind_S2xS2 blind_const22_set) (Product (Fin two) (Fin two)))

{` xca:Gset-A->B: X(-, 2): three orbits, two invariant maps (the constants). `}
def blind_A2_orbits_invariants : Type
  ≔ Product (Equiv (BlindOrbits (symmetric_group two) blind_A2_set) (Fin three))
      (Equiv (BlindInvariantMaps (symmetric_group two) blind_A2_set) (Fin two))

{` xca:Gset-A->B: X(2, -): two orbits, no invariant maps. `}
def blind_2B_orbits_invariants : Type
  ≔ Product (Equiv (BlindOrbits (symmetric_group two) blind_2B_set) (Fin two))
      (Not (BlindInvariantMaps (symmetric_group two) blind_2B_set))

{` xca:HomGsets-ev. The G-set z ↦ (X(z) → Y(z)). `}
def blind_fun_gset (G : Group) (X Y : BlindGSet G) : BlindGSet G
  ≔ z ↦ (X z .fst → Y z .fst, pi_set (X z .fst) (_ ↦ Y z .fst) (_ ↦ Y z .snd))

{` xca:HomGsets-ev: evaluation at sh_G is an equivalence onto the subset of fixed elements
   (stated as: an embedding whose image is exactly the fixed elements). `}
def blind_HomGsets_ev : Type
  ≔ (G : Group) (X Y : BlindGSet G)
    → Product (IsEmbedding (BlindHomG G X Y) (X (shape G) .fst → Y (shape G) .fst) (f ↦ f (shape G)))
        ((φ : X (shape G) .fst → Y (shape G) .fst)
         → BlindIff (Mere (BookFiber (BlindHomG G X Y) (X (shape G) .fst → Y (shape G) .fst) (f ↦ f (shape G)) φ))
             (BlindFixed G (blind_fun_gset G X Y) φ))

{` def:Gx-action-on-G. G̃_x ≔ princ G ∘ Bi_x. `}
def blind_tilde (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) : BlindGSet (blind_stabilizer G X x)
  ≔ u ↦ blind_princ G (u .fst .fst)

{` xca:Gx-action-on-G: s ·_{G̃x} g = s₁ g (book order), i.e. g followed by s₁. `}
def blind_Gx_action_on_G : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) (v : BlindBG (blind_stabilizer G X x))
    (s : Id (BlindBG (blind_stabilizer G X x)) (shape (blind_stabilizer G X x)) v) (g : USym G)
    → Id (Id (BlindBG G) (shape G) (v .fst .fst))
        (blind_act (blind_stabilizer G X x) (blind_tilde G X x) (shape (blind_stabilizer G X x)) v s g)
        (concat (BlindBG G) (shape G) (shape G) (v .fst .fst) g (s .fst .fst))

{` xca:fixed-free-neither-action-types. `}
def blind_fixed_free_neither_action_types : Type
  ≔ Product ((G : Group) (S : SetTypes) (s : S .fst)
               → BookIsContr (BlindTot (blind_stabilizer G (blind_triv G S) s) (blind_tilde G (blind_triv G S) s)))
    (Product ((G : Group) (g : USym G)
               → Equiv (BlindTot (blind_stabilizer G (blind_princ G) g) (blind_tilde G (blind_princ G) g)) (USym G))
      ((f : Fin blind_four → Fin two)
       → Σ (IsFinite (BlindTot (blind_stabilizer blind_C4 blind_c4_set f) (blind_tilde blind_C4 blind_c4_set f)))
           (h ↦ Id Nat (cardinality (BlindTot (blind_stabilizer blind_C4 blind_c4_set f) (blind_tilde blind_C4 blind_c4_set f)) h)
                  (blind_c4_orbit_card f))))

{` con:orbit-stabilizer. (G̃_x)_{hG_x} ≃ G · x. `}
def blind_orbit_stabilizer : Type
  ≔ (G : Group) (X : BlindGSet G) (τ : BlindOrbitWitness G X) (x : X (shape G) .fst)
    → Equiv (BlindTot (blind_stabilizer G X x) (blind_tilde G X x)) (BlindOrbitSet G X τ x)

{` cor:action-subgrp-free. `}
def blind_action_subgrp_free : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst) → BlindGSetFree (blind_stabilizer G X x) (blind_tilde G X x)

{` lem:cosets-Gx.g. `}
def blind_cosets_Gx_g : Type
  ≔ (G : Group) (X : BlindGSet G) (x : X (shape G) .fst)
    (τ : BlindOrbitWitness (blind_stabilizer G X x) (blind_tilde G X x)) (g : USym G)
    → BookIsEquiv (USym (blind_stabilizer G X x))
        (BlindOrbitSet (blind_stabilizer G X x) (blind_tilde G X x) τ g)
        (blind_orbit_map (blind_stabilizer G X x) (blind_tilde G X x) τ g)

{` con:preLagrange. X(sh_G) ≃ G̃_pt / G_pt. `}
def blind_preLagrange : Type
  ≔ (G : Group) (S : BlindSubgroups G)
    → Equiv (S .fst (shape G) .fst)
        (BlindOrbits (blind_stabilizer G (S .fst) (S .snd .fst)) (blind_tilde G (S .fst) (S .snd .fst)))
