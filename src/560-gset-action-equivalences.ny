export "505-gset-core-litmus"
export "436-maps-from-classifying-types"

{` Chapter 5 (actions.tex), sec:gsets and sec:actions:
   - xca:ptd-conn-to-comp (proved in module 436 as pointed_maps_into_component,
     restated here with the book's variables);
   - the text after def:action: (BG → A) ≃ Σ_{a:A} (action of G on a) for
     every type A (action_in_type_equiv), mapping X to X(sh_G) and the
     pointed map BG →* (A_(a), (a, !)) given by X;
   - rem:GSet=SetHomG and the identification after def:Gaction:
     GSet ≃ Σ_{S:Set} Hom(G, Σ_S) (gset_action_equiv), whose maps are the core's
     gset_to_action and action_to_gset, and the actions agree:
     g acts through gset_to_action G X as g ·_X - (gset_to_action_usym_act),
     and the delooped G-set of f : Hom(G, Σ_S) has the action f(g)
     (action_to_gset_usym_act). `}

{` xca:ptd-conn-to-comp. For pointed types (A, a), (B, b) with A connected,
   ((A, a) →* (B, b)) ≃ ((A, a) →* (B_(b), (b, !))). The map sends (f, p)
   to (x ↦ (f(x), !), p) (the pointing path is the component path with
   first component p); the inverse composes with fst. `}
def ptd_conn_to_comp_equiv (A B : Pointed) (hA : Connected (A .carrier))
  : Equiv (BookPointedMap A B)
      (BookPointedMap A (NativeComponent (B .carrier) (B .point), component_point (B .carrier) (B .point)))
  ≔ pointed_maps_into_component A hA (B .carrier) (B .point)

{` Litmus: the lifted map has the same values and pointing path in B, and
   the inverse round trip is reflexivity. `}
def ptd_conn_to_comp_values (A B : Pointed) (hA : Connected (A .carrier)) (f : BookPointedMap A B)
  (x : A .carrier)
  : Id (B .carrier) (ptd_conn_to_comp_equiv A B hA .map f .fst x .fst) (f .fst x)
  ≔ refl (f .fst x)

def ptd_conn_to_comp_pointing (A B : Pointed) (hA : Connected (A .carrier)) (f : BookPointedMap A B)
  : Id (Id (B .carrier) (B .point) (f .fst (A .point))) (ptd_conn_to_comp_equiv A B hA .map f .snd .fst) (f .snd)
  ≔ refl (f .snd)

def ptd_conn_to_comp_inverse (A B : Pointed) (hA : Connected (A .carrier)) (f : BookPointedMap A B)
  : Id (BookPointedMap A B)
      (equiv_inverse_map (BookPointedMap A B)
        (BookPointedMap A (NativeComponent (B .carrier) (B .point), component_point (B .carrier) (B .point)))
        (ptd_conn_to_comp_equiv A B hA) (ptd_conn_to_comp_equiv A B hA .map f)) f
  ≔ refl f

{` The first two steps of the chain of rem:GSet=SetHomG, for any type A:
   (BG → A) ≃ Σ_{a:A} Σ_{X : BG → A} (a = X(sh_G)) ≡ Σ_{a:A} (BG →* (A, a)),
   X ↦ (X(sh_G), (X, refl)); the inverse forgets a and the pointing path
   (lem:contract-away: Σ_a (a = X(sh_G)) is contractible). `}
def ActionInTypePointed (G : Group) (A : Type) : Type ≔ Σ A (a ↦ BookPointedMap (BG G) (A, a))

def action_in_type_pointed (G : Group) (A : Type) (X : BG G .carrier → A) : ActionInTypePointed G A
  ≔ (X (shape G), (X, refl (X (shape G))))

def action_in_type_pointed_counit (G : Group) (A : Type) (u : ActionInTypePointed G A)
  : Id (ActionInTypePointed G A) (action_in_type_pointed G A (u .snd .fst)) u
  ≔ let f ≔ u .snd .fst in
    let b ≔ f (shape G) in
    let T ≔ Σ A (x ↦ Id A x b) in
    refl ((t ↦ (t .fst, (f, t .snd))) : T → ActionInTypePointed G A)
      (contractible_prop T (path_to_contractible A b) (b, refl b) (u .fst, u .snd .snd))

def action_in_type_split_equiv (G : Group) (A : Type)
  : Equiv (BG G .carrier → A) (ActionInTypePointed G A)
  ≔ quasi_inverse_equiv (BG G .carrier → A) (ActionInTypePointed G A)
      (action_in_type_pointed G A) (u ↦ u .snd .fst) (X ↦ refl X) (action_in_type_pointed_counit G A)

{` sec:actions (after def:action): an action of G in A is the same as a
   pair of an object a : A and an action of G on a,
   (BG → A) ≃ Σ_{a:A} (BG →* (A_(a), (a, !))), for every type A (for a
   groupoid A the second component is literally Hom(G, Aut_A(a)), see
   action_in_type_group_equiv). The map is X ↦ (X(sh_G), z ↦ (X(z), !))
   (action_in_type_equiv_map, refl). `}
def action_in_type_equiv (G : Group) (A : Type)
  : Equiv (ActionInType G A) (Σ A (a ↦ ActionOnElement G A a))
  ≔ compose_equiv (ActionInType G A) (ActionInTypePointed G A) (Σ A (a ↦ ActionOnElement G A a))
      (action_in_type_split_equiv G A)
      (family_equiv A (a ↦ BookPointedMap (BG G) (A, a)) (a ↦ ActionOnElement G A a)
        (a ↦ pointed_maps_into_component (BG G) (bg_connected G) A a))

def action_in_type_equiv_map (G : Group) (A : Type) (X : ActionInType G A)
  : Id (Σ A (a ↦ ActionOnElement G A a)) (action_in_type_equiv G A .map X)
      (X (shape G), component_lift (BG G) (bg_connected G) A (X (shape G)) (X, refl (X (shape G))))
  ≔ refl (action_in_type_equiv G A .map X)

def action_in_type_equiv_object (G : Group) (A : Type) (X : ActionInType G A)
  : Id A (action_in_type_equiv G A .map X .fst) (action_object G A X)
  ≔ refl (X (shape G))

def action_in_type_equiv_values (G : Group) (A : Type) (X : ActionInType G A) (z : BG G .carrier)
  : Id A (action_in_type_equiv G A .map X .snd .fst z .fst) (X z)
  ≔ refl (X z)

def action_in_type_equiv_inverse (G : Group) (A : Type) (a : A) (k : ActionOnElement G A a)
  (z : BG G .carrier)
  : Id A (equiv_inverse_map (ActionInType G A) (Σ A (b ↦ ActionOnElement G A b)) (action_in_type_equiv G A) (a, k) z)
      (k .fst z .fst)
  ≔ refl (k .fst z .fst)

{` The displayed equivalence of sec:actions for a groupoid A, with the
   homomorphisms G → Aut_A(a) of def:action (Aut_A(a) is a group). `}
def action_in_type_group_equiv (G : Group) (A : Type) (hA : isGroupoid A)
  : Equiv (ActionInType G A) (Σ A (a ↦ GroupHom G (automorphism_group A hA a)))
  ≔ compose_equiv (ActionInType G A) (Σ A (a ↦ ActionOnElement G A a))
      (Σ A (a ↦ GroupHom G (automorphism_group A hA a)))
      (action_in_type_equiv G A)
      (family_equiv A (a ↦ ActionOnElement G A a) (a ↦ GroupHom G (automorphism_group A hA a))
        (a ↦ action_on_element_group_hom_equiv G A hA a))

{` rem:GSet=SetHomG, the chain as one composite: A ≔ Set. `}
def gset_action_composite_equiv (G : Group) : Equiv (GSet G) (Σ SetTypes (S ↦ GroupActionOnSet G S))
  ≔ action_in_type_group_equiv G SetTypes sets_groupoid

{` Its map agrees with (X(sh_G), gset_to_action G X) (they differ only in the
   propositional witnesses of the component), and its inverse map is
   action_to_gset (definitionally). `}
def gset_action_composite_map (G : Group) (X : GSet G)
  : Id (Σ SetTypes (S ↦ GroupActionOnSet G S)) (gset_action_composite_equiv G .map X)
      (X (shape G), gset_to_action G X)
  ≔ let S ≔ X (shape G) in
    refl ((f ↦ (S, f)) : GroupActionOnSet G S → Σ SetTypes (T ↦ GroupActionOnSet G T))
      (refl (mkhom G (permutation_group S))
        (component_lift_project (BG G) (bg_connected G) SetTypes S (hom_B G (permutation_group S) (gset_to_action G X))))

def gset_action_composite_inverse (G : Group) (u : Σ SetTypes (S ↦ GroupActionOnSet G S))
  : Id (GSet G)
      (equiv_inverse_map (GSet G) (Σ SetTypes (S ↦ GroupActionOnSet G S)) (gset_action_composite_equiv G) u)
      (action_to_gset G (u .fst) (u .snd))
  ≔ refl (action_to_gset G (u .fst) (u .snd))

{` rem:GSet=SetHomG and the sentence after def:Gaction: G-sets are sets
   with an action of G, GSet ≃ Σ_{S:Set} Hom(G, Σ_S), with map
   X ↦ (X(sh_G), gset_to_action G X) and inverse
   (S, f) ↦ action_to_gset G S f (z ↦ Bf(z)); the round trip on GSet is
   reflexivity. `}
def gset_action_equiv (G : Group) : Equiv (GSet G) (Σ SetTypes (S ↦ GroupActionOnSet G S))
  ≔ let E ≔ gset_action_composite_equiv G in
    let Q ≔ Σ SetTypes (S ↦ GroupActionOnSet G S) in
    quasi_inverse_equiv (GSet G) Q
      (X ↦ (X (shape G), gset_to_action G X)) (u ↦ action_to_gset G (u .fst) (u .snd))
      (X ↦ refl X)
      (u ↦ let Y ≔ action_to_gset G (u .fst) (u .snd) in
        concat Q (Y (shape G), gset_to_action G Y) (E .map Y) u
          (inverse Q (E .map Y) (Y (shape G), gset_to_action G Y) (gset_action_composite_map G Y))
          (equiv_counit (GSet G) Q E u))

def gset_action_equiv_map (G : Group) (X : GSet G)
  : Id (Σ SetTypes (S ↦ GroupActionOnSet G S)) (gset_action_equiv G .map X) (X (shape G), gset_to_action G X)
  ≔ refl (X (shape G), gset_to_action G X)

def gset_action_equiv_inverse (G : Group) (S : SetTypes) (f : GroupActionOnSet G S)
  : Id (GSet G) (equiv_inverse_map (GSet G) (Σ SetTypes (T ↦ GroupActionOnSet G T)) (gset_action_equiv G) (S, f))
      (action_to_gset G S f)
  ≔ refl (action_to_gset G S f)

{` rem:GSet=SetHomG: the action of g : USym G on X(sh_G) through the
   homomorphism gset_to_action G X : G → Σ_{X(sh_G)} (the permutation
   permutation_action of its symmetry) is g ·_X - (typal: the pointing path
   of gset_to_action is the component path of refl). `}
def gset_to_action_usym_act (G : Group) (X : GSet G) (g : USym G) (a : gset_underlying G X)
  : Id (gset_underlying G X)
      (permutation_action (X (shape G)) (usym_hom G (permutation_group (X (shape G))) (gset_to_action G X) g) a)
      (gset_usym_act G X g a)
  ≔ let S ≔ X (shape G) in
    let P ≔ NativeComponent SetTypes S in
    let pt ≔ component_point SetTypes S in
    let F : P → Type ≔ u ↦ u .fst .fst in
    let k ≔ hom_function G (permutation_group S) (gset_to_action G X) in
    let ks ≔ k (shape G) in
    let kpt : Id P pt ks ≔ hom_point G (permutation_group S) (gset_to_action G X) in
    let l : Id P ks ks ≔ refl k g in
    let triv : (b : S .fst) → Id (S .fst) (transport P F pt ks kpt b) b
      ≔ b ↦ transport_refl Type (Y ↦ Y) (S .fst) b in
    let y ≔ transport P F ks ks l a in
    calc
      transport P F pt pt (concat P pt ks pt kpt (concat P ks ks pt l (inverse P pt ks kpt))) a
      = transport P F ks pt (concat P ks ks pt l (inverse P pt ks kpt)) (transport P F pt ks kpt a)
        by transport_concat P F pt ks pt kpt (concat P ks ks pt l (inverse P pt ks kpt)) a
      = transport P F ks pt (inverse P pt ks kpt) (transport P F ks ks l (transport P F pt ks kpt a))
        by transport_concat P F ks ks pt l (inverse P pt ks kpt) (transport P F pt ks kpt a)
      = transport P F ks pt (inverse P pt ks kpt) y
        by refl ((b ↦ transport P F ks pt (inverse P pt ks kpt) (transport P F ks ks l b)) : S .fst → S .fst) (triv a)
      = transport P F ks pt (inverse P pt ks kpt) (transport P F pt ks kpt y)
        by refl (transport P F ks pt (inverse P pt ks kpt)) (inverse (S .fst) (transport P F pt ks kpt y) y (triv y))
      = y
        by transport_inverse_roundtrip P F pt ks kpt y ∎

{` rem:GSet=SetHomG, "conversely": the delooped G-set action_to_gset G S f
   has underlying set S (via the pointing path of f, action_to_gset_underlying)
   and the action of g is f(g): transporting along that identification
   intertwines f(g) = permutation_action S (usym_hom f g) with g · -. `}
def action_to_gset_transport (G : Group) (S : SetTypes) (f : GroupActionOnSet G S) (s : S .fst)
  : gset_underlying G (action_to_gset G S f)
  ≔ transport SetTypes (T ↦ T .fst) S (action_to_gset G S f (shape G)) (action_to_gset_underlying G S f) s

{` Transport along p after transport along p⁻¹ is the identity (a separate
   definition with abstract family B, which avoids E0500 for families
   given by projections). `}
def transport_inverse_section (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B y)
  : Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b
  ≔ calc
      transport A B x y p (transport A B y x (inverse A x y p) b)
      = transport A B y y (concat A y x y (inverse A x y p) p) b
        by inverse (B y) (transport A B y y (concat A y x y (inverse A x y p) p) b)
          (transport A B x y p (transport A B y x (inverse A x y p) b))
          (transport_concat A B y x y (inverse A x y p) p b)
      = transport A B y y (refl y) b
        by refl ((q ↦ transport A B y y q b) : Id A y y → B y) (concat_inverse_left A x y p)
      = b by transport_refl A B y b ∎

def action_to_gset_usym_act (G : Group) (S : SetTypes) (f : GroupActionOnSet G S) (g : USym G) (s : S .fst)
  : Id (gset_underlying G (action_to_gset G S f))
      (gset_usym_act G (action_to_gset G S f) g (action_to_gset_transport G S f s))
      (action_to_gset_transport G S f (permutation_action S (usym_hom G (permutation_group S) f g) s))
  ≔ let P ≔ NativeComponent SetTypes S in
    let pt ≔ component_point SetTypes S in
    let F : P → Type ≔ u ↦ u .fst .fst in
    let k ≔ hom_function G (permutation_group S) f in
    let ks ≔ k (shape G) in
    let kpt : Id P pt ks ≔ hom_point G (permutation_group S) f in
    let l : Id P ks ks ≔ refl k g in
    let y ≔ transport P F ks ks l (transport P F pt ks kpt s) in
    let conj ≔ concat P pt ks pt kpt (concat P ks ks pt l (inverse P pt ks kpt)) in
    let step1 : Id (F pt) (transport P F pt pt conj s) (transport P F ks pt (inverse P pt ks kpt) y)
      ≔ concat (F pt) (transport P F pt pt conj s)
          (transport P F ks pt (concat P ks ks pt l (inverse P pt ks kpt)) (transport P F pt ks kpt s))
          (transport P F ks pt (inverse P pt ks kpt) y)
          (transport_concat P F pt ks pt kpt (concat P ks ks pt l (inverse P pt ks kpt)) s)
          (transport_concat P F ks ks pt l (inverse P pt ks kpt) (transport P F pt ks kpt s)) in
    inverse (F ks) (transport P F pt ks kpt (transport P F pt pt conj s)) y
      (concat (F ks) (transport P F pt ks kpt (transport P F pt pt conj s))
        (transport P F pt ks kpt (transport P F ks pt (inverse P pt ks kpt) y)) y
        (refl (transport P F pt ks kpt) step1)
        (transport_inverse_section P F pt ks kpt y))

{` Litmus (Σ_3 acting on Fin 3): through gset_to_action of the standard
   Σ_3-set, τ = (0 1) sends 0 to 1. `}
def gset_to_action_sigma3_tau_zero
  : Id (Fin three)
      (permutation_action (standard_set three)
        (usym_hom (symmetric_group three) (permutation_group (standard_set three))
          (gset_to_action (symmetric_group three) (standard_symmetric_gset three)) sigma3_tau) fin3_zero)
      fin3_one
  ≔ gset_to_action_usym_act (symmetric_group three) (standard_symmetric_gset three) sigma3_tau fin3_zero

{` Litmus: the composite equivalence and gset_action_equiv send X to the
   underlying set X(sh_G). `}
def gset_action_equiv_underlying (G : Group) (X : GSet G)
  : Id SetTypes (gset_action_equiv G .map X .fst) (X (shape G))
  ≔ refl (X (shape G))
