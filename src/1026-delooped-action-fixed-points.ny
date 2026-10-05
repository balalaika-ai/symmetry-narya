export "1023-p-group-fixed-points"
export "560-gset-action-equivalences"

{` Chapter 10, helper for thm:cauchys: a G-set given by an action
   f : Hom(G, Σ_S) on a set S (the delooping action_to_gset G S f of
   rem:GSet=SetHomG). Its underlying set is S (transport along the pointing
   path of f), the action of g is permutation by f(g), so its cardinality
   is |S| and its fixed points are the points of S fixed by every f(g). `}

def fingp_transport_retraction (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B x)
  : Id (B x) (transport A B y x (inverse A x y p) (transport A B x y p b)) b
  ≔ calc
      transport A B y x (inverse A x y p) (transport A B x y p b)
      = transport A B x x (concat A x y x p (inverse A x y p)) b
        by inverse (B x) (transport A B x x (concat A x y x p (inverse A x y p)) b)
          (transport A B y x (inverse A x y p) (transport A B x y p b))
          (transport_concat A B x y x p (inverse A x y p) b)
      = transport A B x x (refl x) b
        by refl ((q ↦ transport A B x x q b) : Id A x x → B x) (concat_inverse_right A x y p)
      = b by transport_refl A B x b ∎

{` The identification of S with the underlying set of the delooped G-set. `}
def delooped_underlying_equiv (G : Group) (S : SetTypes) (f : GroupActionOnSet G S)
  : Equiv (S .fst) (gset_underlying G (action_to_gset G S f))
  ≔ let F : SetTypes → Type ≔ T ↦ T .fst in
    let T ≔ action_to_gset G S f (shape G) in
    let p ≔ action_to_gset_underlying G S f in
    quasi_inverse_equiv (S .fst) (T .fst) (action_to_gset_transport G S f)
      (transport SetTypes F T S (inverse SetTypes S T p))
      (fingp_transport_retraction SetTypes F S T p) (transport_inverse_section SetTypes F S T p)

def delooped_card (G : Group) (S : SetTypes) (f : GroupActionOnSet G S) (hS : IsFinite (S .fst))
  : Id Nat (cardinality (S .fst) hS)
      (gset_card G (action_to_gset G S f)
        (finite_of_equiv (gset_underlying G (action_to_gset G S f)) (S .fst)
          (canonical_inverse_equiv (S .fst) (gset_underlying G (action_to_gset G S f)) (delooped_underlying_equiv G S f)) hS))
  ≔ cardinality_equiv (S .fst) (gset_underlying G (action_to_gset G S f)) (delooped_underlying_equiv G S f) hS
      (finite_of_equiv (gset_underlying G (action_to_gset G S f)) (S .fst)
        (canonical_inverse_equiv (S .fst) (gset_underlying G (action_to_gset G S f)) (delooped_underlying_equiv G S f)) hS)

{` Points of S fixed by every permutation f(g). `}
def ActionFixedPoints (G : Group) (S : SetTypes) (f : GroupActionOnSet G S) : Type
  ≔ Σ (S .fst) (s ↦ (g : USym G) → Id (S .fst) (permutation_action S (usym_hom G (permutation_group S) f g) s) s)

def delooped_fixed_points_equiv (G : Group) (S : SetTypes) (f : GroupActionOnSet G S)
  : Equiv (ActionFixedPoints G S f) (GSetFixedPoints G (action_to_gset G S f))
  ≔ let X ≔ action_to_gset G S f in
    let Y ≔ gset_underlying G X in
    let e ≔ delooped_underlying_equiv G S f in
    let φ : S .fst → Y ≔ e .map in
    let act : USym G → S .fst → S .fst ≔ g ↦ permutation_action S (usym_hom G (permutation_group S) f g) in
    let P : Y → Type ≔ y ↦ (g : USym G) → Id Y (gset_usym_act G X g y) y in
    compose_equiv (ActionFixedPoints G S f) (Σ (S .fst) (s ↦ P (φ s))) (GSetFixedPoints G X)
      (family_equiv (S .fst) (s ↦ (g : USym G) → Id (S .fst) (act g s) s) (s ↦ P (φ s))
        (s ↦ iff_equiv ((g : USym G) → Id (S .fst) (act g s) s) (P (φ s))
          (pi_prop (USym G) (g ↦ Id (S .fst) (act g s) s) (g ↦ S .snd (act g s) s))
          (gset_fixed_points_prop G X (φ s))
          (h g ↦ concat Y (gset_usym_act G X g (φ s)) (φ (act g s)) (φ s)
            (action_to_gset_usym_act G S f g s) (refl φ (h g)))
          (h g ↦ equivalence_injective (S .fst) Y e (act g s) s
            (concat Y (φ (act g s)) (gset_usym_act G X g (φ s)) (φ s)
              (inverse Y (gset_usym_act G X g (φ s)) (φ (act g s)) (action_to_gset_usym_act G S f g s)) (h g)))))
      (sigma_pullback_equiv (S .fst) Y e P)
