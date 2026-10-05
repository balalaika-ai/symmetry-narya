export "956-outer-automorphisms"
export "202-higher-truncations"

{` Chapter 9 (subgroups.tex 2007-2100): cons:simpler-version-Out,
   Φ : Aut_{‖U‖₁}(|BG÷|₁) = Out(G).

   The 1-truncation ‖U‖₁ of the universe is the concrete truncation of
   module 202 (Trunc 2 Type, the join construction; no signature
   hypothesis is needed). Following the implementation, BΦ is the map of
   components induced by ψ : ‖U‖₁ → GSet(Aut(G)), the extension of
   X ↦ (G' ↦ ‖BG'÷ = X‖₀) (the book's φ(X, ω)), pointed through
   lemma:coker-out-action. Since both classifying types are connected,
   BΦ is an equivalence once ap_{BΦ} is one at the base point; this is
   shown by evaluating at |refl|₀ (an injection, out(G) being transitive)
   and computing that the composite ‖BG÷ = BG÷‖₀ → ‖BG÷ = BG÷‖₀ is the
   identity (the book's ψ_G(ev(ψ⁻¹ · ap_{BΦ}(p) · ψ)) = p̂). `}

{` ‖U‖₁ and |-|₁. `}
def UniverseOneTrunc : Type ≔ Trunc (suc. (suc. zero.)) Type

def universe_one_trunc_unit : Type → UniverseOneTrunc ≔ trunc_unit (suc. (suc. zero.)) Type

def universe_one_trunc_groupoid : isGroupoid UniverseOneTrunc
  ≔ hlevel_to_groupoid UniverseOneTrunc (trunc_level (suc. (suc. zero.)) Type)

{` "‖a = b‖₀ is equivalent to |a|₁ = |b|₁" (eq:trunc-path-eq at level 0). `}
def universe_one_trunc_paths (X Y : Type)
  : Equiv (SetTrunc (Id Type X Y)) (Id UniverseOneTrunc (universe_one_trunc_unit X) (universe_one_trunc_unit Y))
  ≔ compose_equiv (SetTrunc (Id Type X Y)) (Trunc (suc. zero.) (Id Type X Y))
      (Id UniverseOneTrunc (universe_one_trunc_unit X) (universe_one_trunc_unit Y))
      (canonical_inverse_equiv (Trunc (suc. zero.) (Id Type X Y)) (SetTrunc (Id Type X Y)) (trunc_one_set_trunc_equiv (Id Type X Y)))
      (trunc_path_equiv (suc. zero.) Type X Y)

{` The domain group Aut_{‖U‖₁}(|BG÷|₁). `}
def outer_simple_group (G : Group) : Group
  ≔ automorphism_group UniverseOneTrunc universe_one_trunc_groupoid (universe_one_trunc_unit (BG G .carrier))

{` φ on representatives: X ↦ (G' ↦ ‖BG'÷ = X‖₀), and its extension ψ. `}
def outer_family0 (G : Group) (X : Type) : GSet (group_aut G)
  ≔ G' ↦ (SetTrunc (Id Type (BG (G' .fst) .carrier) X), set_trunc_set (Id Type (BG (G' .fst) .carrier) X))

def outer_family (G : Group) : UniverseOneTrunc → GSet (group_aut G)
  ≔ trunc_extend (suc. (suc. zero.)) Type (truncation (suc. (suc. zero.)) Type) (GSet (group_aut G))
      (groupoid_to_hlevel (GSet (group_aut G)) (gset_groupoid (group_aut G))) (outer_family0 G)

def outer_family_beta (G : Group) (X : Type)
  : Id (GSet (group_aut G)) (outer_family0 G X) (outer_family G (universe_one_trunc_unit X))
  ≔ trunc_extend_beta (suc. (suc. zero.)) Type (truncation (suc. (suc. zero.)) Type) (GSet (group_aut G))
      (groupoid_to_hlevel (GSet (group_aut G)) (gset_groupoid (group_aut G))) (outer_family0 G) X

def outer_simple_point (G : Group)
  : Id (GSet (group_aut G)) (outer_gset G) (outer_family G (universe_one_trunc_unit (BG G .carrier)))
  ≔ concat (GSet (group_aut G)) (outer_gset G) (outer_paths_gset G) (outer_family G (universe_one_trunc_unit (BG G .carrier)))
      (outer_gset_path G) (outer_family_beta G (BG G .carrier))

{` Φ, with BΦ the induced map of components. `}
def outer_simple_hom (G : Group) : GroupHom (outer_simple_group G) (outer_aut_group G)
  ≔ ch9w2_aut_hom UniverseOneTrunc (GSet (group_aut G)) universe_one_trunc_groupoid (gset_groupoid (group_aut G))
      (outer_family G) (universe_one_trunc_unit (BG G .carrier)) (outer_gset G) (outer_simple_point G)

{` Helpers: right concatenation is an equivalence; if e is an embedding
   and e ∘ m an equivalence, m is an equivalence. `}
def ch9w2_concat_right_equiv (A : Type) (x y z : A) (q : Id A y z) : Equiv (Id A x y) (Id A x z)
  ≔ quasi_inverse_equiv (Id A x y) (Id A x z) (r ↦ concat A x y z r q) (s ↦ concat A x z y s (inverse A y z q))
      (r ↦ calc
        concat A x z y (concat A x y z r q) (inverse A y z q)
        = concat A x y y r (concat A y z y q (inverse A y z q)) by concat_assoc A x y z y r q (inverse A y z q)
        = concat A x y y r (refl y) by refl (concat A x y y r) (concat_inverse_right A y z q)
        = r by concat_p1 A x y r ∎)
      (s ↦ calc
        concat A x y z (concat A x z y s (inverse A y z q)) q
        = concat A x z z s (concat A z y z (inverse A y z q) q) by concat_assoc A x z y z s (inverse A y z q) q
        = concat A x z z s (refl z) by refl (concat A x z z s) (concat_inverse_left A y z q)
        = s by concat_p1 A x z s ∎)

def ch9w2_equiv_of_embedding_composite (A B C : Type) (m : A → B) (e : B → C) (he : IsEmbedding B C e)
  (hc : BookIsEquiv A C (x ↦ e (m x))) : BookIsEquiv A B m
  ≔ let E : Equiv B C
      ≔ native_equivalence B C (e, c ↦ ((m (hc c .center .fst), hc c .center .snd), t ↦ he c (m (hc c .center .fst), hc c .center .snd) t)) in
    let D : Equiv A C ≔ native_equivalence A C ((x ↦ e (m x)), hc) in
    book_equivalence A B
      (equiv_change_map A B (compose_equiv A C B D (canonical_inverse_equiv B C E)) m
        (x ↦ equiv_retraction B C E (m x))) .equiv

{` The book's computation, for an arbitrary extension ψ of φ (with
   β : φ(X) = ψ(|X|₁)) and an arbitrary path action gen of |-|₁ with
   gen(refl) = refl (kept abstract so that the concrete truncation is not
   unfolded): for p : BG÷ = Y, evaluating β_X · ap_ψ(gen p) · β_Y⁻¹ :
   φ(BG÷) = φ(Y) at |refl|₀ gives |p|₀. `}
def outer_simple_compute (G : Group) (U1 : Type) (u : Type → U1) (ψ : U1 → GSet (group_aut G))
  (β : (X : Type) → Id (GSet (group_aut G)) (outer_family0 G X) (ψ (u X)))
  (gen : (Y : Type) → Id Type (BG G .carrier) Y → Id U1 (u (BG G .carrier)) (u Y))
  (g0 : Id (Id U1 (u (BG G .carrier)) (u (BG G .carrier))) (gen (BG G .carrier) (refl (BG G .carrier))) (refl (u (BG G .carrier))))
  (Y : Type) (p : Id Type (BG G .carrier) Y)
  : Id (SetTrunc (Id Type (BG G .carrier) Y))
      (gset_path_eval (group_aut G) (outer_family0 G (BG G .carrier)) (outer_family0 G Y) (shape (group_aut G))
        (set_trunc (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)))
        (concat (GSet (group_aut G)) (outer_family0 G (BG G .carrier)) (ψ (u (BG G .carrier)))
          (outer_family0 G Y) (β (BG G .carrier))
          (concat (GSet (group_aut G)) (ψ (u (BG G .carrier))) (ψ (u Y)) (outer_family0 G Y)
            (refl ψ (gen Y p)) (inverse (GSet (group_aut G)) (outer_family0 G Y) (ψ (u Y)) (β Y)))))
      (set_trunc (Id Type (BG G .carrier) Y) p)
  ≔ let X ≔ BG G .carrier in let A ≔ group_aut G in let GS ≔ GSet A in
    let ψ0 ≔ outer_family0 G in
    let x0 ≔ set_trunc (Id Type X X) (refl X) in
    let ev : Id GS (ψ0 X) (ψ0 X) → SetTrunc (Id Type X X) ≔ gset_path_eval A (ψ0 X) (ψ0 X) (shape A) x0 in
    J Type X
      (Y p ↦ Id (SetTrunc (Id Type X Y))
        (gset_path_eval A (ψ0 X) (ψ0 Y) (shape A) x0
          (concat GS (ψ0 X) (ψ (u X)) (ψ0 Y) (β X)
            (concat GS (ψ (u X)) (ψ (u Y)) (ψ0 Y) (refl ψ (gen Y p)) (inverse GS (ψ0 Y) (ψ (u Y)) (β Y)))))
        (set_trunc (Id Type X Y) p))
      (calc
        ev (concat GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X) (concat GS (ψ (u X)) (ψ (u X)) (ψ0 X) (refl ψ (gen X (refl X))) (inverse GS (ψ0 X) (ψ (u X)) (β X))))
        = ev (concat GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X) (concat GS (ψ (u X)) (ψ (u X)) (ψ0 X) (refl ψ (refl (u X))) (inverse GS (ψ0 X) (ψ (u X)) (β X))))
          by refl ((r ↦ ev (concat GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X) (concat GS (ψ (u X)) (ψ (u X)) (ψ0 X) (refl ψ r) (inverse GS (ψ0 X) (ψ (u X)) (β X)))))
                : Id U1 (u X) (u X) → SetTrunc (Id Type X X)) g0
        = ev (concat GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X) (inverse GS (ψ0 X) (ψ (u X)) (β X)))
          by refl ((r ↦ ev (concat GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X) r)) : Id GS (ψ (u X)) (ψ0 X) → SetTrunc (Id Type X X))
               (concat_1p GS (ψ (u X)) (ψ0 X) (inverse GS (ψ0 X) (ψ (u X)) (β X)))
        = ev (refl (ψ0 X)) by refl ev (concat_inverse_right GS (ψ0 X) (ψ (u X)) (β X))
        = x0 by transport_refl GS (W ↦ W (shape A) .fst) (ψ0 X) x0 ∎)
      Y p

{` ap_ψ is an equivalence at |BG÷|₁, for any such data with a path
   equivalence tpe : ‖BG÷ = BG÷‖ ≃ (|BG÷|₁ = |BG÷|₁) agreeing with gen on
   representatives. `}
def outer_simple_eval_transitive (G : Group)
  : IsTransitive (group_aut G) (outer_family0 G (BG G .carrier))
  ≔ transport (GSet (group_aut G)) (IsTransitive (group_aut G)) (outer_gset G) (outer_paths_gset G) (outer_gset_path G)
      (cokernel_transitive G (group_aut G) (inn G))

def outer_simple_ap_equiv_gen (G : Group) (U1 : Type) (u : Type → U1) (ψ : U1 → GSet (group_aut G))
  (β : (X : Type) → Id (GSet (group_aut G)) (outer_family0 G X) (ψ (u X)))
  (gen : (Y : Type) → Id Type (BG G .carrier) Y → Id U1 (u (BG G .carrier)) (u Y))
  (g0 : Id (Id U1 (u (BG G .carrier)) (u (BG G .carrier))) (gen (BG G .carrier) (refl (BG G .carrier))) (refl (u (BG G .carrier))))
  (tpe : Equiv (Trunc (suc. zero.) (Id Type (BG G .carrier) (BG G .carrier))) (Id U1 (u (BG G .carrier)) (u (BG G .carrier))))
  (tu : (p : Id Type (BG G .carrier) (BG G .carrier))
        → Id (Id U1 (u (BG G .carrier)) (u (BG G .carrier))) (gen (BG G .carrier) p)
            (tpe .map (trunc_unit (suc. zero.) (Id Type (BG G .carrier) (BG G .carrier)) p)))
  : BookIsEquiv (Id U1 (u (BG G .carrier)) (u (BG G .carrier))) (Id (GSet (group_aut G)) (ψ (u (BG G .carrier))) (ψ (u (BG G .carrier))))
      (map_path U1 (GSet (group_aut G)) ψ (u (BG G .carrier)) (u (BG G .carrier)))
  ≔ let X ≔ BG G .carrier in let A ≔ group_aut G in let GS ≔ GSet A in
    let ψ0 ≔ outer_family0 G in
    let x0 ≔ set_trunc (Id Type X X) (refl X) in
    let T1 ≔ Trunc (suc. zero.) (Id Type X X) in
    let ST ≔ SetTrunc (Id Type X X) in
    let apψ ≔ map_path U1 GS ψ (u X) (u X) in
    let Leq : Equiv (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X))
      ≔ compose_equiv (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ (u X)) (ψ0 X)) (Id GS (ψ0 X) (ψ0 X))
          (ch9w2_concat_right_equiv GS (ψ (u X)) (ψ (u X)) (ψ0 X) (inverse GS (ψ0 X) (ψ (u X)) (β X)))
          (concat_left_equiv GS (ψ0 X) (ψ (u X)) (ψ0 X) (β X)) in
    let ev : Id GS (ψ0 X) (ψ0 X) → ST ≔ gset_path_eval A (ψ0 X) (ψ0 X) (shape A) x0 in
    let M : T1 → Id GS (ψ0 X) (ψ0 X) ≔ t ↦ Leq .map (apψ (tpe .map t)) in
    let Cunits : (p : Id Type X X) → Id ST (ev (M (trunc_unit (suc. zero.) (Id Type X X) p)))
        (trunc_one_to_set_trunc (Id Type X X) (trunc_unit (suc. zero.) (Id Type X X) p))
      ≔ p ↦ calc
          ev (M (trunc_unit (suc. zero.) (Id Type X X) p))
          = ev (Leq .map (apψ (gen X p)))
            by refl ((r ↦ ev (Leq .map (apψ r))) : Id U1 (u X) (u X) → ST)
                 (inverse (Id U1 (u X) (u X)) (gen X p) (tpe .map (trunc_unit (suc. zero.) (Id Type X X) p)) (tu p))
          = set_trunc (Id Type X X) p by outer_simple_compute G U1 u ψ β gen g0 X p
          = trunc_one_to_set_trunc (Id Type X X) (trunc_unit (suc. zero.) (Id Type X X) p)
            by inverse ST (trunc_one_to_set_trunc (Id Type X X) (trunc_unit (suc. zero.) (Id Type X X) p)) (set_trunc (Id Type X X) p)
                 (trunc_one_unit_compare (Id Type X X) p) ∎ in
    let Ceq : Id (T1 → ST) (t ↦ ev (M t)) (trunc_one_to_set_trunc (Id Type X X))
      ≔ trunc_maps_equal (suc. zero.) (Id Type X X) (truncation (suc. zero.) (Id Type X X)) ST
          (set_to_hlevel_two ST (set_trunc_set (Id Type X X))) (t ↦ ev (M t)) (trunc_one_to_set_trunc (Id Type X X)) Cunits in
    let Cequiv : BookIsEquiv T1 ST (t ↦ ev (M t))
      ≔ book_equivalence T1 ST
          (equiv_change_map T1 ST (trunc_one_set_trunc_equiv (Id Type X X)) (t ↦ ev (M t))
            (t ↦ inverse ST (ev (M t)) (trunc_one_to_set_trunc (Id Type X X) t) (happly T1 (_ ↦ ST) (t ↦ ev (M t)) (trunc_one_to_set_trunc (Id Type X X)) Ceq t)))
          .equiv in
    let Mequiv : BookIsEquiv T1 (Id GS (ψ0 X) (ψ0 X)) M
      ≔ ch9w2_equiv_of_embedding_composite T1 (Id GS (ψ0 X) (ψ0 X)) ST M ev
          (gset_path_eval_injective A (ψ0 X) (ψ0 X) (shape A) x0 (outer_simple_eval_transitive G)) Cequiv in
    let Me : Equiv T1 (Id GS (ψ0 X) (ψ0 X)) ≔ native_equivalence T1 (Id GS (ψ0 X) (ψ0 X)) (M, Mequiv) in
    let tinv ≔ equiv_inverse_map T1 (Id U1 (u X) (u X)) tpe in
    book_equivalence (Id U1 (u X) (u X)) (Id GS (ψ (u X)) (ψ (u X)))
      (equiv_change_map (Id U1 (u X) (u X)) (Id GS (ψ (u X)) (ψ (u X)))
        (compose_equiv (Id U1 (u X) (u X)) T1 (Id GS (ψ (u X)) (ψ (u X)))
          (canonical_inverse_equiv T1 (Id U1 (u X) (u X)) tpe)
          (compose_equiv T1 (Id GS (ψ0 X) (ψ0 X)) (Id GS (ψ (u X)) (ψ (u X))) Me
            (canonical_inverse_equiv (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X)) Leq)))
        apψ
        (r ↦ calc
          equiv_inverse_map (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X)) Leq (M (tinv r))
          = equiv_inverse_map (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X)) Leq (Leq .map (apψ r))
            by refl ((s ↦ equiv_inverse_map (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X)) Leq (Leq .map (apψ s)))
                   : Id U1 (u X) (u X) → Id GS (ψ (u X)) (ψ (u X)))
                 (equiv_counit T1 (Id U1 (u X) (u X)) tpe r)
          = apψ r by equiv_retraction (Id GS (ψ (u X)) (ψ (u X))) (Id GS (ψ0 X) (ψ0 X)) Leq (apψ r) ∎))
      .equiv

def outer_simple_ap_equiv (G : Group)
  : BookIsEquiv (Id UniverseOneTrunc (universe_one_trunc_unit (BG G .carrier)) (universe_one_trunc_unit (BG G .carrier)))
      (Id (GSet (group_aut G)) (outer_family G (universe_one_trunc_unit (BG G .carrier))) (outer_family G (universe_one_trunc_unit (BG G .carrier))))
      (map_path UniverseOneTrunc (GSet (group_aut G)) (outer_family G) (universe_one_trunc_unit (BG G .carrier)) (universe_one_trunc_unit (BG G .carrier)))
  ≔ let X ≔ BG G .carrier in
    outer_simple_ap_equiv_gen G UniverseOneTrunc universe_one_trunc_unit (outer_family G) (outer_family_beta G)
      (Y p ↦ trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) Type X Y p)
      (transport_refl Type (z ↦ Id UniverseOneTrunc (universe_one_trunc_unit X) (universe_one_trunc_unit z)) X
        (refl (universe_one_trunc_unit X)))
      (trunc_path_equiv (suc. zero.) Type X X)
      (p ↦ trunc_path_equiv_unit (suc. zero.) Type X X p)

{` cons:simpler-version-Out: Φ is an isomorphism, hence an identification
   of groups Aut_{‖U‖₁}(|BG÷|₁) = Out(G). `}
def outer_simple_iso (G : Group) : IsGroupIso (outer_simple_group G) (outer_aut_group G) (outer_simple_hom G)
  ≔ let X ≔ BG G .carrier in let A ≔ group_aut G in let GS ≔ GSet A in
    let U1 ≔ UniverseOneTrunc in let u ≔ universe_one_trunc_unit in
    let ψ ≔ outer_family G in
    let D ≔ outer_simple_group G in let O ≔ outer_aut_group G in
    let C1 ≔ BG D .carrier in let C2 ≔ BG O .carrier in
    let BΦ ≔ hom_function D O (outer_simple_hom G) in
    let c0 ≔ shape D in
    let cpeS ≔ component_path_equiv U1 (u X) c0 c0 in
    let cpeT ≔ component_path_equiv GS (outer_gset G) (BΦ c0) (BΦ c0) in
    let apΦ ≔ map_path C1 C2 BΦ c0 c0 in
    let ψe : Equiv (Id U1 (u X) (u X)) (Id GS (ψ (u X)) (ψ (u X)))
      ≔ native_equivalence (Id U1 (u X) (u X)) (Id GS (ψ (u X)) (ψ (u X))) (map_path U1 GS ψ (u X) (u X), outer_simple_ap_equiv G) in
    let h : BookIsEquiv (Id C1 c0 c0) (Id C2 (BΦ c0) (BΦ c0)) apΦ
      ≔ book_equivalence (Id C1 c0 c0) (Id C2 (BΦ c0) (BΦ c0))
          (equiv_change_map (Id C1 c0 c0) (Id C2 (BΦ c0) (BΦ c0))
            (compose_equiv (Id C1 c0 c0) (Id U1 (u X) (u X)) (Id C2 (BΦ c0) (BΦ c0)) cpeS
              (compose_equiv (Id U1 (u X) (u X)) (Id GS (ψ (u X)) (ψ (u X))) (Id C2 (BΦ c0) (BΦ c0)) ψe
                (canonical_inverse_equiv (Id C2 (BΦ c0) (BΦ c0)) (Id GS (ψ (u X)) (ψ (u X))) cpeT)))
            apΦ (r ↦ equiv_retraction (Id C2 (BΦ c0) (BΦ c0)) (Id GS (ψ (u X)) (ψ (u X))) cpeT (apΦ r))) .equiv in
    connected_map_equiv_from_loops native_truncation C1 C2 BΦ (bg_connected D) (bg_connected O) c0 h .equiv

def outer_simple_path (G : Group) : Id Group (outer_simple_group G) (outer_aut_group G)
  ≔ group_path_from_iso (outer_simple_group G) (outer_aut_group G) (outer_simple_hom G, outer_simple_iso G)
