export "541-cayley"

{` Chapter 5, sec:homotor: restriction f^*, induction f_! and coinduction f_*
   of G-sets (def:restrictandinduce, rem:coinduced-Hset), the adjunctions
   (xca:adjunction-_!-^*, xca:adjunction-^*-_*), xca:why-setTrunc_f_!,
   images and preimages of subtypes (rem:^*-_!-as-(pre)image,
   rem:coinduced-subset) and induced torsors (con:inducedtorsor). `}

{` xca:adjunction-_!-^*, second part: Hom_H(f_!X, Y) ≃ Hom_G(X, f^*Y)
   (Y lands in sets; curry; exchange the products; substitute away w). `}
def induce_restrict_adjunction (G H : Group) (f : GroupHom G H) (X : GSet G) (Y : GSet H)
  : Equiv (GSetHom H (gset_induce G H f X) Y) (GSetHom G X (gset_restrict G H f Y))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let Bf ≔ hom_function G H f in
    let S : B → Type ≔ w ↦ GSetInducedSum G H f X w in
    let T1 ≔ (w : B) → SetTrunc (S w) → Y w .fst in
    let T2 ≔ (w : B) → S w → Y w .fst in
    let T3 ≔ (w : B) (z : A) (p : Id B (Bf z) w) → X z .fst → Y w .fst in
    let T4 ≔ (z : A) (w : B) (p : Id B (Bf z) w) → X z .fst → Y w .fst in
    let T5 ≔ (z : A) → X z .fst → Y (Bf z) .fst in
    compose_equiv T1 T2 T5
      (pi_equiv B (w ↦ SetTrunc (S w) → Y w .fst) (w ↦ S w → Y w .fst)
        (w ↦ native_equivalence (SetTrunc (S w) → Y w .fst) (S w → Y w .fst)
          (set_trunc_universal_property (S w) (Y w .fst) (Y w .snd))))
      (compose_equiv T2 T3 T5
        (quasi_inverse_equiv T2 T3 (k w z p x ↦ k w (z, (p, x))) (k w s ↦ k w (s .fst) (s .snd .fst) (s .snd .snd))
          (k ↦ refl k) (k ↦ refl k))
        (compose_equiv T3 T4 T5
          (quasi_inverse_equiv T3 T4 (k z w p x ↦ k w z p x) (k w z p x ↦ k z w p x) (k ↦ refl k) (k ↦ refl k))
          (pi_equiv A (z ↦ (w : B) (p : Id B (Bf z) w) → X z .fst → Y w .fst) (z ↦ X z .fst → Y (Bf z) .fst)
            (z ↦ substitute_away_equiv B (Bf z) (w _ ↦ X z .fst → Y w .fst)))))

{` xca:adjunction-^*-_*: Hom_G(f^*Y, X) ≃ Hom_H(Y, f_*X). `}
def restrict_coinduce_adjunction (G H : Group) (f : GroupHom G H) (X : GSet G) (Y : GSet H)
  : Equiv (GSetHom G (gset_restrict G H f Y) X) (GSetHom H Y (gset_coinduce G H f X))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let Bf ≔ hom_function G H f in
    let T1 ≔ (z : A) → Y (Bf z) .fst → X z .fst in
    let T2 ≔ (z : A) (w : B) (p : Id B (Bf z) w) → Y w .fst → X z .fst in
    let T3 ≔ (w : B) → Y w .fst → (z : A) → Id B (Bf z) w → X z .fst in
    compose_equiv T1 T2 T3
      (canonical_inverse_equiv T2 T1
        (pi_equiv A (z ↦ (w : B) (p : Id B (Bf z) w) → Y w .fst → X z .fst) (z ↦ Y (Bf z) .fst → X z .fst)
          (z ↦ substitute_away_equiv B (Bf z) (w _ ↦ Y w .fst → X z .fst))))
      (quasi_inverse_equiv T2 T3 (k w y z p ↦ k z w p y) (k z w p y ↦ k w y z p) (k ↦ refl k) (k ↦ refl k))

{` xca:adjunction-_!-^*, first part: for an isomorphism f, f_!X ≃ X ∘ Bf⁻¹,
   for any equivalence of types (equivalence induction). `}
def induced_sum_equivalence (A : Type) (X : A → SetTypes) (B : Type) (e : Equiv A B) (w : B)
  : Equiv (SetTrunc (Σ A (z ↦ Product (Id B (e .map z) w) (X z .fst)))) (X (equiv_inverse_map A B e w) .fst)
  ≔ equivalence_induction A
      (B e ↦ (w : B) → Equiv (SetTrunc (Σ A (z ↦ Product (Id B (e .map z) w) (X z .fst)))) (X (equiv_inverse_map A B e w) .fst))
      (w ↦ compose_equiv (SetTrunc (Σ A (z ↦ Product (Id A z w) (X z .fst)))) (Σ A (z ↦ Product (Id A z w) (X z .fst))) (X w .fst)
        (set_trunc_of_set_equiv (Σ A (z ↦ Product (Id A z w) (X z .fst)))
          (hlevel_two_to_set (Σ A (z ↦ Product (Id A z w) (X z .fst)))
            (hlevel_equiv (suc. (suc. zero.)) (X w .fst) (Σ A (z ↦ Product (Id A z w) (X z .fst)))
              (canonical_inverse_equiv (Σ A (z ↦ Product (Id A z w) (X z .fst))) (X w .fst)
                (compose_equiv (Σ A (z ↦ Product (Id A z w) (X z .fst))) (Σ A (z ↦ Product (Id A w z) (X z .fst))) (X w .fst)
                  (family_equiv A (z ↦ Product (Id A z w) (X z .fst)) (z ↦ Product (Id A w z) (X z .fst))
                    (z ↦ quasi_inverse_equiv (Product (Id A z w) (X z .fst)) (Product (Id A w z) (X z .fst))
                      (u ↦ (inverse A z w (u .fst), u .snd)) (u ↦ (inverse A w z (u .fst), u .snd))
                      (u ↦ (inverse_inverse A z w (u .fst), refl (u .snd)))
                      (u ↦ (inverse_inverse A w z (u .fst), refl (u .snd)))))
                  (contract_away_simple A w (z ↦ X z .fst))))
              (set_to_hlevel_two (X w .fst) (X w .snd)))))
        (compose_equiv (Σ A (z ↦ Product (Id A z w) (X z .fst))) (Σ A (z ↦ Product (Id A w z) (X z .fst))) (X w .fst)
          (family_equiv A (z ↦ Product (Id A z w) (X z .fst)) (z ↦ Product (Id A w z) (X z .fst))
            (z ↦ quasi_inverse_equiv (Product (Id A z w) (X z .fst)) (Product (Id A w z) (X z .fst))
              (u ↦ (inverse A z w (u .fst), u .snd)) (u ↦ (inverse A w z (u .fst), u .snd))
              (u ↦ (inverse_inverse A z w (u .fst), refl (u .snd)))
              (u ↦ (inverse_inverse A w z (u .fst), refl (u .snd)))))
          (contract_away_simple A w (z ↦ X z .fst))))
      B e w

def induce_iso_equiv (G H : Group) (f : GroupHom G H) (hf : IsGroupIso G H f) (X : GSet G) (w : BG H .carrier)
  : Equiv (gset_induce G H f X w .fst)
      (X (equiv_inverse_map (BG G .carrier) (BG H .carrier)
          (native_equivalence (BG G .carrier) (BG H .carrier) (hom_function G H f, hf)) w) .fst)
  ≔ induced_sum_equivalence (BG G .carrier) X (BG H .carrier)
      (native_equivalence (BG G .carrier) (BG H .carrier) (hom_function G H f, hf)) w

def induce_iso_path (G H : Group) (f : GroupHom G H) (hf : IsGroupIso G H f) (X : GSet G)
  : Id (GSet H) (gset_induce G H f X)
      (w ↦ X (equiv_inverse_map (BG G .carrier) (BG H .carrier)
          (native_equivalence (BG G .carrier) (BG H .carrier) (hom_function G H f, hf)) w))
  ≔ gset_path_from_equivs H (gset_induce G H f X)
      (w ↦ X (equiv_inverse_map (BG G .carrier) (BG H .carrier)
          (native_equivalence (BG G .carrier) (BG H .carrier) (hom_function G H f, hf)) w))
      (induce_iso_equiv G H f hf X)

{` xca:why-setTrunc_f_!: for G = Z (any circle), H = 1, f : Z → 1 and X the
   constant G-set 1, the untruncated value Σ_{z:S¹} (Bf(z) = w) × 1 is not a set
   (it is equivalent to the circle). `}
def why_set_trunc_circle_equiv (C : CircleSignature)
  : Equiv (C .carrier)
      (GSetInducedSum (circle_group C) unit_group (group_hom_to_unit (circle_group C))
        (gset_trivial (circle_group C) (Unit, unit_set)) star.)
  ≔ let S ≔ GSetInducedSum (circle_group C) unit_group (group_hom_to_unit (circle_group C))
        (gset_trivial (circle_group C) (Unit, unit_set)) star. in
    quasi_inverse_equiv (C .carrier) S (z ↦ (z, (refl (star. : Unit), star.))) (s ↦ s .fst)
      (z ↦ refl z)
      (s ↦ (refl (s .fst), (unit_set star. star. (refl (star. : Unit)) (s .snd .fst), unit_prop star. (s .snd .snd))))

def why_set_trunc_not_set (C : CircleSignature)
  (h : isSet (GSetInducedSum (circle_group C) unit_group (group_hom_to_unit (circle_group C))
        (gset_trivial (circle_group C) (Unit, unit_set)) star.)) : Empty
  ≔ let S ≔ GSetInducedSum (circle_group C) unit_group (group_hom_to_unit (circle_group C))
        (gset_trivial (circle_group C) (Unit, unit_set)) star. in
    circle_not_set C
      (hlevel_two_to_set (C .carrier)
        (hlevel_equiv (suc. (suc. zero.)) S (C .carrier)
          (canonical_inverse_equiv (C .carrier) S (why_set_trunc_circle_equiv C)) (set_to_hlevel_two S h)))

{` ft:f_!X(w)-orbitset: f_!X(w) is the set truncation of the action type of
   the G-set z ↦ (Bf(z) = w) × X(z), whose underlying set is P_H(w) × X(sh_G)
   (composing with Bf_pt). The identification of a set truncation of an action
   type with the set of orbits is lem:X/G=setTruncX_hG. `}
def induced_sum_gset (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier) : GSet G
  ≔ z ↦ (Product (Id (BG H .carrier) (hom_function G H f z) w) (X z .fst),
      product_set (Id (BG H .carrier) (hom_function G H f z) w) (X z .fst)
        (bg_groupoid H (hom_function G H f z) w) (X z .snd))

def induce_as_set_trunc (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier)
  : Id Type (gset_induce G H f X w .fst) (SetTrunc (ActionType G (induced_sum_gset G H f X w)))
  ≔ refl (gset_induce G H f X w .fst)

def ch5_concat_inverse_cancel (B : Type) (x y z : B) (p : Id B x y) (v : Id B x z)
  : Id (Id B x z) (concat B x y z p (concat B y x z (inverse B x y p) v)) v
  ≔ J B x (y p ↦ Id (Id B x z) (concat B x y z p (concat B y x z (inverse B x y p) v)) v)
      (concat (Id B x z) (concat B x x z (refl x) (concat B x x z (inverse B x x (refl x)) v))
        (concat B x x z (inverse B x x (refl x)) v) v
        (concat_1p B x z (concat B x x z (inverse B x x (refl x)) v))
        (inverse_refl_concat B x z v))
      y p

def induced_sum_underlying_equiv (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier)
  : Equiv (gset_underlying G (induced_sum_gset G H f X w)) (Product (principal_gset H w .fst) (gset_underlying G X))
  ≔ let B ≔ BG H .carrier in
    let b ≔ hom_function G H f (shape G) in
    let p ≔ hom_point G H f in
    quasi_inverse_equiv (Product (Id B b w) (gset_underlying G X)) (Product (Id B (shape H) w) (gset_underlying G X))
      (u ↦ (concat B (shape H) b w p (u .fst), u .snd))
      (u ↦ (concat B b (shape H) w (inverse B (shape H) b p) (u .fst), u .snd))
      (u ↦ (concat_left_inverse B (shape H) b w p (u .fst), refl (u .snd)))
      (u ↦ (ch5_concat_inverse_cancel B (shape H) b w p (u .fst), refl (u .snd)))

{` rem:coinduced-Hset, footnote: f_*X(w) is the set of invariant maps of the
   G-set z ↦ ((Bf(z) = w) → X(z)). `}
def coinduced_invariant_maps (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier)
  : Id Type (gset_coinduce G H f X w .fst)
      (InvariantMaps G (z ↦ (Id (BG H .carrier) (hom_function G H f z) w → X z .fst,
        pi_set (Id (BG H .carrier) (hom_function G H f z) w) (_ ↦ X z .fst) (_ ↦ X z .snd))))
  ≔ refl (gset_coinduce G H f X w .fst)

{` The set truncation of a type equivalent to a set. `}
def ch5_set_trunc_equiv (S T : Type) (hT : isSet T) (e : Equiv S T) : Equiv (SetTrunc S) T
  ≔ compose_equiv (SetTrunc S) S T
      (set_trunc_of_set_equiv S
        (hlevel_two_to_set S
          (hlevel_equiv (suc. (suc. zero.)) T S (canonical_inverse_equiv S T e) (set_to_hlevel_two T hT))))
      e

{` con:inducedtorsor. Contracting away z gives η_w : f_!P^G_x(w) ≃ (Bf(x) = w),
   hence η : f_!P^G_x = P^H_{Bf(x)}; with π = ap_{P^H}(Bf_pt) : P_H = P^H_{Bf(sh_G)}
   we get η⁻¹π : P_H = f_!P_G (π first), f_! maps torsors to torsors, and
   f_! : Torsor_G →* Torsor_H with f_! ∘ P^G_- = P^H_- ∘ Bf. `}
def induced_paths_equiv (G H : Group) (f : GroupHom G H) (x : BG G .carrier) (w : BG H .carrier)
  : Equiv (gset_induce G H f (gset_paths G x) w .fst) (Id (BG H .carrier) (hom_function G H f x) w)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let Bf ≔ hom_function G H f in
    ch5_set_trunc_equiv (GSetInducedSum G H f (gset_paths G x) w) (Id B (Bf x) w) (bg_groupoid H (Bf x) w)
      (compose_equiv (Σ A (z ↦ Product (Id B (Bf z) w) (Id A x z))) (Σ A (z ↦ Product (Id A x z) (Id B (Bf z) w)))
        (Id B (Bf x) w)
        (family_equiv A (z ↦ Product (Id B (Bf z) w) (Id A x z)) (z ↦ Product (Id A x z) (Id B (Bf z) w))
          (z ↦ product_swap_equiv (Id B (Bf z) w) (Id A x z)))
        (contract_away_simple A x (z ↦ Id B (Bf z) w)))

def induced_paths_path (G H : Group) (f : GroupHom G H) (x : BG G .carrier)
  : Id (GSet H) (gset_induce G H f (gset_paths G x)) (gset_paths H (hom_function G H f x))
  ≔ gset_path_from_equivs H (gset_induce G H f (gset_paths G x)) (gset_paths H (hom_function G H f x))
      (w ↦ induced_paths_equiv G H f x w)

def induced_principal_path (G H : Group) (f : GroupHom G H)
  : Id (GSet H) (principal_gset H) (gset_induce G H f (principal_gset G))
  ≔ let B ≔ BG H .carrier in
    concat (GSet H) (principal_gset H) (gset_paths H (hom_function G H f (shape G))) (gset_induce G H f (principal_gset G))
      (map_path B (GSet H) (gset_paths H) (shape H) (hom_function G H f (shape G)) (hom_point G H f))
      (inverse (GSet H) (gset_induce G H f (principal_gset G)) (gset_paths H (hom_function G H f (shape G)))
        (induced_paths_path G H f (shape G)))

def induced_torsor (G H : Group) (f : GroupHom G H) (T : Torsors G) : Torsors H
  ≔ (gset_induce G H f (T .fst),
     mere_rec (Id (GSet G) (principal_gset G) (T .fst)) (Mere (Id (GSet H) (principal_gset H) (gset_induce G H f (T .fst))))
       (mere_isprop (Id (GSet H) (principal_gset H) (gset_induce G H f (T .fst))))
       (p ↦ mere (Id (GSet H) (principal_gset H) (gset_induce G H f (T .fst)))
         (concat (GSet H) (principal_gset H) (gset_induce G H f (principal_gset G)) (gset_induce G H f (T .fst))
           (induced_principal_path G H f)
           (map_path (GSet G) (GSet H) (gset_induce G H f) (principal_gset G) (T .fst) p)))
       (T .snd))

def induced_torsor_pointed (G H : Group) (f : GroupHom G H) : BookPointedMap (torsors_pointed G) (torsors_pointed H)
  ≔ (induced_torsor G H f,
     equiv_inverse_map (Id (Torsors H) (principal_torsor H) (induced_torsor G H f (principal_torsor G)))
       (Id (GSet H) (principal_gset H) (gset_induce G H f (principal_gset G)))
       (torsors_path_equiv H (principal_torsor H) (induced_torsor G H f (principal_torsor G)))
       (induced_principal_path G H f))

def induced_torsor_naturality (G H : Group) (f : GroupHom G H)
  : Id (BG G .carrier → Torsors H) (z ↦ induced_torsor G H f (bg_to_torsors G z))
      (z ↦ bg_to_torsors H (hom_function G H f z))
  ≔ funext (BG G .carrier) (_ ↦ Torsors H) (z ↦ induced_torsor G H f (bg_to_torsors G z))
      (z ↦ bg_to_torsors H (hom_function G H f z))
      (z ↦ equiv_inverse_map (Id (Torsors H) (induced_torsor G H f (bg_to_torsors G z)) (bg_to_torsors H (hom_function G H f z)))
        (Id (GSet H) (gset_induce G H f (gset_paths G z)) (gset_paths H (hom_function G H f z)))
        (torsors_path_equiv H (induced_torsor G H f (bg_to_torsors G z)) (bg_to_torsors H (hom_function G H f z)))
        (induced_paths_path G H f z))
