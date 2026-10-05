export "901-kernels-cokernels-images"

{` Chapter 9 (subgroups.tex), sec:actiononsub: the G-sets Mono(G) and
   Sub(G) (the definitions at lines 1200 and 1282), conjugation
   (rem:action-Mono(G)), the action on Sub(G), the map of G-sets
   E : Mono(G) → Sub(G) (definition at line 1295) and rem:typeofsubgpstrivifab.

   group_at G z (module 437) is mkgroup(BG÷, z); group_at G (shape G) ≡ G. `}

{` The definition at line 1200: Mono(G) : BG → Set, z ↦ Mono(mkgroup(BG÷, z)). `}
def monos_gset (G : Group) : GSet G ≔ z ↦ (GroupMonos (group_at G z), group_monos_set (group_at G z))

{` "The underlying set Mono(G)(sh_G) is definitionally the set Mono(G)." `}
def monos_gset_underlying (G : Group) : Id Type (gset_underlying G (monos_gset G)) (GroupMonos G)
  ≔ refl (GroupMonos G)

{` rem:action-Mono(G). Moving the shape along p : z = z' is the
   isomorphism mkgroup(id_BG, p⁻¹) : mkgroup(BG÷, z) → mkgroup(BG÷, z')
   (for z ≡ sh_G this is conj_hom of module 437). `}
def group_at_move (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z')
  : GroupHom (group_at G z) (group_at G z')
  ≔ mkhom (group_at G z) (group_at G z') (identity (BG G .carrier), inverse (BG G .carrier) z z' p)

def group_at_move_shape (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : Id (GroupHom G (group_at G y)) (group_at_move G (shape G) y p) (conj_hom G y p)
  ≔ refl (conj_hom G y p)

{` The footnote of rem:action-Mono(G): Ω(id_BG, p⁻¹) is g ↦ p g p⁻¹
   (loop_conjugate: first p⁻¹, then g, then p in concatenation order). `}
def group_at_move_usym (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (g : Id (BG G .carrier) z z)
  : Id (Id (BG G .carrier) z' z') (usym_hom (group_at G z) (group_at G z') (group_at_move G z z' p) g)
      (loop_conjugate (BG G .carrier) z z' p g)
  ≔ let A ≔ BG G .carrier in
    refl (concat A z' z z' (inverse A z z' p)) (refl (concat A z z z' g) (inverse_inverse A z z' p))

{` Post-composing a monomorphism with group_at_move gives a monomorphism
   (the classifying map is unchanged, so it is still a covering). `}
def group_at_move_mono (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (m : GroupMonos (group_at G z))
  : IsGroupMono (m .fst) (group_at G z')
      (group_hom_compose (m .fst) (group_at G z) (group_at G z') (m .snd .fst) (group_at_move G z z' p))
  ≔ covering_group_mono (m .fst) (group_at G z')
      (group_hom_compose (m .fst) (group_at G z) (group_at G z') (m .snd .fst) (group_at_move G z z' p))
      (group_mono_covering (m .fst) (group_at G z) (m .snd .fst) (m .snd .snd))

def monos_conjugate (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (m : GroupMonos (group_at G z))
  : GroupMonos (group_at G z')
  ≔ (m .fst, (group_hom_compose (m .fst) (group_at G z) (group_at G z') (m .snd .fst) (group_at_move G z z' p),
      group_at_move_mono G z z' p m))

{` Paths in Mono(K) with fixed source group from paths of homomorphisms. `}
def group_monos_path_same (K H : Group) (f f' : GroupHom H K) (m : IsGroupMono H K f) (m' : IsGroupMono H K f')
  (e : Id (GroupHom H K) f f') : Id (GroupMonos K) (H, (f, m)) (H, (f', m'))
  ≔ refl ((u ↦ (H, u)) : Σ (GroupHom H K) (IsGroupMono H K) → GroupMonos K)
      (subtype_equal (GroupHom H K) (IsGroupMono H K) (is_group_mono_prop H K) (f, m) (f', m') e)

def group_at_move_refl (G : Group) (z : BG G .carrier) (H : Group) (f : GroupHom H (group_at G z))
  : Id (GroupHom H (group_at G z)) (group_hom_compose H (group_at G z) (group_at G z) f (group_at_move G z z (refl z))) f
  ≔ let A ≔ BG G .carrier in let b ≔ hom_function H (group_at G z) f (shape H) in
    let q ≔ hom_point H (group_at G z) f in
    ch9_hom_path H (group_at G z) (group_hom_compose H (group_at G z) (group_at G z) f (group_at_move G z z (refl z))) f
      ((x ↦ refl (hom_function H (group_at G z) f x)),
       calc
         concat A z b b (concat A z z b (inverse A z z (refl z)) q) (refl b)
         = concat A z z b (inverse A z z (refl z)) q by concat_p1 A z b (concat A z z b (inverse A z z (refl z)) q)
         = concat A z z b (refl z) q by refl ((r ↦ concat A z z b r q) : Id A z z → Id A z b) (inverse_refl A z)
         = q by concat_1p A z b q ∎)

{` rem:action-Mono(G): the action of the G-set Mono(G) along p maps (H, f)
   to (H, mkgroup(id_BG, p⁻¹) ∘ f) ("conjugation"). `}
def monos_gset_act (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (m : GroupMonos (group_at G z))
  : Id (GroupMonos (group_at G z')) (gset_act G (monos_gset G) z z' p m) (monos_conjugate G z z' p m)
  ≔ let A ≔ BG G .carrier in
    J A z (z' p ↦ Id (GroupMonos (group_at G z')) (gset_act G (monos_gset G) z z' p m) (monos_conjugate G z z' p m))
      (concat (GroupMonos (group_at G z)) (gset_act G (monos_gset G) z z (refl z) m) m (monos_conjugate G z z (refl z) m)
        (gset_act_refl G (monos_gset G) z m)
        (inverse (GroupMonos (group_at G z)) (monos_conjugate G z z (refl z) m) m
          (group_monos_path_same (group_at G z) (m .fst)
            (group_hom_compose (m .fst) (group_at G z) (group_at G z) (m .snd .fst) (group_at_move G z z (refl z)))
            (m .snd .fst) (group_at_move_mono G z z (refl z) m) (m .snd .snd)
            (group_at_move_refl G z (m .fst) (m .snd .fst)))))
      z' p

{` At the shape: g · (H, f) = (H, conj^g ∘ f), conj^g = conj_hom G (shape G) g. `}
def monos_gset_usym_act (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (GroupMonos G) (gset_usym_act G (monos_gset G) g m) (monos_conjugate G (shape G) (shape G) g m)
  ≔ monos_gset_act G (shape G) (shape G) g m

{` The definition at line 1282: Sub(G) : BG → Set, z ↦ Sub(mkgroup(BG÷, z)). `}
def subgroups_gset (G : Group) : GSet G ≔ z ↦ (Subgroups (group_at G z), subgroups_set (group_at G z))

def subgroups_gset_underlying (G : Group) : Id Type (gset_underlying G (subgroups_gset G)) (Subgroups G)
  ≔ refl (Subgroups G)

{` "Sub(G)(z) unpacks as Σ_{X:BG→Set} X(z) × istrans(X)": the G-set and
   the point are literally X and X(z); transitivity relative to the shape z
   is equivalent to transitivity relative to sh_G (both are connectedness of
   the same action type). `}
def subgroup_transitive_move (G : Group) (z z' : BG G .carrier) (X : GSet G) (t : IsTransitive (group_at G z) X)
  : IsTransitive (group_at G z') X
  ≔ connected_action_type_transitive (group_at G z') X (transitive_action_type_connected (group_at G z) X t)

def subgroups_at_transitive_equiv (G : Group) (z : BG G .carrier) (X : GSet G)
  : Equiv (IsTransitive (group_at G z) X) (IsTransitive G X)
  ≔ iff_equiv (IsTransitive (group_at G z) X) (IsTransitive G X)
      (is_transitive_prop (group_at G z) X) (is_transitive_prop G X)
      (subgroup_transitive_move G z (shape G) X) (subgroup_transitive_move G (shape G) z X)

{` "The action of Sub(G) applied to (X, x) does nothing with X and applies
   the action of X to x." `}
def subgroups_move (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (S : Subgroups (group_at G z))
  : Subgroups (group_at G z')
  ≔ (S .gset, gset_act G (S .gset) z z' p (S .point), subgroup_transitive_move G z z' (S .gset) (S .transitive))

def subgroups_gset_act (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (S : Subgroups (group_at G z))
  : Id (Subgroups (group_at G z')) (gset_act G (subgroups_gset G) z z' p S) (subgroups_move G z z' p S)
  ≔ let A ≔ BG G .carrier in
    J A z (z' p ↦ Id (Subgroups (group_at G z')) (gset_act G (subgroups_gset G) z z' p S) (subgroups_move G z z' p S))
      (concat (Subgroups (group_at G z)) (gset_act G (subgroups_gset G) z z (refl z) S) S (subgroups_move G z z (refl z) S)
        (gset_act_refl G (subgroups_gset G) z S)
        (subgroup_path (group_at G z) S (subgroups_move G z z (refl z) S)
          (refl ((y ↦ (S .gset, y)) : S .gset z .fst → PointedGSet (group_at G z))
            (inverse (S .gset z .fst) (gset_act G (S .gset) z z (refl z) (S .point)) (S .point)
              (gset_act_refl G (S .gset) z (S .point))))))
      z' p

def subgroups_gset_usym_act (G : Group) (g : USym G) (S : Subgroups G)
  : Id (Subgroups G) (gset_usym_act G (subgroups_gset G) g S) (subgroups_move G (shape G) (shape G) g S)
  ≔ subgroups_gset_act G (shape G) (shape G) g S

{` The definition at line 1295: E : Hom_G(Mono(G), Sub(G)),
   E_z(H, f) ≔ (Bf⁻¹, (sh_H, Bf_pt)), i.e. chapter 5's E for the group
   mkgroup(BG÷, z); E_{sh_G} ≡ E. Each E_z is an equivalence (lem:SubG=MonoG),
   so E is an equivalence of G-sets. `}
def monos_to_subgroups (G : Group) : GSetHom G (monos_gset G) (subgroups_gset G)
  ≔ z ↦ mono_to_subgroup (group_at G z)

def monos_to_subgroups_shape (G : Group) (m : GroupMonos G)
  : Id (Subgroups G) (monos_to_subgroups G (shape G) m) (mono_to_subgroup G m)
  ≔ refl (mono_to_subgroup G m)

def monos_subgroups_equiv (G : Group) : Equiv (GroupMonos G) (Subgroups G)
  ≔ quasi_inverse_equiv (GroupMonos G) (Subgroups G) (mono_to_subgroup G) (subgroup_to_mono G)
      (mono_subgroup_roundtrip G) (subgroup_mono_roundtrip G)

def monos_to_subgroups_equiv (G : Group) (z : BG G .carrier)
  : Equiv (monos_gset G z .fst) (subgroups_gset G z .fst)
  ≔ monos_subgroups_equiv (group_at G z)

def monos_subgroups_gset_path (G : Group) : Id (GSet G) (monos_gset G) (subgroups_gset G)
  ≔ gset_path_from_equivs G (monos_gset G) (subgroups_gset G) (monos_to_subgroups_equiv G)
