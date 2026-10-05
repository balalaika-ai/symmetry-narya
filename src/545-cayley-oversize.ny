export "544-restriction-injective"
export "403-abstract-groups"

{` Chapter 5, rem:CayleyOversize and xca:PP-fixed-permutations: the G-set
   PP(z) ≔ (P_G(z) = P_G(z)), its invariant maps (= identifications P_G = P_G),
   the fixed permutations of USym G, and evaluation at refl. As printed,
   xca:PP-fixed-permutations asks for evaluation at refl to be an abstract
   isomorphism from the group of fixed permutations (under composition) to
   abstr(G); it is a bijective ANTI-homomorphism (ev(π∘π') = ev(π')·ev(π)),
   so the claim fails for every non-abelian G (counterexample Σ_3 below); the
   corrected isomorphism is π ↦ ev(π)⁻¹. `}

def cayley_pp_gset (G : Group) : GSet G
  ≔ z ↦ (Id SetTypes (principal_gset G z) (principal_gset G z), sets_groupoid (principal_gset G z) (principal_gset G z))

{` By function extensionality, P_G = P_G is equivalent to Π_z PP(z), the type
   of invariant maps of PP; an invariant map is determined by its value at sh_G
   (lem:fixpts-are-fixed (i)). `}
def cayley_pp_invariant_equiv (G : Group)
  : Equiv (Id (GSet G) (principal_gset G) (principal_gset G)) (InvariantMaps G (cayley_pp_gset G))
  ≔ function_extensionality (BG G .carrier) (_ ↦ SetTypes) (principal_gset G) (principal_gset G)

def cayley_pp_invariant_reflects (G : Group) (h h' : InvariantMaps G (cayley_pp_gset G))
  (e : Id (Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G))) (h (shape G)) (h' (shape G)))
  : Id (InvariantMaps G (cayley_pp_gset G)) h h'
  ≔ connected_sections_agree (BG G .carrier) (bg_connected G) (cayley_pp_gset G) h h' (shape G) e

{` The permutation underlying an identification of sets, and extensionality. `}
def set_path_permutation (A B : SetTypes) (r : Id SetTypes A B) : A .fst → B .fst ≔ r .fst .trr

def set_path_ext (A B : SetTypes) (r r' : Id SetTypes A B)
  (h : (x : A .fst) → Id (B .fst) (set_path_permutation A B r x) (set_path_permutation A B r' x))
  : Id (Id SetTypes A B) r r'
  ≔ let e ≔ compose_equiv (Id SetTypes A B) (Id Type (A .fst) (B .fst)) (Equiv (A .fst) (B .fst))
      (subtype_path_equiv Type isSet isset_isprop A B) (transport_univalence_equiv (A .fst) (B .fst)) in
    equivalence_injective (Id SetTypes A B) (Equiv (A .fst) (B .fst)) e r r'
      (equiv_path (A .fst) (B .fst) (e .map r) (e .map r')
        (funext (A .fst) (_ ↦ B .fst) (set_path_permutation A B r) (set_path_permutation A B r') h))

{` How PP acts: (g · ρ)(x) = g · ρ(g⁻¹ · x) (the book's commented solution
   PP(p)(q) = p · q(p⁻¹ · −)). `}
def cayley_pp_transport (G : Group) (z : BG G .carrier) (g : Id (BG G .carrier) (shape G) z)
  (r : Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G))) (x : principal_gset G z .fst)
  : Id (principal_gset G z .fst)
      (set_path_permutation (principal_gset G z) (principal_gset G z)
        (transport (BG G .carrier) (w ↦ Id SetTypes (principal_gset G w) (principal_gset G w)) (shape G) z g r) x)
      (gset_act G (principal_gset G) (shape G) z g
        (set_path_permutation (principal_gset G (shape G)) (principal_gset G (shape G)) r
          (gset_act G (principal_gset G) z (shape G) (inverse (BG G .carrier) (shape G) z g) x)))
  ≔ let B ≔ BG G .carrier in
    let P ≔ principal_gset G in
    let sh ≔ shape G in
    let F : B → Type ≔ w ↦ Id SetTypes (P w) (P w) in
    let perm ≔ set_path_permutation (P sh) (P sh) in
    J B sh
      (z g ↦ (x : P z .fst) → Id (P z .fst)
        (set_path_permutation (P z) (P z) (transport B F sh z g r) x)
        (gset_act G P sh z g (perm r (gset_act G P z sh (inverse B sh z g) x))))
      (x ↦ calc
        perm (transport B F sh sh (refl sh) r) x
        = perm r x by map_path (F sh) (USym G) (s ↦ perm s x) (transport B F sh sh (refl sh) r) r (transport_refl B F sh r)
        = perm r (gset_act G P sh sh (refl sh) x)
          by map_path (USym G) (USym G) (perm r) x (gset_act G P sh sh (refl sh) x)
               (inverse (USym G) (gset_act G P sh sh (refl sh) x) x (gset_act_refl G P sh x))
        = perm r (gset_act G P sh sh (inverse B sh sh (refl sh)) x)
          by map_path (Id B sh sh) (USym G) (q ↦ perm r (gset_act G P sh sh q x)) (refl sh) (inverse B sh sh (refl sh))
               (inverse (Id B sh sh) (inverse B sh sh (refl sh)) (refl sh) (inverse_refl B sh))
        = gset_act G P sh sh (refl sh) (perm r (gset_act G P sh sh (inverse B sh sh (refl sh)) x))
          by inverse (USym G) (gset_act G P sh sh (refl sh) (perm r (gset_act G P sh sh (inverse B sh sh (refl sh)) x)))
               (perm r (gset_act G P sh sh (inverse B sh sh (refl sh)) x))
               (gset_act_refl G P sh (perm r (gset_act G P sh sh (inverse B sh sh (refl sh)) x))) ∎)
      z g x

{` Fixed permutations: π(g g') = g π(g') for all g, g'. `}
def IsCayleyFixed (G : Group) (p : USym G → USym G) : Type
  ≔ (g g' : USym G) → Id (USym G) (p (usym_mul G g g')) (usym_mul G g (p g'))

def is_cayley_fixed_prop (G : Group) (p : USym G → USym G) : isProp (IsCayleyFixed G p)
  ≔ pi_prop (USym G) (g ↦ (g' : USym G) → Id (USym G) (p (usym_mul G g g')) (usym_mul G g (p g')))
      (g ↦ pi_prop (USym G) (g' ↦ Id (USym G) (p (usym_mul G g g')) (usym_mul G g (p g')))
        (g' ↦ usym_set G (p (usym_mul G g g')) (usym_mul G g (p g'))))

def ch5_usym_inv_mul_cancel (G : Group) (g g' : USym G)
  : Id (USym G) (usym_mul G (usym_inv G g) (usym_mul G g g')) g'
  ≔ let B ≔ BG G .carrier in
    let sh ≔ shape G in
    calc
      concat B sh sh sh (concat B sh sh sh g' g) (inverse B sh sh g)
      = concat B sh sh sh g' (concat B sh sh sh g (inverse B sh sh g)) by concat_assoc B sh sh sh sh g' g (inverse B sh sh g)
      = concat B sh sh sh g' (refl sh)
        by map_path (USym G) (USym G) (concat B sh sh sh g') (concat B sh sh sh g (inverse B sh sh g)) (refl sh)
             (concat_inverse_right B sh sh g)
      = g' by concat_p1 B sh sh g' ∎

def ch5_usym_mul_inv_cancel (G : Group) (g x : USym G)
  : Id (USym G) (usym_mul G g (usym_mul G (usym_inv G g) x)) x
  ≔ ch5_concat_cancel_inverse_right (BG G .carrier) (shape G) (shape G) (shape G) x g

{` xca:PP-fixed-permutations, first part: ρ : PP(sh_G) is fixed by every g iff
   its permutation π satisfies π(g g') = g π(g'). `}
def CayleyPPFixed (G : Group) (r : Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G))) : Type
  ≔ (g : USym G) → Id (Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G)))
      (gset_usym_act G (cayley_pp_gset G) g r) r

def cayley_pp_fixed_to (G : Group) (r : Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G)))
  (fx : CayleyPPFixed G r) : IsCayleyFixed G (set_path_permutation (principal_gset G (shape G)) (principal_gset G (shape G)) r)
  ≔ let S ≔ principal_gset G (shape G) in
    let perm ≔ set_path_permutation S S in
    g g' ↦ calc
      perm r (usym_mul G g g')
      = perm (gset_usym_act G (cayley_pp_gset G) g r) (usym_mul G g g')
        by inverse (USym G) (perm (gset_usym_act G (cayley_pp_gset G) g r) (usym_mul G g g')) (perm r (usym_mul G g g'))
             (map_path (Id SetTypes S S) (USym G) (s ↦ perm s (usym_mul G g g')) (gset_usym_act G (cayley_pp_gset G) g r) r (fx g))
      = usym_mul G g (perm r (usym_mul G (usym_inv G g) (usym_mul G g g')))
        by cayley_pp_transport G (shape G) g r (usym_mul G g g')
      = usym_mul G g (perm r g')
        by map_path (USym G) (USym G) (y ↦ usym_mul G g (perm r y)) (usym_mul G (usym_inv G g) (usym_mul G g g')) g'
             (ch5_usym_inv_mul_cancel G g g') ∎

def cayley_pp_fixed_from (G : Group) (r : Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G)))
  (fx : IsCayleyFixed G (set_path_permutation (principal_gset G (shape G)) (principal_gset G (shape G)) r))
  : CayleyPPFixed G r
  ≔ let S ≔ principal_gset G (shape G) in
    let perm ≔ set_path_permutation S S in
    g ↦ set_path_ext S S (gset_usym_act G (cayley_pp_gset G) g r) r
      (x ↦ calc
        perm (gset_usym_act G (cayley_pp_gset G) g r) x
        = usym_mul G g (perm r (usym_mul G (usym_inv G g) x)) by cayley_pp_transport G (shape G) g r x
        = perm r (usym_mul G g (usym_mul G (usym_inv G g) x))
          by inverse (USym G) (perm r (usym_mul G g (usym_mul G (usym_inv G g) x)))
               (usym_mul G g (perm r (usym_mul G (usym_inv G g) x))) (fx g (usym_mul G (usym_inv G g) x))
        = perm r x by map_path (USym G) (USym G) (perm r) (usym_mul G g (usym_mul G (usym_inv G g) x)) x
             (ch5_usym_mul_inv_cancel G g x) ∎)

def cayley_pp_fixed_iff (G : Group) (r : Id SetTypes (principal_gset G (shape G)) (principal_gset G (shape G)))
  : Product (CayleyPPFixed G r → IsCayleyFixed G (set_path_permutation (principal_gset G (shape G)) (principal_gset G (shape G)) r))
      (IsCayleyFixed G (set_path_permutation (principal_gset G (shape G)) (principal_gset G (shape G)) r) → CayleyPPFixed G r)
  ≔ (cayley_pp_fixed_to G r, cayley_pp_fixed_from G r)

{` A fixed permutation is right multiplication by its value at refl:
   π(x) = x · π(e) (the book's "− ∘ σ⁻¹" with σ = π(e)⁻¹). `}
def cayley_fixed_right_mult (G : Group) (p : USym G → USym G) (fx : IsCayleyFixed G p) (x : USym G)
  : Id (USym G) (p x) (usym_mul G x (p (usym_unit G)))
  ≔ concat (USym G) (p x) (p (usym_mul G x (usym_unit G))) (usym_mul G x (p (usym_unit G)))
      (map_path (USym G) (USym G) p x (usym_mul G x (usym_unit G))
        (inverse (USym G) (usym_mul G x (usym_unit G)) x (usym_abstract_laws G .unit_right x)))
      (fx x (usym_unit G))

{` The fixed permutations as an abstract group under composition. `}
def CayleyFixedPerms (G : Group) : Type
  ≔ Σ (Equiv (USym G) (USym G)) (p ↦ IsCayleyFixed G (p .map))

def cayley_fixed_perms_path (G : Group) (p q : CayleyFixedPerms G)
  (h : (x : USym G) → Id (USym G) (p .fst .map x) (q .fst .map x)) : Id (CayleyFixedPerms G) p q
  ≔ subtype_equal (Equiv (USym G) (USym G)) (e ↦ IsCayleyFixed G (e .map)) (e ↦ is_cayley_fixed_prop G (e .map)) p q
      (equiv_path (USym G) (USym G) (p .fst) (q .fst) (funext (USym G) (_ ↦ USym G) (p .fst .map) (q .fst .map) h))

def cayley_fixed_unit (G : Group) : CayleyFixedPerms G
  ≔ (identity_equiv (USym G), g g' ↦ refl (usym_mul G g g'))

def cayley_fixed_mul (G : Group) (p q : CayleyFixedPerms G) : CayleyFixedPerms G
  ≔ (compose_equiv (USym G) (USym G) (USym G) (q .fst) (p .fst),
     g g' ↦ concat (USym G) (p .fst .map (q .fst .map (usym_mul G g g'))) (p .fst .map (usym_mul G g (q .fst .map g')))
       (usym_mul G g (p .fst .map (q .fst .map g')))
       (map_path (USym G) (USym G) (p .fst .map) (q .fst .map (usym_mul G g g')) (usym_mul G g (q .fst .map g')) (q .snd g g'))
       (p .snd g (q .fst .map g')))

def cayley_fixed_inv (G : Group) (p : CayleyFixedPerms G) : CayleyFixedPerms G
  ≔ let e ≔ p .fst in
    let ei ≔ equiv_inverse_map (USym G) (USym G) e in
    (canonical_inverse_equiv (USym G) (USym G) e,
     g g' ↦ equivalence_injective (USym G) (USym G) e (ei (usym_mul G g g')) (usym_mul G g (ei g'))
       (calc
         e .map (ei (usym_mul G g g'))
         = usym_mul G g g' by equiv_counit (USym G) (USym G) e (usym_mul G g g')
         = usym_mul G g (e .map (ei g'))
           by map_path (USym G) (USym G) (usym_mul G g) g' (e .map (ei g'))
                (inverse (USym G) (e .map (ei g')) g' (equiv_counit (USym G) (USym G) e g'))
         = e .map (usym_mul G g (ei g'))
           by inverse (USym G) (e .map (usym_mul G g (ei g'))) (usym_mul G g (e .map (ei g'))) (p .snd g (ei g')) ∎))

def cayley_fixed_perms_set (G : Group) : isSet (CayleyFixedPerms G)
  ≔ sigma_set (Equiv (USym G) (USym G)) (p ↦ IsCayleyFixed G (p .map))
      (equivalences_set (USym G) (USym G) (usym_set G))
      (p ↦ prop_is_set (IsCayleyFixed G (p .map)) (is_cayley_fixed_prop G (p .map)))

def cayley_fixed_abstract_group (G : Group) : AbstractGroup
  ≔ (CayleyFixedPerms G, cayley_fixed_unit G, cayley_fixed_mul G, cayley_fixed_inv G,
     (cayley_fixed_perms_set G,
      p ↦ cayley_fixed_perms_path G (cayley_fixed_mul G p (cayley_fixed_unit G)) p (x ↦ refl (p .fst .map x)),
      p ↦ cayley_fixed_perms_path G (cayley_fixed_mul G (cayley_fixed_unit G) p) p (x ↦ refl (p .fst .map x)),
      p q r ↦ cayley_fixed_perms_path G (cayley_fixed_mul G p (cayley_fixed_mul G q r)) (cayley_fixed_mul G (cayley_fixed_mul G p q) r)
        (x ↦ refl (p .fst .map (q .fst .map (r .fst .map x)))),
      p ↦ cayley_fixed_perms_path G (cayley_fixed_mul G p (cayley_fixed_inv G p)) (cayley_fixed_unit G)
        (x ↦ equiv_counit (USym G) (USym G) (p .fst) x)))

{` Evaluation at refl: a bijection onto USym G, and an anti-homomorphism. `}
def cayley_fixed_eval (G : Group) (p : CayleyFixedPerms G) : USym G ≔ p .fst .map (usym_unit G)

def cayley_right_mult (G : Group) (c : USym G) : CayleyFixedPerms G
  ≔ (quasi_inverse_equiv (USym G) (USym G) (x ↦ usym_mul G x c) (x ↦ usym_mul G x (usym_inv G c))
       (x ↦ concat_left_inverse (BG G .carrier) (shape G) (shape G) (shape G) c x)
       (x ↦ ch5_concat_inverse_cancel (BG G .carrier) (shape G) (shape G) (shape G) c x),
     g g' ↦ inverse (USym G) (usym_mul G g (usym_mul G g' c)) (usym_mul G (usym_mul G g g') c)
       (usym_abstract_laws G .assoc g g' c))

def cayley_fixed_eval_right_mult (G : Group) (c : USym G)
  : Id (USym G) (cayley_fixed_eval G (cayley_right_mult G c)) c
  ≔ usym_abstract_laws G .unit_left c

def cayley_fixed_eval_equiv (G : Group) : BookEquiv (CayleyFixedPerms G) (USym G)
  ≔ book_quasi_inverse_equiv (CayleyFixedPerms G) (USym G) (cayley_fixed_eval G) (cayley_right_mult G)
      (p ↦ cayley_fixed_perms_path G (cayley_right_mult G (cayley_fixed_eval G p)) p
        (x ↦ inverse (USym G) (p .fst .map x) (usym_mul G x (cayley_fixed_eval G p))
          (cayley_fixed_right_mult G (p .fst .map) (p .snd) x)))
      (cayley_fixed_eval_right_mult G)

def cayley_fixed_eval_anti (G : Group) (p q : CayleyFixedPerms G)
  : Id (USym G) (cayley_fixed_eval G (cayley_fixed_mul G p q))
      (usym_mul G (cayley_fixed_eval G q) (cayley_fixed_eval G p))
  ≔ cayley_fixed_right_mult G (p .fst .map) (p .snd) (q .fst .map (usym_unit G))

{` Corrected statement: π ↦ π(refl)⁻¹ is an abstract isomorphism to abstr(G). `}
def cayley_fixed_inverse_eval_hom (G : Group)
  : IsAbstractHom (cayley_fixed_abstract_group G) (abstr G) (p ↦ usym_inv G (cayley_fixed_eval G p))
  ≔ p q ↦
    let B ≔ BG G .carrier in
    let sh ≔ shape G in
    concat (USym G) (usym_inv G (cayley_fixed_eval G (cayley_fixed_mul G p q)))
      (usym_inv G (usym_mul G (cayley_fixed_eval G q) (cayley_fixed_eval G p)))
      (usym_mul G (usym_inv G (cayley_fixed_eval G p)) (usym_inv G (cayley_fixed_eval G q)))
      (map_path (USym G) (USym G) (usym_inv G) (cayley_fixed_eval G (cayley_fixed_mul G p q))
        (usym_mul G (cayley_fixed_eval G q) (cayley_fixed_eval G p)) (cayley_fixed_eval_anti G p q))
      (inverse_concat B sh sh sh (cayley_fixed_eval G p) (cayley_fixed_eval G q))

{` The printed claim fails for Σ_3: evaluation at refl is not an abstract
   homomorphism (it would make σ·τ = τ·σ). `}
def cayley_fixed_eval_not_hom_sigma3
  (h : IsAbstractHom (cayley_fixed_abstract_group (symmetric_group three)) (abstr (symmetric_group three))
         (cayley_fixed_eval (symmetric_group three))) : Empty
  ≔ let G ≔ symmetric_group three in
    let ps ≔ cayley_right_mult G sigma3_sigma in
    let pt ≔ cayley_right_mult G sigma3_tau in
    let ev ≔ cayley_fixed_eval G in
    sigma3_tau_sigma_noncommuting
      (calc
        usym_mul G sigma3_sigma sigma3_tau
        = usym_mul G (ev ps) sigma3_tau
          by map_path (USym G) (USym G) (s ↦ usym_mul G s sigma3_tau) sigma3_sigma (ev ps)
               (inverse (USym G) (ev ps) sigma3_sigma (cayley_fixed_eval_right_mult G sigma3_sigma))
        = usym_mul G (ev ps) (ev pt)
          by map_path (USym G) (USym G) (usym_mul G (ev ps)) sigma3_tau (ev pt)
               (inverse (USym G) (ev pt) sigma3_tau (cayley_fixed_eval_right_mult G sigma3_tau))
        = ev (cayley_fixed_mul G ps pt)
          by inverse (USym G) (ev (cayley_fixed_mul G ps pt)) (usym_mul G (ev ps) (ev pt)) (h ps pt)
        = usym_mul G (ev pt) (ev ps) by cayley_fixed_eval_anti G ps pt
        = usym_mul G sigma3_tau (ev ps)
          by map_path (USym G) (USym G) (s ↦ usym_mul G s (ev ps)) (ev pt) sigma3_tau (cayley_fixed_eval_right_mult G sigma3_tau)
        = usym_mul G sigma3_tau sigma3_sigma
          by map_path (USym G) (USym G) (usym_mul G sigma3_tau) (ev ps) sigma3_sigma (cayley_fixed_eval_right_mult G sigma3_sigma) ∎)
