export "540-torsor-characterizations"

{` Chapter 5, sec:groupssubperm: "any symmetry is a symmetry in Set" (Cayley,
   lem:allgpsarepermutationgps). Bρ_G ≔ P_-(sh_G) : BG → Set_(USym G),
   z ↦ (z = sh_G), pointed by reflexivity. `}

def cayley_set (G : Group) : SetTypes ≔ (USym G, usym_set G)

def cayley_classifying_map (G : Group) (z : BG G .carrier) : BG (permutation_group (cayley_set G)) .carrier
  ≔ (gset_paths G z (shape G),
     mere_rec (Id (BG G .carrier) (shape G) z) (Mere (Id SetTypes (cayley_set G) (gset_paths G z (shape G))))
       (mere_isprop (Id SetTypes (cayley_set G) (gset_paths G z (shape G))))
       (p ↦ mere (Id SetTypes (cayley_set G) (gset_paths G z (shape G)))
         (map_path (BG G .carrier) SetTypes (w ↦ gset_paths G w (shape G)) (shape G) z p))
       (bg_connected G .snd (shape G) z))

{` ρ_G : Hom(G, Σ_{USym G}); the pointing path has first component refl. `}
def cayley_hom (G : Group) : GroupHom G (permutation_group (cayley_set G))
  ≔ mkhom G (permutation_group (cayley_set G))
      (cayley_classifying_map G,
       component_path SetTypes (cayley_set G) (component_point SetTypes (cayley_set G))
         (cayley_classifying_map G (shape G)) (refl (cayley_set G)))

{` The book's proof. ev_sh : Torsor_G → Set_(USym G), X ↦ X(sh_G); the
   triangle Bρ_G = ev_sh ∘ P_- commutes (first components agree by definition). `}
def torsor_evaluation (G : Group) (T : Torsors G) : BG (permutation_group (cayley_set G)) .carrier
  ≔ (T .fst (shape G),
     mere_rec (Id (GSet G) (principal_gset G) (T .fst)) (Mere (Id SetTypes (cayley_set G) (T .fst (shape G))))
       (mere_isprop (Id SetTypes (cayley_set G) (T .fst (shape G))))
       (p ↦ mere (Id SetTypes (cayley_set G) (T .fst (shape G)))
         (map_path (GSet G) SetTypes (X ↦ X (shape G)) (principal_gset G) (T .fst) p))
       (T .snd))

def cayley_factorization (G : Group) (z : BG G .carrier)
  : Id (BG (permutation_group (cayley_set G)) .carrier) (torsor_evaluation G (bg_to_torsors G z)) (cayley_classifying_map G z)
  ≔ component_path SetTypes (cayley_set G) (torsor_evaluation G (bg_to_torsors G z)) (cayley_classifying_map G z)
      (refl (gset_paths G z (shape G)))

{` The fiber of ev_sh at S is a subtype of Σ_{X : BG → Set} (S = X(sh_G)), the
   set of pointed maps BG →* (Set, S) (ft:ptd-decr-h-lev). `}
def TorsorEvaluationFiberData (G : Group) (c : BG (permutation_group (cayley_set G)) .carrier) : Type
  ≔ Σ (BookPointedMap (BG G) (SetTypes, c .fst)) (u ↦ Mere (Id (GSet G) (principal_gset G) (u .fst)))

def torsor_evaluation_fiber_equiv (G : Group) (c : BG (permutation_group (cayley_set G)) .carrier)
  : Equiv (BookFiber (Torsors G) (BG (permutation_group (cayley_set G)) .carrier) (torsor_evaluation G) c)
      (TorsorEvaluationFiberData G c)
  ≔ let S ≔ cayley_set G in
    let C ≔ BG (permutation_group S) .carrier in
    let Fib ≔ BookFiber (Torsors G) C (torsor_evaluation G) c in
    quasi_inverse_equiv Fib (TorsorEvaluationFiberData G c)
      (w ↦ ((w .fst .fst, w .snd .fst), w .fst .snd))
      (v ↦ ((v .fst .fst, v .snd),
            component_path SetTypes S c (torsor_evaluation G (v .fst .fst, v .snd)) (v .fst .snd)))
      (w ↦ map_path (Id C c (torsor_evaluation G (w .fst))) Fib (r ↦ (w .fst, r))
        (component_path SetTypes S c (torsor_evaluation G (w .fst)) (w .snd .fst)) (w .snd)
        (equiv_retraction (Id C c (torsor_evaluation G (w .fst))) (Id SetTypes (c .fst) (w .fst .fst (shape G)))
          (component_path_equiv SetTypes S c (torsor_evaluation G (w .fst))) (w .snd)))
      (v ↦ refl v)

def torsor_evaluation_covering (G : Group)
  : IsCovering (Torsors G) (BG (permutation_group (cayley_set G)) .carrier) (torsor_evaluation G)
  ≔ let C ≔ BG (permutation_group (cayley_set G)) .carrier in
    c ↦ hlevel_two_to_set (BookFiber (Torsors G) C (torsor_evaluation G) c)
      (hlevel_equiv (suc. (suc. zero.)) (TorsorEvaluationFiberData G c) (BookFiber (Torsors G) C (torsor_evaluation G) c)
        (canonical_inverse_equiv (BookFiber (Torsors G) C (torsor_evaluation G) c) (TorsorEvaluationFiberData G c)
          (torsor_evaluation_fiber_equiv G c))
        (set_to_hlevel_two (TorsorEvaluationFiberData G c)
          (sigma_set (BookPointedMap (BG G) (SetTypes, c .fst)) (u ↦ Mere (Id (GSet G) (principal_gset G) (u .fst)))
            (pointed_maps_set (BG G) (SetTypes, c .fst) (bg_connected G) sets_groupoid)
            (u ↦ prop_is_set (Mere (Id (GSet G) (principal_gset G) (u .fst)))
              (mere_isprop (Id (GSet G) (principal_gset G) (u .fst)))))))

def cayley_classifying_covering (G : Group)
  : IsCovering (BG G .carrier) (BG (permutation_group (cayley_set G)) .carrier) (cayley_classifying_map G)
  ≔ let B ≔ BG G .carrier in
    let C ≔ BG (permutation_group (cayley_set G)) .carrier in
    let h : TruncatedMap (suc. (suc. zero.)) B C (compose B (Torsors G) C (torsor_evaluation G) (bg_to_torsors G))
      ≔ preequivalence_truncated_map (suc. (suc. zero.)) B (Torsors G) C
          (native_equivalence B (Torsors G) (bg_torsors_equiv G)) (torsor_evaluation G)
          (c ↦ set_to_hlevel_two (BookFiber (Torsors G) C (torsor_evaluation G) c) (torsor_evaluation_covering G c)) in
    let k : TruncatedMap (suc. (suc. zero.)) B C (cayley_classifying_map G)
      ≔ transport (B → C) (TruncatedMap (suc. (suc. zero.)) B C)
          (compose B (Torsors G) C (torsor_evaluation G) (bg_to_torsors G)) (cayley_classifying_map G)
          (funext B (_ ↦ C) (compose B (Torsors G) C (torsor_evaluation G) (bg_to_torsors G)) (cayley_classifying_map G)
            (cayley_factorization G)) h in
    c ↦ hlevel_two_to_set (BookFiber B C (cayley_classifying_map G) c) (k c)

{` lem:allgpsarepermutationgps (Cayley). ρ_G is a monomorphism. `}
def cayley_mono (G : Group) : IsGroupMono G (permutation_group (cayley_set G)) (cayley_hom G)
  ≔ covering_group_mono G (permutation_group (cayley_set G)) (cayley_hom G) (cayley_classifying_covering G)

def cayley_monomorphism (G : Group) : GroupMonos (permutation_group (cayley_set G))
  ≔ (G, (cayley_hom G, cayley_mono G))

{` "The induced map on symmetries is USym ρ_G : g ↦ (x ↦ x g⁻¹)". `}
def cayley_usym_action (G : Group) (g x : USym G)
  : Id (USym G) (permutation_action (cayley_set G) (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) g) x)
      (usym_mul G x (usym_inv G g))
  ≔ let S ≔ cayley_set G in
    let B ≔ BG G .carrier in
    let C ≔ BG (permutation_group S) .carrier in
    let F : C → Type ≔ c ↦ c .fst .fst in
    let c0 ≔ component_point SetTypes S in
    let c1 ≔ cayley_classifying_map G (shape G) in
    let kpt ≔ hom_point G (permutation_group S) (cayley_hom G) in
    let l ≔ map_path B C (cayley_classifying_map G) (shape G) (shape G) g in
    let tk : (y : USym G) → Id (USym G) (transport C F c0 c1 kpt y) y ≔ y ↦ transport_refl Type (T ↦ T) (USym G) y in
    let w ≔ transport C F c1 c1 l (transport C F c0 c1 kpt x) in
    calc
      permutation_action S (usym_hom G (permutation_group S) (cayley_hom G) g) x
      = transport C F c1 c0 (concat C c1 c1 c0 l (inverse C c0 c1 kpt)) (transport C F c0 c1 kpt x)
        by transport_concat C F c0 c1 c0 kpt (concat C c1 c1 c0 l (inverse C c0 c1 kpt)) x
      = transport C F c1 c0 (inverse C c0 c1 kpt) w
        by transport_concat C F c1 c1 c0 l (inverse C c0 c1 kpt) (transport C F c0 c1 kpt x)
      = transport C F c1 c0 (inverse C c0 c1 kpt) (transport C F c0 c1 kpt w)
        by map_path (USym G) (USym G) (transport C F c1 c0 (inverse C c0 c1 kpt)) w (transport C F c0 c1 kpt w)
             (inverse (USym G) (transport C F c0 c1 kpt w) w (tk w))
      = w by transport_inverse_roundtrip C F c0 c1 kpt w
      = transport C F c1 c1 l x
        by map_path (USym G) (USym G) (transport C F c1 c1 l) (transport C F c0 c1 kpt x) x (tk x)
      = concat B (shape G) (shape G) (shape G) (inverse B (shape G) (shape G) g) x
        by gset_paths_family_transport G (shape G) (shape G) (shape G) g x ∎

{` Remark after lem:allgpsarepermutationgps (elementary proof): the action
   formula alone shows that USym ρ_G is injective (evaluate at refl). `}
def cayley_usym_reflects (G : Group) : PathReflecting (USym G) (USym (permutation_group (cayley_set G)))
    (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G))
  ≔ g h e ↦
    let B ≔ BG G .carrier in
    let sh ≔ shape G in
    let r ≔ refl sh in
    let act : USym (permutation_group (cayley_set G)) → USym G ≔ p ↦ permutation_action (cayley_set G) p r in
    let ginv ≔ inverse B sh sh g in
    let hinv ≔ inverse B sh sh h in
    let s : Id (USym G) ginv hinv
      ≔ calc
          ginv = concat B sh sh sh ginv r by inverse (USym G) (concat B sh sh sh ginv r) ginv (concat_p1 B sh sh ginv)
          = act (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) g)
            by inverse (USym G) (act (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) g)) (concat B sh sh sh ginv r)
                 (cayley_usym_action G g r)
          = act (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) h)
            by map_path (USym (permutation_group (cayley_set G))) (USym G) act
                 (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) g)
                 (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G) h) e
          = concat B sh sh sh hinv r by cayley_usym_action G h r
          = hinv by concat_p1 B sh sh hinv ∎ in
    calc
      g = inverse B sh sh ginv by inverse (USym G) (inverse B sh sh ginv) g (inverse_inverse B sh sh g)
      = inverse B sh sh hinv by map_path (USym G) (USym G) (inverse B sh sh) ginv hinv s
      = h by inverse_inverse B sh sh h ∎

def cayley_mono_elementary (G : Group) : IsGroupMono G (permutation_group (cayley_set G)) (cayley_hom G)
  ≔ path_reflecting_set_embedding (USym G) (USym (permutation_group (cayley_set G)))
      (usym_set (permutation_group (cayley_set G)))
      (usym_hom G (permutation_group (cayley_set G)) (cayley_hom G)) (cayley_usym_reflects G)

{` The subgroup E(G, ρ_G) of Σ_{USym G}: a symmetry π of its shape is picked
   out iff π = USym ρ_G(g) for some g, i.e. (cayley_usym_action) π is right
   multiplication by g⁻¹ (lem:E-preserves-symms). `}
def cayley_subgroup (G : Group) : Subgroups (permutation_group (cayley_set G))
  ≔ mono_to_subgroup (permutation_group (cayley_set G)) (cayley_monomorphism G)

def cayley_subgroup_symmetries (G : Group) (p : USym (permutation_group (cayley_set G)))
  : Product
      (Id (gset_underlying (permutation_group (cayley_set G)) (cayley_subgroup G .gset))
          (gset_usym_act (permutation_group (cayley_set G)) (cayley_subgroup G .gset) p (cayley_subgroup G .point))
          (cayley_subgroup G .point)
        → SymmetryPickedOut (permutation_group (cayley_set G)) (cayley_monomorphism G) p)
      (SymmetryPickedOut (permutation_group (cayley_set G)) (cayley_monomorphism G) p
        → Id (gset_underlying (permutation_group (cayley_set G)) (cayley_subgroup G .gset))
          (gset_usym_act (permutation_group (cayley_set G)) (cayley_subgroup G .gset) p (cayley_subgroup G .point))
          (cayley_subgroup G .point))
  ≔ let P ≔ permutation_group (cayley_set G) in
    mono_preserves_symmetries P (cayley_subgroup G) (cayley_monomorphism G)
      (inverse (GroupMonos P) (subgroup_to_mono P (cayley_subgroup G)) (cayley_monomorphism G)
        (mono_subgroup_roundtrip P (cayley_monomorphism G)))
      p
