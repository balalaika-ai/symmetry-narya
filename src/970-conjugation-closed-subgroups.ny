export "903-normal-subgroups"
export "1030-subgroup-containment"
export "916-conjugation-abstract"

{` Chapter 9 (subgroups.tex): rem:typeofsubgpstrivifab (line 1268) parts
   (a) and (b), a conjugation criterion for normality, and the first part
   of xca:Sub(Sigma3) (line 1311): Sub(G) is transitive iff G is trivial.

   For a subgroup S = (X, x) a symmetry k of G is a symmetry of S if
   k · x = x (SubgroupHasSymmetry; these are the symmetries picked out by
   S, lem:E-preserves-symms, module 507). Conjugation conj^g(k) = g k g⁻¹
   is abstract_conj (abstr G) g k (ex:conjhom, module 723). The criterion:
   g · S = S iff conjugation by g⁻¹ preserves the symmetries of S both
   ways (subgroup_conjugate_fixed / subgroup_fixed_conj_closed), and S is
   normal iff its symmetries are closed under all conjugations
   (normal_iff_conj_closed, also in terms of SymmetryPickedOut). The
   identification of subgroups uses containment both ways
   (subgroup_le_antisym, chapter 10's module 1030). `}

{` k is a symmetry of the subgroup S = (X, x): k · x = x. `}
def SubgroupHasSymmetry (G : Group) (S : Subgroups G) (k : USym G) : Type
  ≔ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) k (S .point)) (S .point)

{` rem:typeofsubgpstrivifab (a): G is abelian iff conj^g = id for all
   g : USym G (conj^g the abstract homomorphism of ex:conjhom on abstr G). `}
def abelian_conj_identity (G : Group) (hab : IsAbelian G) (g : USym G)
  : Id (AbstractHom (abstr G) (abstr G)) (abstract_conj_hom (abstr G) g) (abstract_hom_id (abstr G))
  ≔ let AG ≔ abstr G in
    abstract_hom_ext AG AG (abstract_conj_hom AG g) (abstract_hom_id AG)
      (s ↦ concat (USym G) (usym_mul G (usym_mul G g s) (usym_inv G g)) (usym_mul G (usym_mul G s g) (usym_inv G g)) s
        (refl ((t ↦ usym_mul G t (usym_inv G g)) : USym G → USym G) (hab g s))
        (ag_mul_inv_cancel_right AG s g))

def conj_identity_abelian (G : Group)
  (h : (g : USym G) → Id (AbstractHom (abstr G) (abstr G)) (abstract_conj_hom (abstr G) g) (abstract_hom_id (abstr G)))
  : IsAbelian G
  ≔ g k ↦
    let AG ≔ abstr G in
    let e : Id (USym G) (usym_mul G (usym_mul G g k) (usym_inv G g)) k
      ≔ refl ((φ ↦ φ .fst k) : AbstractHom AG AG → USym G) (h g) in
    calc
      usym_mul G g k
      = usym_mul G (usym_mul G (usym_mul G g k) (usym_inv G g)) g
        by inverse (USym G) (usym_mul G (usym_mul G (usym_mul G g k) (usym_inv G g)) g) (usym_mul G g k)
             (ag_mul_cancel_inv_right AG (usym_mul G g k) g)
      = usym_mul G k g by refl ((t ↦ usym_mul G t g) : USym G → USym G) e ∎

def abelian_iff_conj_identity (G : Group)
  : Product
      (IsAbelian G
        → (g : USym G) → Id (AbstractHom (abstr G) (abstr G)) (abstract_conj_hom (abstr G) g) (abstract_hom_id (abstr G)))
      (((g : USym G) → Id (AbstractHom (abstr G) (abstr G)) (abstract_conj_hom (abstr G) g) (abstract_hom_id (abstr G)))
        → IsAbelian G)
  ≔ (abelian_conj_identity G, conj_identity_abelian G)

{` The concrete conj^g of module 437 acts on symmetries as the abstract one. `}
def conj_hom_usym_abstract (G : Group) (g k : USym G)
  : Id (USym G) (usym_hom G G (conj_hom G (shape G) g) k) (abstract_conj (abstr G) g k)
  ≔ conj_at_shape_usym G g k

{` conj^g(k) · (g · x) = g · (k · x) in any G-set. `}
def conj_act_shift (G : Group) (X : GSet G) (g k : USym G) (x : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X (abstract_conj (abstr G) g k) (gset_usym_act G X g x))
      (gset_usym_act G X g (gset_usym_act G X k x))
  ≔ let s ≔ shape G in
    let Y ≔ gset_underlying G X in
    let ig ≔ usym_inv G g in
    let act ≔ gset_usym_act G X in
    calc
      act (abstract_conj (abstr G) g k) (act g x)
      = act (usym_mul G g k) (act ig (act g x)) by gset_act_concat G X s s s ig (usym_mul G g k) (act g x)
      = act g (act k (act ig (act g x))) by gset_act_concat G X s s s k g (act ig (act g x))
      = act g (act k x) by refl ((y ↦ act g (act k y)) : Y → Y) (gset_act_inverse_left G X s s g x) ∎

{` conj^g ∘ conj^{g⁻¹} = id. `}
def conj_conj_inverse (G : Group) (g k : USym G)
  : Id (USym G) (abstract_conj (abstr G) g (abstract_conj (abstr G) (usym_inv G g) k)) k
  ≔ let AG ≔ abstr G in
    calc
      abstract_conj AG g (abstract_conj AG (usym_inv G g) k)
      = abstract_conj AG (usym_mul G g (usym_inv G g)) k
        by inverse (USym G) (abstract_conj AG (usym_mul G g (usym_inv G g)) k)
             (abstract_conj AG g (abstract_conj AG (usym_inv G g) k)) (hom_gset_conj_mul_law AG g (usym_inv G g) k)
      = abstract_conj AG (usym_unit G) k
        by refl ((t ↦ abstract_conj AG t k) : USym G → USym G) (AG .laws .inv_right g)
      = k by hom_gset_conj_unit_law AG k ∎

{` g · a = g · b implies a = b. `}
def gset_usym_act_cancel (G : Group) (X : GSet G) (g : USym G) (a b : gset_underlying G X)
  (e : Id (gset_underlying G X) (gset_usym_act G X g a) (gset_usym_act G X g b))
  : Id (gset_underlying G X) a b
  ≔ let s ≔ shape G in
    let Y ≔ gset_underlying G X in
    let back ≔ gset_usym_act G X (usym_inv G g) in
    calc
      a = back (gset_usym_act G X g a) by inverse Y (back (gset_usym_act G X g a)) a (gset_act_inverse_left G X s s g a)
      = back (gset_usym_act G X g b) by refl back e
      = b by gset_act_inverse_left G X s s g b ∎

{` The criterion: if conjugation by g⁻¹ maps the symmetries of S into
   symmetries of S and conversely, then g · S = S (g · S = (X, g · x) is
   subgroups_move of module 902, the action of Sub(G)). `}
def subgroup_conjugate_fixed (G : Group) (S : Subgroups G) (g : USym G)
  (c1 : (k : USym G) → SubgroupHasSymmetry G S k → SubgroupHasSymmetry G S (abstract_conj (abstr G) (usym_inv G g) k))
  (c2 : (k : USym G) → SubgroupHasSymmetry G S (abstract_conj (abstr G) (usym_inv G g) k) → SubgroupHasSymmetry G S k)
  : Id (Subgroups G) (subgroups_move G (shape G) (shape G) g S) S
  ≔ let X ≔ S .gset in
    let x ≔ S .point in
    let Y ≔ gset_underlying G X in
    let act ≔ gset_usym_act G X in
    let AG ≔ abstr G in
    let kk : USym G → USym G ≔ k ↦ abstract_conj AG (usym_inv G g) k in
    let shift : (k : USym G) → Id Y (act k (act g x)) (act g (act (kk k) x))
      ≔ k ↦ concat Y (act k (act g x)) (act (abstract_conj AG g (kk k)) (act g x)) (act g (act (kk k) x))
          (refl ((t ↦ act t (act g x)) : USym G → Y) (inverse (USym G) (abstract_conj AG g (kk k)) k (conj_conj_inverse G g k)))
          (conj_act_shift G X g (kk k) x) in
    subgroup_le_antisym G (subgroups_move G (shape G) (shape G) g S) S
      (k r ↦ c2 k (gset_usym_act_cancel G X g (act (kk k) x) x
        (concat Y (act g (act (kk k) x)) (act k (act g x)) (act g x)
          (inverse Y (act k (act g x)) (act g (act (kk k) x)) (shift k)) r)))
      (k r ↦ concat Y (act k (act g x)) (act g (act (kk k) x)) (act g x) (shift k) (refl (act g) (c1 k r)))

{` Conversely, if g · S = S then conjugation by g maps symmetries of S to
   symmetries of S. `}
def subgroup_fixed_conj_closed (G : Group) (S : Subgroups G) (g : USym G)
  (e : Id (Subgroups G) (subgroups_move G (shape G) (shape G) g S) S) (k : USym G) (r : SubgroupHasSymmetry G S k)
  : SubgroupHasSymmetry G S (abstract_conj (abstr G) g k)
  ≔ let X ≔ S .gset in
    let x ≔ S .point in
    let Y ≔ gset_underlying G X in
    let h ≔ abstract_conj (abstr G) g k in
    let P : PointedGSet G → Type ≔ u ↦ Id (gset_underlying G (u .fst)) (gset_usym_act G (u .fst) h (u .snd)) (u .snd) in
    transport (PointedGSet G) P (X, gset_usym_act G X g x) (X, x)
      (refl ((T ↦ (T .gset, T .point)) : Subgroups G → PointedGSet G) e)
      (concat Y (gset_usym_act G X h (gset_usym_act G X g x)) (gset_usym_act G X g (gset_usym_act G X k x))
        (gset_usym_act G X g x) (conj_act_shift G X g k x) (refl (gset_usym_act G X g) r))

{` S is closed under conjugation: conj^g(k) is a symmetry of S whenever k is. `}
def SubgroupConjClosed (G : Group) (S : Subgroups G) : Type
  ≔ (g k : USym G) → SubgroupHasSymmetry G S k → SubgroupHasSymmetry G S (abstract_conj (abstr G) g k)

def conj_closed_fixed (G : Group) (S : Subgroups G) (c : SubgroupConjClosed G S) (g : USym G)
  : Id (Subgroups G) (subgroups_move G (shape G) (shape G) g S) S
  ≔ subgroup_conjugate_fixed G S g (c (usym_inv G g))
      (k r ↦ transport (USym G) (SubgroupHasSymmetry G S)
        (abstract_conj (abstr G) g (abstract_conj (abstr G) (usym_inv G g) k)) k
        (conj_conj_inverse G g k) (c g (abstract_conj (abstr G) (usym_inv G g) k) r))

def conj_closed_normal (G : Group) (S : Subgroups G) (c : SubgroupConjClosed G S) : IsNormalSubgroup G S
  ≔ fixed_normal_subgroup G S (conj_closed_fixed G S c)

def normal_conj_closed (G : Group) (S : Subgroups G) (n : IsNormalSubgroup G S) : SubgroupConjClosed G S
  ≔ g k r ↦ subgroup_fixed_conj_closed G S g (normal_subgroup_fixed G S n g) k r

{` A subgroup is normal iff its symmetries are closed under conjugation. `}
def normal_iff_conj_closed (G : Group) (S : Subgroups G)
  : Product (IsNormalSubgroup G S → SubgroupConjClosed G S) (SubgroupConjClosed G S → IsNormalSubgroup G S)
  ≔ (normal_conj_closed G S, conj_closed_normal G S)

{` The same with the symmetries picked out by the monomorphism F(S)
   (lem:E-preserves-symms). `}
def SubgroupPickedOutConjClosed (G : Group) (S : Subgroups G) : Type
  ≔ (g k : USym G) → SymmetryPickedOut G (subgroup_to_mono G S) k
      → SymmetryPickedOut G (subgroup_to_mono G S) (abstract_conj (abstr G) g k)

def normal_iff_picked_out_conj_closed (G : Group) (S : Subgroups G)
  : Product (IsNormalSubgroup G S → SubgroupPickedOutConjClosed G S) (SubgroupPickedOutConjClosed G S → IsNormalSubgroup G S)
  ≔ (n g k t ↦ subgroup_fixes_picked_out G S (abstract_conj (abstr G) g k)
        (normal_conj_closed G S n g k (subgroup_picked_out_fixes G S k t)),
     c ↦ conj_closed_normal G S
       (g k r ↦ subgroup_picked_out_fixes G S (abstract_conj (abstr G) g k)
         (c g k (subgroup_fixes_picked_out G S k r))))

{` A G-set is trivial (as an action) if every symmetry fixes every element;
   likewise for abstract G-sets. `}
def GSetActionTrivial (G : Group) (X : GSet G) : Type
  ≔ (g : USym G) (x : gset_underlying G X) → Id (gset_underlying G X) (gset_usym_act G X g x) x

def AGSetActionTrivial (AG : AbstractGroup) (X : AbstractGSet AG) : Type
  ≔ (g : AG .carrier) (x : agset_carrier AG X) → Id (agset_carrier AG X) (agset_act AG X g x) x

{` Sub(G) is trivial iff every subgroup is normal. `}
def all_normal_subgroups_trivial (G : Group) (h : (S : Subgroups G) → IsNormalSubgroup G S)
  : GSetActionTrivial G (subgroups_gset G)
  ≔ g S ↦ concat (Subgroups G) (gset_usym_act G (subgroups_gset G) g S) (subgroups_move G (shape G) (shape G) g S) S
      (subgroups_gset_usym_act G g S) (normal_subgroup_fixed G S (h S) g)

def subgroups_trivial_all_normal (G : Group) (t : GSetActionTrivial G (subgroups_gset G)) (S : Subgroups G)
  : IsNormalSubgroup G S
  ≔ fixed_normal_subgroup G S
      (g ↦ concat (Subgroups G) (subgroups_move G (shape G) (shape G) g S) (gset_usym_act G (subgroups_gset G) g S) S
        (inverse (Subgroups G) (gset_usym_act G (subgroups_gset G) g S) (subgroups_move G (shape G) (shape G) g S)
          (subgroups_gset_usym_act G g S))
        (t g S))

{` Mono(G) and Sub(G) are identified as G-sets (E, module 902), so one is
   trivial iff the other is; and then so is the abstract G-set of
   lem:conj-abstract (module 916). `}
def monos_trivial_of_subgroups (G : Group) (t : GSetActionTrivial G (subgroups_gset G)) : GSetActionTrivial G (monos_gset G)
  ≔ transport (GSet G) (GSetActionTrivial G) (subgroups_gset G) (monos_gset G)
      (inverse (GSet G) (monos_gset G) (subgroups_gset G) (monos_subgroups_gset_path G)) t

def subgroups_trivial_of_monos (G : Group) (t : GSetActionTrivial G (monos_gset G)) : GSetActionTrivial G (subgroups_gset G)
  ≔ transport (GSet G) (GSetActionTrivial G) (monos_gset G) (subgroups_gset G) (monos_subgroups_gset_path G) t

def ev_gset_trivial (G : Group) (X : GSet G) (t : GSetActionTrivial G X) : AGSetActionTrivial (abstr G) (ev_gset G X)
  ≔ g x ↦ concat (gset_underlying G X) (agset_act (abstr G) (ev_gset G X) g x) (gset_usym_act G X g x) x
      (ev_gset_act G X g x) (t g x)

def conj_abstract_trivial_of_monos (G : Group) (t : GSetActionTrivial G (monos_gset G))
  : AGSetActionTrivial (abstr G) (conj_abstract_agset G)
  ≔ transport (AbstractGSet (abstr G)) (AGSetActionTrivial (abstr G)) (gset_abstract_gset_equiv G .map (monos_gset G))
      (conj_abstract_agset G) (conj_abstract_path G) (ev_gset_trivial G (monos_gset G) t)

{` rem:typeofsubgpstrivifab (b): if G is abelian, every subgroup is normal
   and the G-sets Sub(G), Mono(G) and the abstr(G)-set of abstract
   monomorphisms are trivial. (The converse is false: module 971.) `}
def abelian_conj_closed (G : Group) (hab : IsAbelian G) (S : Subgroups G) : SubgroupConjClosed G S
  ≔ g k r ↦ transport (USym G) (SubgroupHasSymmetry G S) k (abstract_conj (abstr G) g k)
      (inverse (USym G) (abstract_conj (abstr G) g k) k
        (refl ((φ ↦ φ .fst k) : AbstractHom (abstr G) (abstr G) → USym G) (abelian_conj_identity G hab g)))
      r

def abelian_subgroup_normal (G : Group) (hab : IsAbelian G) (S : Subgroups G) : IsNormalSubgroup G S
  ≔ conj_closed_normal G S (abelian_conj_closed G hab S)

def abelian_subgroups_trivial (G : Group) (hab : IsAbelian G) : GSetActionTrivial G (subgroups_gset G)
  ≔ all_normal_subgroups_trivial G (abelian_subgroup_normal G hab)

def abelian_monos_trivial (G : Group) (hab : IsAbelian G) : GSetActionTrivial G (monos_gset G)
  ≔ monos_trivial_of_subgroups G (abelian_subgroups_trivial G hab)

def abelian_conj_abstract_trivial (G : Group) (hab : IsAbelian G) : AGSetActionTrivial (abstr G) (conj_abstract_agset G)
  ≔ conj_abstract_trivial_of_monos G (abelian_monos_trivial G hab)

{` The trivial subgroup (P_G, refl) (the same term as fingp_trivial_subgroup
   of module 1036) and the full subgroup E(G, id) (group_full_subgroup,
   module 1021) are normal in every group. `}
def principal_subgroup (G : Group) : Subgroups G ≔ (principal_gset G, refl (shape G), principal_gset_transitive G)

def principal_subgroup_symmetry_unit (G : Group) (k : USym G) (r : SubgroupHasSymmetry G (principal_subgroup G) k)
  : Id (USym G) k (usym_unit G)
  ≔ concat (USym G) k (usym_mul G k (usym_unit G)) (usym_unit G)
      (inverse (USym G) (usym_mul G k (usym_unit G)) k (abstr G .laws .unit_right k)) r

def principal_subgroup_conj_closed (G : Group) : SubgroupConjClosed G (principal_subgroup G)
  ≔ g k r ↦
    let AG ≔ abstr G in
    let e ≔ usym_unit G in
    let p : Id (USym G) (abstract_conj AG g k) e
      ≔ calc
          abstract_conj AG g k = abstract_conj AG g e by refl (abstract_conj AG g) (principal_subgroup_symmetry_unit G k r)
          = usym_mul G g (usym_inv G g)
            by refl ((t ↦ usym_mul G t (usym_inv G g)) : USym G → USym G) (AG .laws .unit_right g)
          = e by AG .laws .inv_right g ∎ in
    transport (USym G) (SubgroupHasSymmetry G (principal_subgroup G)) e (abstract_conj AG g k)
      (inverse (USym G) (abstract_conj AG g k) e p) (AG .laws .unit_left e)

def principal_subgroup_normal (G : Group) : IsNormalSubgroup G (principal_subgroup G)
  ≔ conj_closed_normal G (principal_subgroup G) (principal_subgroup_conj_closed G)

def full_subgroup_has_symmetry (G : Group) (k : USym G) : SubgroupHasSymmetry G (group_full_subgroup G) k
  ≔ let S ≔ group_full_subgroup G in
    let Y ≔ gset_underlying G (S .gset) in
    contractible_prop Y (native_contraction Y (group_full_subgroup_fibers_contractible G (shape G)))
      (gset_usym_act G (S .gset) k (S .point)) (S .point)

def full_subgroup_normal (G : Group) : IsNormalSubgroup G (group_full_subgroup G)
  ≔ conj_closed_normal G (group_full_subgroup G) (g k r ↦ full_subgroup_has_symmetry G (abstract_conj (abstr G) g k))

{` Symmetries of subgroups transport along identifications of subgroups. `}
def subgroup_symmetry_transport (G : Group) (S T : Subgroups G) (e : Id (Subgroups G) S T) (k : USym G)
  (r : SubgroupHasSymmetry G S k) : SubgroupHasSymmetry G T k
  ≔ transport (Subgroups G) (U ↦ SubgroupHasSymmetry G U k) S T e r

{` xca:Sub(Sigma3), first part: Sub(G) is a transitive G-set iff G is
   trivial. If G is trivial every subgroup has every symmetry, so all
   subgroups are equal; if Sub(G) is transitive, the fixed points 1 and G
   are in one orbit, hence equal, so every symmetry fixes refl in P_G. `}
def trivial_group_has_symmetry (G : Group) (h : IsTrivialGroup G) (S : Subgroups G) (k : USym G)
  : SubgroupHasSymmetry G S k
  ≔ let c ≔ is_trivial_group_usym_contractible G h in
    let ke : Id (USym G) (usym_unit G) k
      ≔ concat (USym G) (usym_unit G) (c .center) k
          (inverse (USym G) (c .center) (usym_unit G) (c .contract (usym_unit G))) (c .contract k) in
    transport (USym G) (SubgroupHasSymmetry G S) (usym_unit G) k ke
      (gset_act_refl G (S .gset) (shape G) (S .point))

def trivial_group_subgroups_equal (G : Group) (h : IsTrivialGroup G) (S T : Subgroups G) : Id (Subgroups G) S T
  ≔ subgroup_le_antisym G S T (k r ↦ trivial_group_has_symmetry G h T k) (k r ↦ trivial_group_has_symmetry G h S k)

def trivial_group_subgroups_transitive (G : Group) (h : IsTrivialGroup G) : IsTransitive G (subgroups_gset G)
  ≔ let P ≔ principal_subgroup G in
    let X ≔ subgroups_gset G in
    mere (Σ (Subgroups G) (x ↦ (y : Subgroups G) → Mere (Σ (USym G) (g ↦ Id (Subgroups G) x (gset_usym_act G X g y)))))
      (P, y ↦ mere (Σ (USym G) (g ↦ Id (Subgroups G) P (gset_usym_act G X g y)))
        (usym_unit G,
         concat (Subgroups G) P y (gset_usym_act G X (usym_unit G) y) (trivial_group_subgroups_equal G h P y)
           (inverse (Subgroups G) (gset_usym_act G X (usym_unit G) y) y (gset_act_refl G X (shape G) y))))

def subgroups_transitive_trivial_group (G : Group) (t : IsTransitive G (subgroups_gset G)) : IsTrivialGroup G
  ≔ let X ≔ subgroups_gset G in
    let P ≔ principal_subgroup G in
    let F ≔ group_full_subgroup G in
    let conclude : Id (Subgroups G) P F → IsTrivialGroup G
      ≔ e ↦ usym_contractible_trivial_group G
          (usym_unit G,
           k ↦ inverse (USym G) k (usym_unit G)
             (principal_subgroup_symmetry_unit G k
               (subgroup_symmetry_transport G F P (inverse (Subgroups G) P F e) k (full_subgroup_has_symmetry G k)))) in
    let fixed_of : (S : Subgroups G) → IsNormalSubgroup G S → (g : USym G) → Id (Subgroups G) (gset_usym_act G X g S) S
      ≔ S n g ↦ concat (Subgroups G) (gset_usym_act G X g S) (subgroups_move G (shape G) (shape G) g S) S
          (subgroups_gset_usym_act G g S) (normal_subgroup_fixed G S n g) in
    let W ≔ Σ (Subgroups G) (x ↦ (y : Subgroups G) → Mere (Σ (USym G) (g ↦ Id (Subgroups G) x (gset_usym_act G X g y)))) in
    let R ≔ is_trivial_group_prop G in
    mere_rec W (IsTrivialGroup G) R
      (w ↦ mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (w .fst) (gset_usym_act G X g P))) (IsTrivialGroup G) R
        (a ↦ mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (w .fst) (gset_usym_act G X g F))) (IsTrivialGroup G) R
          (b ↦ conclude
            (calc
              P = gset_usym_act G X (a .fst) P
                by inverse (Subgroups G) (gset_usym_act G X (a .fst) P) P (fixed_of P (principal_subgroup_normal G) (a .fst))
              = w .fst by inverse (Subgroups G) (w .fst) (gset_usym_act G X (a .fst) P) (a .snd)
              = gset_usym_act G X (b .fst) F by b .snd
              = F by fixed_of F (full_subgroup_normal G) (b .fst) ∎))
          (w .snd F))
        (w .snd P))
      t

def subgroups_transitive_iff_trivial (G : Group)
  : Product (IsTransitive G (subgroups_gset G) → IsTrivialGroup G) (IsTrivialGroup G → IsTransitive G (subgroups_gset G))
  ≔ (subgroups_transitive_trivial_group G, trivial_group_subgroups_transitive G)
