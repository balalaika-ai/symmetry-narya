export "02-abshom"
export "../../../src/412-symmetric-group-two"

{` Blind statements, chapter 7, section "Groups: from abstract to concrete and back". `}

def blind_abshom_set (G H : BlindAbsGroup) : isSet (BlindAbsHom G H)
  ≔ sigma_set (G .carrier → H .carrier) (BlindIsAbsHom G H)
      (pi_set (G .carrier) (_ ↦ H .carrier) (_ ↦ blind_ag_set H))
      (f ↦ prop_is_set (BlindIsAbsHom G H f)
        (pi_prop (G .carrier) (s ↦ (s' : G .carrier) → Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
          (s ↦ pi_prop (G .carrier) (s' ↦ Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
            (s' ↦ blind_ag_set H (f (G .mul s s')) (H .mul (f s) (f s'))))))

{` def:abstrGtorsors. abstr(Σ_X), the abstract permutation group of a set X. `}
def blind_perm_group (X : SetTypes) : BlindAbsGroup ≔ blind_abstr (permutation_group X)

{` The type of G-sets: Σ (X : Set) Hom^abs(G, abstr(Σ_X)). `}
def BlindAbsGSet (G : BlindAbsGroup) : Type ≔ Σ SetTypes (X ↦ BlindAbsHom G (blind_perm_group X))

def blind_gset_carrier (G : BlindAbsGroup) (X : BlindAbsGSet G) : Type ≔ X .fst .fst

{` s ·_X x: the symmetry s ·_X : X = X applied to x (by transport). `}
def blind_gset_act (G : BlindAbsGroup) (X : BlindAbsGSet G) (s : G .carrier) (x : X .fst .fst) : X .fst .fst
  ≔ permutation_action (X .fst) (X .snd .fst s) x

{` A G-set from an action map act satisfying (g·h)x = g(hx) and e x = x
   (helper used to build the G-sets that the text defines; the
   permutation of g is act g, with inverse act g⁻¹). `}
def blind_action_equiv (G : BlindAbsGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (am : (g h : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul g h) x) (act g (act h x)))
  (au : (x : X .fst) → Id (X .fst) (act (G .unit) x) x) (g : G .carrier) : Equiv (X .fst) (X .fst)
  ≔ quasi_inverse_equiv (X .fst) (X .fst) (act g) (act (G .inv g))
      (a ↦ concat (X .fst) (act (G .inv g) (act g a)) (act (G .mul (G .inv g) g) a) a
        (inverse (X .fst) (act (G .mul (G .inv g) g) a) (act (G .inv g) (act g a)) (am (G .inv g) g a))
        (concat (X .fst) (act (G .mul (G .inv g) g) a) (act (G .unit) a) a
          (refl ((k ↦ act k a) : G .carrier → X .fst) (blind_ag_linv G g)) (au a)))
      (b ↦ concat (X .fst) (act g (act (G .inv g) b)) (act (G .mul g (G .inv g)) b) b
        (inverse (X .fst) (act (G .mul g (G .inv g)) b) (act g (act (G .inv g) b)) (am g (G .inv g) b))
        (concat (X .fst) (act (G .mul g (G .inv g)) b) (act (G .unit) b) b
          (refl ((k ↦ act k b) : G .carrier → X .fst) (blind_ag_rinv G g)) (au b)))

def blind_gset_of_action (G : BlindAbsGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (am : (g h : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul g h) x) (act g (act h x)))
  (au : (x : X .fst) → Id (X .fst) (act (G .unit) x) x) : BlindAbsGSet G
  ≔ let perm : G .carrier → USym (permutation_group X)
        ≔ g ↦ permutation_symmetry X (blind_action_equiv G X act am au g) in
    (X, (perm,
     g h ↦ permutation_symmetries_ext X (perm (G .mul g h)) (usym_mul (permutation_group X) (perm g) (perm h))
       (x ↦ concat (X .fst) (act (G .mul g h) x) (act g (act h x))
          (permutation_action X (usym_mul (permutation_group X) (perm g) (perm h)) x)
          (am g h x)
          (inverse (X .fst) (permutation_action X (usym_mul (permutation_group X) (perm g) (perm h)) x)
            (act g (act h x)) (permutation_action_mul X (perm g) (perm h) x)))))

{` The principal G-torsor: (S, g ↦ (s ↦ μ(g,s))). `}
def blind_abs_principal (G : BlindAbsGroup) : BlindAbsGSet G
  ≔ blind_gset_of_action G (G .carrier, blind_ag_set G) (G .mul)
      (g h x ↦ inverse (G .carrier) (G .mul g (G .mul h x)) (G .mul (G .mul g h) x) (blind_ag_assoc G g h x))
      (blind_ag_lunit G)

{` The type of G-torsors: Σ (X : G-set) ‖P_G = X‖. `}
def BlindAbsTorsor (G : BlindAbsGroup) : Type
  ≔ Σ (BlindAbsGSet G) (X ↦ Mere (Id (BlindAbsGSet G) (blind_abs_principal G) X))

{` xca:absprtorsor: (S, s ↦ μ(g,s)) = (S, s ↦ μ(s, ι g)); the second datum
   is a G-set (its action laws are part of the claim). `}
def blind_xca_absprtorsor : Type
  ≔ (G : BlindAbsGroup)
    → Σ ((g h x : G .carrier) → Id (G .carrier) (G .mul x (G .inv (G .mul g h))) (G .mul (G .mul x (G .inv h)) (G .inv g))) (am ↦
      Σ ((x : G .carrier) → Id (G .carrier) (G .mul x (G .inv (G .unit))) x) (au ↦
        Id (BlindAbsGSet G) (blind_abs_principal G)
          (blind_gset_of_action G (G .carrier, blind_ag_set G) (g x ↦ G .mul x (G .inv g)) am au)))

{` Example (absgroup.tex 505): an abstr(G)-set is a set S with a function
   f : USym G → USym(Σ_S) such that f(pq) = f(p) f(q). `}
def blind_ex_abstr_gset_unfold : Type
  ≔ (G : Group)
    → Id Type (BlindAbsGSet (blind_abstr G))
        (Σ SetTypes (S ↦ Σ (USym G → USym (permutation_group S)) (f ↦
          (p q : USym G) → Id (USym (permutation_group S)) (f (usym_mul G p q))
            (usym_mul (permutation_group S) (f p) (f q)))))

{` "Clearly AbsGSet is a groupoid" (used by def:concr). `}
def blind_abs_gset_groupoid (G : BlindAbsGroup) : isGroupoid (BlindAbsGSet G)
  ≔ hlevel_to_groupoid (BlindAbsGSet G)
      (hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes (X ↦ BlindAbsHom G (blind_perm_group X))
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (X ↦ groupoid_to_hlevel (BlindAbsHom G (blind_perm_group X))
          (set_is_groupoid (BlindAbsHom G (blind_perm_group X)) (blind_abshom_set G (blind_perm_group X)))))

{` def:concr: concr(G) is the group classified by (Torsor_G, P_G)
   (the torsor type is literally the component of P_G in AbsGSet). `}
def blind_concr (G : BlindAbsGroup) : Group
  ≔ mkgroup (component_pcg (BlindAbsGSet G) (blind_abs_gset_groupoid G) (blind_abs_principal G))

def blind_concr_carrier (G : BlindAbsGroup) : Id Type (BG (blind_concr G) .carrier) (BlindAbsTorsor G)
  ≔ refl (BlindAbsTorsor G)

{` ex:BqG. For z : BG, the set (z = sh_G) with post_z(g)(p) ≔ g p
   (= concat p g) is an abstr(G)-set. `}
def blind_bq_set (G : Group) (z : BG G .carrier) : SetTypes
  ≔ (Id (BG G .carrier) z (shape G), bg_groupoid G z (shape G))

def blind_post (G : Group) (z : BG G .carrier) (g : USym G) (p : Id (BG G .carrier) z (shape G))
  : Id (BG G .carrier) z (shape G)
  ≔ concat (BG G .carrier) z (shape G) (shape G) p g

def blind_bq_gset (G : Group) (z : BG G .carrier) : BlindAbsGSet (blind_abstr G)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    blind_gset_of_action (blind_abstr G) (blind_bq_set G z) (blind_post G z)
      (g h p ↦ inverse (Id A z a) (concat A z a a (concat A z a a p h) g) (concat A z a a p (concat A a a a h g))
        (concat_assoc A z a a a p h g))
      (p ↦ concat_p1 A z a p)

{` "For z ≡ sh_G this abstr(G)-set is definitionally the principal torsor." `}
def blind_ex_bqg_principal : Type
  ≔ (G : Group) → Id (BlindAbsGSet (blind_abstr G)) (blind_bq_gset G (shape G)) (blind_abs_principal (blind_abstr G))

def blind_bq_gset_principal (G : Group)
  : Id (BlindAbsGSet (blind_abstr G)) (blind_bq_gset G (shape G)) (blind_abs_principal (blind_abstr G))
  ≔ refl (blind_abs_principal (blind_abstr G))

def blind_bq (G : Group) (z : BG G .carrier) : BlindAbsTorsor (blind_abstr G)
  ≔ (blind_bq_gset G z,
     mere_rec (Id (BG G .carrier) (shape G) z)
       (Mere (Id (BlindAbsGSet (blind_abstr G)) (blind_abs_principal (blind_abstr G)) (blind_bq_gset G z)))
       (mere_isprop (Id (BlindAbsGSet (blind_abstr G)) (blind_abs_principal (blind_abstr G)) (blind_bq_gset G z)))
       (p ↦ mere (Id (BlindAbsGSet (blind_abstr G)) (blind_abs_principal (blind_abstr G)) (blind_bq_gset G z))
         (map_path (BG G .carrier) (BlindAbsGSet (blind_abstr G)) (blind_bq_gset G) (shape G) z p))
       (bg_connected G .snd (shape G) z))

{` Bq_G : BG →* (Torsor_abstr(G), P), pointed by reflexivity (of the
   underlying G-sets). `}
def blind_bq_pointed (G : Group) : BookPointedMap (BG G) (BG (blind_concr (blind_abstr G)))
  ≔ (blind_bq G,
     component_path (BlindAbsGSet (blind_abstr G)) (blind_abs_principal (blind_abstr G))
       (component_point (BlindAbsGSet (blind_abstr G)) (blind_abs_principal (blind_abstr G)))
       (blind_bq G (shape G)) (refl (blind_abs_principal (blind_abstr G))))

{` ft:shG=z: the set (sh_G = z) with preinv_z(g)(r) ≔ r g⁻¹ (= concat g⁻¹ r)
   is an abstr(G)-set; for z ≡ sh_G it can be identified with the principal torsor. `}
def blind_ft_shg_z : Type
  ≔ (G : Group)
    → let A ≔ BG G .carrier in let a ≔ shape G in
      let act : (z : A) → USym G → Id A a z → Id A a z ≔ z g r ↦ concat A a a z (inverse A a a g) r in
      Σ ((z : A) (g h : USym G) (r : Id A a z) → Id (Id A a z) (act z (usym_mul G g h) r) (act z g (act z h r))) (am ↦
      Σ ((z : A) (r : Id A a z) → Id (Id A a z) (act z (usym_unit G) r) r) (au ↦
        Id (BlindAbsGSet (blind_abstr G))
          (blind_gset_of_action (blind_abstr G) (Id A a a, bg_groupoid G a a) (act a) (am a) (au a))
          (blind_abs_principal (blind_abstr G))))

{` def:qG-concr-abstr. `}
def blind_qG (G : Group) : GroupHom G (blind_concr (blind_abstr G))
  ≔ mkhom G (blind_concr (blind_abstr G)) (blind_bq_pointed G)

{` lem:Groupsareidentitytypes. `}
def blind_lem_groups_are_identity_types : Type
  ≔ (G : Group) → IsGroupIso G (blind_concr (blind_abstr G)) (blind_qG G)

{` thm:Groupsareidentitytypes. `}
def blind_thm_groups_are_identity_types : Type ≔ BookIsEquiv Group BlindAbsGroup blind_abstr

{` ft:abstract-Cayley: every abstract group embeds into the abstract
   permutation group of its underlying set. `}
def blind_ft_abstract_cayley : Type
  ≔ (G : BlindAbsGroup)
    → Σ (BlindAbsHom G (blind_perm_group (G .carrier, blind_ag_set G))) (f ↦
        IsEmbedding (G .carrier) (USym (permutation_group (G .carrier, blind_ag_set G))) (f .fst))
