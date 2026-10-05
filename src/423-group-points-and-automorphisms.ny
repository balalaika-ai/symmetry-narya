export "410-pointed-connected-groupoids"

{` Chapter 4, the exercise at group.tex:779 and xca:typegroupisgroupoid. `}

{` xca (group.tex:779): for mkgroup(A, a) and any b : A, the groups
   mkgroup(A, a) and mkgroup(A, b) are merely identical; similarly for
   ∞-groups (module 485). `}
def mkgroup_points_merely_equal (A : Type) (a b : A) (c : Connected A) (g : isGroupoid A)
  : Mere (Id Group (mkgroup (A, a, c, g)) (mkgroup (A, b, c, g)))
  ≔ mere_rec (Id A a b) (Mere (Id Group (mkgroup (A, a, c, g)) (mkgroup (A, b, c, g))))
      (mere_isprop (Id Group (mkgroup (A, a, c, g)) (mkgroup (A, b, c, g))))
      (p ↦ mere (Id Group (mkgroup (A, a, c, g)) (mkgroup (A, b, c, g)))
        (refl ((x ↦ mkgroup (A, x, c, g)) : A → Group) p))
      (c .snd a b)

def infty_group_points_merely_equal (A : Type) (a b : A) (c : Connected A)
  : Mere (Id InftyGroup (mk_infty_group (A, a, c)) (mk_infty_group (A, b, c)))
  ≔ mere_rec (Id A a b) (Mere (Id InftyGroup (mk_infty_group (A, a, c)) (mk_infty_group (A, b, c))))
      (mere_isprop (Id InftyGroup (mk_infty_group (A, a, c)) (mk_infty_group (A, b, c))))
      (p ↦ mere (Id InftyGroup (mk_infty_group (A, a, c)) (mk_infty_group (A, b, c)))
        (refl ((x ↦ mk_infty_group (A, x, c)) : A → InftyGroup) p))
      (c .snd a b)

{` xca:typegroupisgroupoid: G = H is a set (group_paths_set) and Group is a
   groupoid (group_groupoid), so Aut(G) ≔ Aut_Group(G) is a group
   (group_aut, module 402). Its symmetries are the identifications G = G,
   equivalently the automorphisms (isomorphisms G → G) of G. `}
def group_aut_usym_paths (G : Group) : Equiv (USym (group_aut G)) (Id Group G G)
  ≔ automorphism_group_usym_equiv Group group_groupoid G

def group_aut_usym_isos (G : Group) : Equiv (USym (group_aut G)) (GroupIso G G)
  ≔ compose_equiv (USym (group_aut G)) (Id Group G G) (GroupIso G G) (group_aut_usym_paths G)
      (group_path_iso_equiv G G)

