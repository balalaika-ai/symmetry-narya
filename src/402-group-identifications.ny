export "401-group-homomorphisms"

{` Identifications of groups (rem:aut, remark:groupsasunivalenttype,
   xca:typegroupisgroupoid). `}

{` Identifications of groups are identifications of classifying types in
   U^{=1}_* (the wrapper is a one-field record, so this is eta). `}
def group_path_classifying_equiv (G H : Group)
  : Equiv (Id Group G H) (Id PointedConnectedGroupoid (group_B G) (group_B H))
  ≔ quasi_inverse_equiv (Id Group G H) (Id PointedConnectedGroupoid (group_B G) (group_B H))
      (p ↦ p .classifying) (q ↦ (classifying ≔ q)) (p ↦ refl p) (q ↦ refl q)

{` U^{=1}_* is a subtype of U_* (rem:aut): connectedness and being a
   groupoid are propositions, so paths of pointed connected groupoids are
   paths of the underlying pointed types (lem:subtype-eq-=). `}
def pcg_connected_pathover (X Y : PointedConnectedGroupoid) (s : Id Type (X .carrier) (Y .carrier))
  : isContr (Id Connected s (X .connected) (Y .connected))
  ≔ pathover_hlevel zero. Type Connected (A ↦ prop_to_hlevel_one (Connected A) (connected_prop A))
      (X .carrier) (Y .carrier) s (X .connected) (Y .connected)

def pcg_groupoid_pathover (X Y : PointedConnectedGroupoid) (s : Id Type (X .carrier) (Y .carrier))
  : isContr (Id isGroupoid s (X .groupoid) (Y .groupoid))
  ≔ pathover_hlevel zero. Type isGroupoid (A ↦ prop_to_hlevel_one (isGroupoid A) (isgroupoid_isprop A))
      (X .carrier) (Y .carrier) s (X .groupoid) (Y .groupoid)

def pcg_path_pointed_equiv (X Y : PointedConnectedGroupoid)
  : Equiv (Id PointedConnectedGroupoid X Y) (Id Pointed (pcg_pointed X) (pcg_pointed Y))
  ≔ quasi_inverse_equiv (Id PointedConnectedGroupoid X Y) (Id Pointed (pcg_pointed X) (pcg_pointed Y))
      (r ↦ (r .carrier, r .point))
      (s ↦ (s .carrier, s .point, pcg_connected_pathover X Y (s .carrier) .center,
        pcg_groupoid_pathover X Y (s .carrier) .center))
      (r ↦ (refl (r .carrier), refl (r .point),
        inverse (Id Connected (r .carrier) (X .connected) (Y .connected)) (r .connected)
          (pcg_connected_pathover X Y (r .carrier) .center)
          (pcg_connected_pathover X Y (r .carrier) .contract (r .connected)),
        inverse (Id isGroupoid (r .carrier) (X .groupoid) (Y .groupoid)) (r .groupoid)
          (pcg_groupoid_pathover X Y (r .carrier) .center)
          (pcg_groupoid_pathover X Y (r .carrier) .contract (r .groupoid))))
      (s ↦ refl s)

def book_pointed_equiv_group_iso_equiv (G H : Group)
  : Equiv (BookPointedEquiv (BG G) (BG H)) (GroupIso G H)
  ≔ quasi_inverse_equiv (BookPointedEquiv (BG G) (BG H)) (GroupIso G H)
      (u ↦ (mkhom G H (u .fst), u .snd)) (w ↦ (hom_B G H (w .fst), w .snd))
      (u ↦ refl u) (w ↦ refl w)

{` remark:groupsasunivalenttype: (G = H) ≃ Iso(G, H), via xca:pointedequiv. `}
def group_path_iso_equiv (G H : Group) : Equiv (Id Group G H) (GroupIso G H)
  ≔ compose_equiv (Id Group G H) (Id PointedConnectedGroupoid (group_B G) (group_B H)) (GroupIso G H)
      (group_path_classifying_equiv G H)
      (compose_equiv (Id PointedConnectedGroupoid (group_B G) (group_B H)) (Id Pointed (BG G) (BG H)) (GroupIso G H)
        (pcg_path_pointed_equiv (group_B G) (group_B H))
        (compose_equiv (Id Pointed (BG G) (BG H)) (BookPointedEquiv (BG G) (BG H)) (GroupIso G H)
          (pointed_path_equiv (BG G) (BG H)) (book_pointed_equiv_group_iso_equiv G H)))

{` The identification of groups induced by an isomorphism. `}
def group_path_from_iso (G H : Group) (f : GroupIso G H) : Id Group G H
  ≔ equiv_inverse_map (Id Group G H) (GroupIso G H) (group_path_iso_equiv G H) f

def group_path_from_pointed_equiv (G H : Group) (f : BookPointedEquiv (BG G) (BG H)) : Id Group G H
  ≔ group_path_from_iso G H (mkhom G H (f .fst), f .snd)

{` xca:typegroupisgroupoid: G = H is a set and Group is a groupoid. `}
def group_paths_set (G H : Group) : isSet (Id Group G H)
  ≔ hlevel_two_to_set (Id Group G H)
      (hlevel_equiv (suc. (suc. zero.)) (GroupIso G H) (Id Group G H)
        (canonical_inverse_equiv (Id Group G H) (GroupIso G H) (group_path_iso_equiv G H))
        (set_to_hlevel_two (GroupIso G H) (group_iso_set G H)))

def group_groupoid : isGroupoid Group ≔ G H ↦ group_paths_set G H

{` xca:typegroupisgroupoid: Aut(G) ≔ Aut_Group(G), the component of Group at G. `}
def group_aut (G : Group) : Group ≔ automorphism_group Group group_groupoid G
