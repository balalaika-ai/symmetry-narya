export "842-wedge-pointed-universal-property"
export "410-pointed-connected-groupoids"

{` Chapter 8 (congp.tex), def:sumofgroup (congp.tex:571) and
   lem:sumofgroupsISsum (congp.tex:577).

   The book defines G1 ∨ G2 ≔ Aut_{A1∨A2}(a12) for G_i = Aut_{A_i}(a_i).
   automorphism_group (module 400) needs the ambient type to be a groupoid,
   and the wedge is a groupoid only by lem:wedgeofgpoidisgpoid (decidable
   groups, modules 845-848) or by results the book cites without proof.  So
   the groupoid property of the wedge is an explicit hypothesis hW here:
   - wedge_automorphism_group A1 A2 W hW is the literal Aut_{A1∨A2}(a12)
     for arbitrary pointed types (A_i, a_i);
   - sum_of_groups G1 G2 W hW ≔ mkgroup (A1∨A2, a12) for A_i = BG_i (the
     wedge of connected types is connected, wedge_connected), so that
     B(G1∨G2) ≡ (A1∨A2, a12) judgmentally; sum_of_groups_aut_path identifies
     it with the literal Aut_{BG1∨BG2}(a12).
   The structure maps i1, i2 are the homomorphisms classified by the pointed
   structure maps (i1, refl) and (i2, g) of module 841; on symmetries they
   are i1^g and i2^g.  decidable_sum_of_groups (module 848) discharges hW
   for decidable groups.

   lem:sumofgroupsISsum is the special case of lem:univvee with B ≔ BG:
   restriction along the structure maps, Hom(G1∨G2, G) → Hom(G1, G) ×
   Hom(G2, G), is an equivalence; its inverse is sum_of_groups_hom_extend. `}

def wedge_automorphism_group (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (hW : isGroupoid (W .carrier)) : Group
  ≔ automorphism_group (W .carrier) hW (wedge_point A1 A2 W)

def sum_of_groups_pcg (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  : PointedConnectedGroupoid
  ≔ (W .carrier, W .incl1 (shape G1), wedge_connected (BG G1) (BG G2) W (bg_connected G1) (bg_connected G2), hW)

{` def:sumofgroup: G1 ∨ G2. `}
def sum_of_groups (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier)) : Group
  ≔ mkgroup (sum_of_groups_pcg G1 G2 W hW)

def sum_of_groups_classifying (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  : Id Pointed (BG (sum_of_groups G1 G2 W hW)) (wedge_pointed (BG G1) (BG G2) W)
  ≔ refl (wedge_pointed (BG G1) (BG G2) W)

{` G1 ∨ G2 is the book's Aut_{BG1∨BG2}(a12). `}
def sum_of_groups_aut_path (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  : Id Group (sum_of_groups G1 G2 W hW) (wedge_automorphism_group (BG G1) (BG G2) W hW)
  ≔ pcg_automorphism_path (sum_of_groups_pcg G1 G2 W hW)

{` The structure maps i1 : G1 → G1 ∨ G2 and i2 : G2 → G1 ∨ G2. `}
def sum_of_groups_incl1 (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  : GroupHom G1 (sum_of_groups G1 G2 W hW)
  ≔ mkhom G1 (sum_of_groups G1 G2 W hW) (wedge_incl1_pointed (BG G1) (BG G2) W)

def sum_of_groups_incl2 (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  : GroupHom G2 (sum_of_groups G1 G2 W hW)
  ≔ mkhom G2 (sum_of_groups G1 G2 W hW) (wedge_incl2_pointed (BG G1) (BG G2) W)

def sum_of_groups_incl1_usym (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (g : USym G1)
  : Id (USym (sum_of_groups G1 G2 W hW)) (usym_hom G1 (sum_of_groups G1 G2 W hW) (sum_of_groups_incl1 G1 G2 W hW) g)
      (wedge_loop1 (BG G1) (BG G2) W g)
  ≔ inverse (USym (sum_of_groups G1 G2 W hW)) (wedge_loop1 (BG G1) (BG G2) W g)
      (usym_hom G1 (sum_of_groups G1 G2 W hW) (sum_of_groups_incl1 G1 G2 W hW) g)
      (wedge_loop1_loops_map (BG G1) (BG G2) W g)

def sum_of_groups_incl2_usym (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (g : USym G2)
  : Id (USym (sum_of_groups G1 G2 W hW)) (usym_hom G2 (sum_of_groups G1 G2 W hW) (sum_of_groups_incl2 G1 G2 W hW) g)
      (wedge_loop2 (BG G1) (BG G2) W g)
  ≔ refl (wedge_loop2 (BG G1) (BG G2) W g)

{` lem:sumofgroupsISsum: restriction along the structure maps. `}
def sum_of_groups_restrict (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f : GroupHom (sum_of_groups G1 G2 W hW) G) : Product (GroupHom G1 G) (GroupHom G2 G)
  ≔ (group_hom_compose G1 (sum_of_groups G1 G2 W hW) G (sum_of_groups_incl1 G1 G2 W hW) f,
     group_hom_compose G2 (sum_of_groups G1 G2 W hW) G (sum_of_groups_incl2 G1 G2 W hW) f)

def sum_of_groups_hom_equiv (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) : Equiv (GroupHom (sum_of_groups G1 G2 W hW) G) (Product (GroupHom G1 G) (GroupHom G2 G))
  ≔ let S ≔ sum_of_groups G1 G2 W hW in
    let P1 ≔ BookPointedMap (BG G1) (BG G) in let P2 ≔ BookPointedMap (BG G2) (BG G) in
    let H ≔ Product (GroupHom G1 G) (GroupHom G2 G) in
    equiv_change_map (GroupHom S G) H
      (compose_equiv (GroupHom S G) (BookPointedMap (BG S) (BG G)) H
        (group_hom_classifying_equiv S G)
        (compose_equiv (BookPointedMap (BG S) (BG G)) (Product P1 P2) H
          (wedge_pointed_universal_property (BG G1) (BG G2) W (BG G))
          (product_equiv P1 P2 (GroupHom G1 G) (GroupHom G2 G)
            (canonical_inverse_equiv (GroupHom G1 G) P1 (group_hom_classifying_equiv G1 G))
            (canonical_inverse_equiv (GroupHom G2 G) P2 (group_hom_classifying_equiv G2 G)))))
      (sum_of_groups_restrict G1 G2 W hW G)
      (f ↦ refl (sum_of_groups_restrict G1 G2 W hW G f))

def sum_of_groups_hom_book_equiv (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group)
  : BookIsEquiv (GroupHom (sum_of_groups G1 G2 W hW) G) (Product (GroupHom G1 G) (GroupHom G2 G))
      (sum_of_groups_restrict G1 G2 W hW G)
  ≔ book_equivalence (GroupHom (sum_of_groups G1 G2 W hW) G) (Product (GroupHom G1 G) (GroupHom G2 G))
      (sum_of_groups_hom_equiv G1 G2 W hW G) .equiv

{` The inverse: the homomorphism with prescribed restrictions f1, f2. `}
def sum_of_groups_hom_extend (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f1 : GroupHom G1 G) (f2 : GroupHom G2 G) : GroupHom (sum_of_groups G1 G2 W hW) G
  ≔ mkhom (sum_of_groups G1 G2 W hW) G (wedge_pointed_extend (BG G1) (BG G2) W (BG G) (hom_B G1 G f1) (hom_B G2 G f2))

def sum_of_groups_restrict_extend (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f1 : GroupHom G1 G) (f2 : GroupHom G2 G)
  : Id (Product (GroupHom G1 G) (GroupHom G2 G))
      (sum_of_groups_restrict G1 G2 W hW G (sum_of_groups_hom_extend G1 G2 W hW G f1 f2)) (f1, f2)
  ≔ refl ((u ↦ (mkhom G1 G (u .fst), mkhom G2 G (u .snd)))
        : Product (BookPointedMap (BG G1) (BG G)) (BookPointedMap (BG G2) (BG G)) → Product (GroupHom G1 G) (GroupHom G2 G))
      (wedge_restrict_extend (BG G1) (BG G2) W (BG G) (hom_B G1 G f1) (hom_B G2 G f2))

def sum_of_groups_extend_restrict (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f : GroupHom (sum_of_groups G1 G2 W hW) G)
  : Id (GroupHom (sum_of_groups G1 G2 W hW) G)
      (sum_of_groups_hom_extend G1 G2 W hW G (sum_of_groups_restrict G1 G2 W hW G f .fst)
        (sum_of_groups_restrict G1 G2 W hW G f .snd)) f
  ≔ refl (mkhom (sum_of_groups G1 G2 W hW) G)
      (wedge_extend_restrict (BG G1) (BG G2) W (BG G) (hom_B (sum_of_groups G1 G2 W hW) G f))

{` On symmetries, the extension sends i1^g(g) to f1(g) and i2^g(g) to f2(g). `}
def sum_of_groups_extend_loop1 (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f1 : GroupHom G1 G) (f2 : GroupHom G2 G) (g : USym G1)
  : Id (USym G) (usym_hom (sum_of_groups G1 G2 W hW) G (sum_of_groups_hom_extend G1 G2 W hW G f1 f2)
        (wedge_loop1 (BG G1) (BG G2) W g))
      (usym_hom G1 G f1 g)
  ≔ let S ≔ sum_of_groups G1 G2 W hW in
    let F ≔ sum_of_groups_hom_extend G1 G2 W hW G f1 f2 in
    let i1 ≔ sum_of_groups_incl1 G1 G2 W hW in
    calc
      usym_hom S G F (wedge_loop1 (BG G1) (BG G2) W g)
      = usym_hom S G F (usym_hom G1 S i1 g)
        by refl (usym_hom S G F) (wedge_loop1_loops_map (BG G1) (BG G2) W g)
      = usym_hom G1 G (group_hom_compose G1 S G i1 F) g
        by inverse (USym G) (usym_hom G1 G (group_hom_compose G1 S G i1 F) g) (usym_hom S G F (usym_hom G1 S i1 g))
          (loops_map_compose_pointwise (BG G1) (BG S) (BG G) (hom_B G1 S i1) (hom_B S G F) g)
      = usym_hom G1 G f1 g
        by refl ((h ↦ usym_hom G1 G h g) : GroupHom G1 G → USym G)
          (sum_of_groups_restrict_extend G1 G2 W hW G f1 f2 .fst) ∎

def sum_of_groups_extend_loop2 (G1 G2 : Group) (W : WedgeSignature (BG G1) (BG G2)) (hW : isGroupoid (W .carrier))
  (G : Group) (f1 : GroupHom G1 G) (f2 : GroupHom G2 G) (g : USym G2)
  : Id (USym G) (usym_hom (sum_of_groups G1 G2 W hW) G (sum_of_groups_hom_extend G1 G2 W hW G f1 f2)
        (wedge_loop2 (BG G1) (BG G2) W g))
      (usym_hom G2 G f2 g)
  ≔ let S ≔ sum_of_groups G1 G2 W hW in
    let F ≔ sum_of_groups_hom_extend G1 G2 W hW G f1 f2 in
    let i2 ≔ sum_of_groups_incl2 G1 G2 W hW in
    calc
      usym_hom S G F (wedge_loop2 (BG G1) (BG G2) W g)
      = usym_hom G2 G (group_hom_compose G2 S G i2 F) g
        by inverse (USym G) (usym_hom G2 G (group_hom_compose G2 S G i2 F) g) (usym_hom S G F (usym_hom G2 S i2 g))
          (loops_map_compose_pointwise (BG G2) (BG S) (BG G) (hom_B G2 S i2) (hom_B S G F) g)
      = usym_hom G2 G f2 g
        by refl ((h ↦ usym_hom G2 G h g) : GroupHom G2 G → USym G)
          (sum_of_groups_restrict_extend G1 G2 W hW G f1 f2 .snd) ∎
