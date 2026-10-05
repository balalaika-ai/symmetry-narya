export "504-torsors"

{` Chapter 5, sec:fixpts-orbits, first part: truncated identifications in
   the action type (rem:path-in-action-type), identifications of orbits
   ([u]_0 = [v]_0 ⇔ ‖u = v‖), membership in an orbit (O(u) ⇔ O = [u]_0),
   surjectivity of [-]_0, of [-] and of x ↦ (sh_G, x) (ft:orbit-surj), and
   the equivalent forms of [x] = [y] (rem:equivalents-of-[x]=[y]). `}

{` rem:path-in-action-type, "which also goes for their propositional
   truncations": ‖u = v‖ ≃ ‖Σ_{g : u.1 = v.1} (g · u.2 = v.2)‖. `}
def action_type_mere_path_equiv (G : Group) (X : GSet G) (u v : ActionType G X)
  : Equiv (Mere (Id (ActionType G X) u v)) (Mere (ActionTypePath G X u v))
  ≔ let T ≔ ActionType G X in
    let e ≔ action_type_path_equiv G X u v in
    iff_equiv (Mere (Id T u v)) (Mere (ActionTypePath G X u v))
      (mere_isprop (Id T u v)) (mere_isprop (ActionTypePath G X u v))
      (trunc_map native_truncation (Id T u v) (ActionTypePath G X u v) (e .map))
      (trunc_map native_truncation (ActionTypePath G X u v) (Id T u v)
        (equiv_inverse_map (Id T u v) (ActionTypePath G X u v) e))

{` The same in the book's pointwise notation (also the footnote in the
   introduction of sec:fixpts-orbits): ‖(z, x) = (w, y)‖ holds iff there
   exists g : z = w with g · x = y. `}
def action_type_mere_path_exists (G : Group) (X : GSet G) (z w : BG G .carrier) (x : X z .fst) (y : X w .fst)
  : Equiv (Mere (Id (ActionType G X) (z, x) (w, y)))
      (Mere (Σ (Id (BG G .carrier) z w) (g ↦ Id (X w .fst) (gset_act G X z w g x) y)))
  ≔ action_type_mere_path_equiv G X (z, x) (w, y)

{` Backward transport along an identification of propositions. `}
def orbit_prop_path_backward (P Q : PropTypes) (e : Id PropTypes P Q) (q : Q .fst) : P .fst
  ≔ transport PropTypes (R ↦ R .fst) Q P (inverse PropTypes P Q e) q

{` [u]_0 = [v]_0 ⇔ ‖u = v‖ (the observation before lem:X/G=setTruncX_hG). `}
def orbit_map_path_to_mere (G : Group) (X : GSet G) (u v : ActionType G X)
  (p : Id (Orbits G X) (orbit_map G X u) (orbit_map G X v)) : Mere (Id (ActionType G X) u v)
  ≔ let T ≔ ActionType G X in
    let e1 : Id (X (v .fst) .fst → PropTypes) (orbit_subset G X u (v .fst)) (orbit_subset G X v (v .fst))
      ≔ happly (BG G .carrier) (z ↦ X z .fst → PropTypes) (orbit_subset G X u) (orbit_subset G X v) (p .fst)
          (v .fst) in
    let e2 : Id PropTypes (orbit_subset G X u (v .fst) (v .snd)) (orbit_subset G X v (v .fst) (v .snd))
      ≔ happly (X (v .fst) .fst) (_ ↦ PropTypes) (orbit_subset G X u (v .fst)) (orbit_subset G X v (v .fst)) e1
          (v .snd) in
    orbit_prop_path_backward (orbit_subset G X u (v .fst) (v .snd)) (orbit_subset G X v (v .fst) (v .snd)) e2
      (mere (Id T v v) (refl v))

def orbit_map_path_from_mere (G : Group) (X : GSet G) (u v : ActionType G X)
  (r : Mere (Id (ActionType G X) u v)) : Id (Orbits G X) (orbit_map G X u) (orbit_map G X v)
  ≔ let T ≔ ActionType G X in
    mere_rec (Id T u v) (Id (Orbits G X) (orbit_map G X u) (orbit_map G X v))
      (orbits_set G X (orbit_map G X u) (orbit_map G X v))
      (q ↦ map_path T (Orbits G X) (orbit_map G X) u v q) r

def orbit_map_path_equiv (G : Group) (X : GSet G) (u v : ActionType G X)
  : Equiv (Id (Orbits G X) (orbit_map G X u) (orbit_map G X v)) (Mere (Id (ActionType G X) u v))
  ≔ iff_equiv (Id (Orbits G X) (orbit_map G X u) (orbit_map G X v)) (Mere (Id (ActionType G X) u v))
      (orbits_set G X (orbit_map G X u) (orbit_map G X v)) (mere_isprop (Id (ActionType G X) u v))
      (orbit_map_path_to_mere G X u v) (orbit_map_path_from_mere G X u v)

{` Membership of u = (z, x) in an orbit O, the book's O(u) for O(z)(x)
   (footnote in the paragraph after rem:equivalents-of-[x]=[y]). `}
def OrbitMember (G : Group) (X : GSet G) (O : Orbits G X) (u : ActionType G X) : Type
  ≔ O .fst (u .fst) (u .snd) .fst

def orbit_member_prop (G : Group) (X : GSet G) (O : Orbits G X) (u : ActionType G X)
  : isProp (OrbitMember G X O u)
  ≔ O .fst (u .fst) (u .snd) .snd

{` "If O(u) and O(v), then ‖u = v‖ by the transitivity of X_O": the action
   type of X_O is connected (lem:conistrans) and maps to X_hG. `}
def orbit_members_merely_equal (G : Group) (X : GSet G) (O : Orbits G X) (u v : ActionType G X)
  (hu : OrbitMember G X O u) (hv : OrbitMember G X O v) : Mere (Id (ActionType G X) u v)
  ≔ let Y ≔ gsubset_gset G X (O .fst) in
    let TY ≔ ActionType G Y in
    let u' : TY ≔ (u .fst, (u .snd, hu)) in
    let v' : TY ≔ (v .fst, (v .snd, hv)) in
    trunc_map native_truncation (Id TY u' v') (Id (ActionType G X) u v)
      (map_path TY (ActionType G X) (t ↦ (t .fst, t .snd .fst)) u' v')
      (transitive_action_type_connected G Y (O .snd) .snd u' v')

{` O(u) ⇒ O = [u]_0. `}
def orbit_path_of_member (G : Group) (X : GSet G) (O : Orbits G X) (u : ActionType G X)
  (hu : OrbitMember G X O u) : Id (Orbits G X) O (orbit_map G X u)
  ≔ let T ≔ ActionType G X in
    orbit_path G X O (orbit_map G X u)
      (funext (BG G .carrier) (z ↦ X z .fst → PropTypes) (O .fst) (orbit_subset G X u)
        (z ↦ funext (X z .fst) (_ ↦ PropTypes) (O .fst z) (orbit_subset G X u z)
          (x ↦ proposition_extensionality (O .fst z x) (orbit_subset G X u z x)
            (o ↦ orbit_members_merely_equal G X O u (z, x) hu o)
            (r ↦ mere_rec (Id T u (z, x)) (O .fst z x .fst) (O .fst z x .snd)
              (q ↦ transport T (w ↦ OrbitMember G X O w) u (z, x) q hu) r))))

{` O = [u]_0 ⇒ O(u). `}
def orbit_member_of_path (G : Group) (X : GSet G) (O : Orbits G X) (u : ActionType G X)
  (p : Id (Orbits G X) O (orbit_map G X u)) : OrbitMember G X O u
  ≔ transport (Orbits G X) (Q ↦ OrbitMember G X Q u) (orbit_map G X u) O
      (inverse (Orbits G X) O (orbit_map G X u) p) (mere (Id (ActionType G X) u u) (refl u))

{` The paragraph after rem:equivalents-of-[x]=[y]: "O(u) holds if and only
   if O = [u]_0, for all u : X_hG". `}
def orbit_member_path_equiv (G : Group) (X : GSet G) (O : Orbits G X) (u : ActionType G X)
  : Equiv (OrbitMember G X O u) (Id (Orbits G X) O (orbit_map G X u))
  ≔ iff_equiv (OrbitMember G X O u) (Id (Orbits G X) O (orbit_map G X u))
      (orbit_member_prop G X O u) (orbits_set G X O (orbit_map G X u))
      (orbit_path_of_member G X O u) (orbit_member_of_path G X O u)

{` Every orbit merely has a member in the underlying set: the transitivity
   of X_O provides a point x : X_O(sh_G). `}
def orbit_has_base_member (G : Group) (X : GSet G) (O : Orbits G X)
  : Mere (Σ (gset_underlying G X) (x ↦ OrbitMember G X O (shape G, x)))
  ≔ let Y ≔ gsubset_gset G X (O .fst) in
    let S ≔ gset_underlying G Y in
    let Goal ≔ Σ (gset_underlying G X) (x ↦ OrbitMember G X O (shape G, x)) in
    mere_rec (Σ S (x ↦ (y : S) → Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G Y g y)))))
      (Mere Goal) (mere_isprop Goal)
      (a ↦ mere Goal (a .fst .fst, a .fst .snd))
      (O .snd)

{` lem:X/G=setTruncX_hG, first part: [-]_0 : X_hG → X/G is surjective. `}
def orbit_map_surjective (G : Group) (X : GSet G)
  : Surjective (ActionType G X) (Orbits G X) (orbit_map G X)
  ≔ O ↦
    let F ≔ BookFiber (ActionType G X) (Orbits G X) (orbit_map G X) O in
    mere_rec (Σ (gset_underlying G X) (x ↦ OrbitMember G X O (shape G, x))) (Mere F) (mere_isprop F)
      (a ↦ mere F ((shape G, a .fst), orbit_path_of_member G X O (shape G, a .fst) (a .snd)))
      (orbit_has_base_member G X O)

{` cor:orbit-equiv: [-] : X(sh_G) → X/G, [x] = [(sh_G, x)]_0, is surjective. `}
def orbit_of_point_surjective (G : Group) (X : GSet G)
  : Surjective (gset_underlying G X) (Orbits G X) (orbit_of_point G X)
  ≔ O ↦
    let F ≔ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O in
    mere_rec (Σ (gset_underlying G X) (x ↦ OrbitMember G X O (shape G, x))) (Mere F) (mere_isprop F)
      (a ↦ mere F (a .fst, orbit_path_of_member G X O (shape G, a .fst) (a .snd)))
      (orbit_has_base_member G X O)

{` ft:orbit-surj: the triangle X(sh_G) → X_hG → X/G commutes by definition
   and x ↦ (sh_G, x) is surjective (BG is connected). `}
def action_type_base_point (G : Group) (X : GSet G) (x : gset_underlying G X) : ActionType G X
  ≔ (shape G, x)

def orbit_of_point_factors (G : Group) (X : GSet G)
  : Id (gset_underlying G X → Orbits G X) (orbit_of_point G X)
      (x ↦ orbit_map G X (action_type_base_point G X x))
  ≔ refl (orbit_of_point G X)

def action_type_base_point_surjective (G : Group) (X : GSet G)
  : Surjective (gset_underlying G X) (ActionType G X) (action_type_base_point G X)
  ≔ u ↦
    let F ≔ BookFiber (gset_underlying G X) (ActionType G X) (action_type_base_point G X) u in
    mere_rec (Id (BG G .carrier) (u .fst) (shape G)) (Mere F) (mere_isprop F)
      (p ↦ let x ≔ gset_act G X (u .fst) (shape G) p (u .snd) in
        mere F (x, action_type_path G X (u .fst) (shape G) (u .snd) x p (refl x)))
      (bg_connected G .snd (u .fst) (shape G))

{` rem:equivalents-of-[x]=[y]. The relation ∃_{g : USym G} (g · x = y). `}
def OrbitRelation (G : Group) (X : GSet G) (x y : gset_underlying G X) : Type
  ≔ Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) y))

{` [x] = [y] ≃ ‖(sh_G, x) = (sh_G, y)‖. `}
def orbit_point_path_mere_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (Mere (Id (ActionType G X) (shape G, x) (shape G, y)))
  ≔ orbit_map_path_equiv G X (shape G, x) (shape G, y)

{` cor:orbit-equiv (first statement): [x] = [y] ≃ ∃_{g : USym G} (g · x = y). `}
def orbit_point_path_exists_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y)) (OrbitRelation G X x y)
  ≔ compose_equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (Mere (Id (ActionType G X) (shape G, x) (shape G, y))) (OrbitRelation G X x y)
      (orbit_point_path_mere_equiv G X x y)
      (action_type_mere_path_equiv G X (shape G, x) (shape G, y))

{` [x] = [y] ≃ ([x](sh_G) = [y](sh_G)) as subsets of X(sh_G). `}
def orbit_point_path_subset_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (Id (gset_underlying G X → PropTypes) (orbit_of_point G X x .fst (shape G))
        (orbit_of_point G X y .fst (shape G)))
  ≔ let S ≔ gset_underlying G X in
    let Px ≔ orbit_of_point G X x .fst (shape G) in
    let Py ≔ orbit_of_point G X y .fst (shape G) in
    iff_equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y)) (Id (S → PropTypes) Px Py)
      (orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y)) (subtypes_set S Px Py)
      (p ↦ map_path (Orbits G X) (S → PropTypes) (O ↦ O .fst (shape G)) (orbit_of_point G X x)
        (orbit_of_point G X y) p)
      (q ↦ orbit_map_path_from_mere G X (shape G, x) (shape G, y)
        (orbit_prop_path_backward (Px y) (Py y) (happly S (_ ↦ PropTypes) Px Py q y)
          (mere (Id (ActionType G X) (shape G, y) (shape G, y)) (refl (shape G, y)))))

{` [x] = [y] ≃ [x](sh_G, y), which is ‖(sh_G, x) = (sh_G, y)‖ by definition. `}
def orbit_point_member_definition (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Id Type (OrbitMember G X (orbit_of_point G X x) (shape G, y))
      (Mere (Id (ActionType G X) (shape G, x) (shape G, y)))
  ≔ refl (Mere (Id (ActionType G X) (shape G, x) (shape G, y)))

def orbit_point_path_member_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (OrbitMember G X (orbit_of_point G X x) (shape G, y))
  ≔ orbit_point_path_mere_equiv G X x y

{` [x] = [y] ≃ [y](sh_G, x). `}
def orbit_point_path_member_symm_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X)
  : Equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (OrbitMember G X (orbit_of_point G X y) (shape G, x))
  ≔ let T ≔ ActionType G X in
    iff_equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (Mere (Id T (shape G, y) (shape G, x)))
      (orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y)) (mere_isprop (Id T (shape G, y) (shape G, x)))
      (p ↦ trunc_map native_truncation (Id T (shape G, x) (shape G, y)) (Id T (shape G, y) (shape G, x))
        (inverse T (shape G, x) (shape G, y)) (orbit_map_path_to_mere G X (shape G, x) (shape G, y) p))
      (r ↦ orbit_map_path_from_mere G X (shape G, x) (shape G, y)
        (trunc_map native_truncation (Id T (shape G, y) (shape G, x)) (Id T (shape G, x) (shape G, y))
          (inverse T (shape G, y) (shape G, x)) r))

{` The relation ∃_g (g · x = y) as an equivalence relation on X(sh_G);
   reflexivity, symmetry and transitivity are transferred from [x] = [y]. `}
def orbit_relation_from_path (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (p : Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y)) : OrbitRelation G X x y
  ≔ orbit_point_path_exists_equiv G X x y .map p

def orbit_relation_to_path (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (r : OrbitRelation G X x y) : Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y)
  ≔ equiv_inverse_map (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y)) (OrbitRelation G X x y)
      (orbit_point_path_exists_equiv G X x y) r

def orbit_equivalence_relation (G : Group) (X : GSet G) : EquivalenceRelation (gset_underlying G X)
  ≔ let O ≔ Orbits G X in
    let c ≔ orbit_of_point G X in
    ((x y ↦ (OrbitRelation G X x y,
              mere_isprop (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) y)))),
     (x ↦ orbit_relation_from_path G X x x (refl (c x))),
     (x y r ↦ orbit_relation_from_path G X y x (inverse O (c x) (c y) (orbit_relation_to_path G X x y r))),
     (x y z r s ↦ orbit_relation_from_path G X x z
        (concat O (c x) (c y) (c z) (orbit_relation_to_path G X x y r) (orbit_relation_to_path G X y z s))))

{` rem:equivalents-of-[x]=[y], last sentence: as a function of x and y, the
   relation ∃_g (g · x = y) is the equivalence relation induced by the
   surjection [-] (x ~ y iff ‖[x] = [y]‖, module 45). `}
def orbit_relation_induced (G : Group) (X : GSet G)
  : Id (gset_underlying G X → gset_underlying G X → PropTypes) (orbit_equivalence_relation G X .predicate)
      (induced_relation (gset_underlying G X) (Orbits G X) (orbit_of_point G X) .predicate)
  ≔ let S ≔ gset_underlying G X in
    let O ≔ Orbits G X in
    let c ≔ orbit_of_point G X in
    let R ≔ orbit_equivalence_relation G X .predicate in
    let I ≔ induced_relation S O c .predicate in
    funext S (_ ↦ S → PropTypes) R I
      (x ↦ funext S (_ ↦ PropTypes) (R x) (I x)
        (y ↦ proposition_extensionality (R x y) (I x y)
          (r ↦ mere (Id O (c x) (c y)) (orbit_relation_to_path G X x y r))
          (m ↦ mere_rec (Id O (c x) (c y)) (OrbitRelation G X x y)
            (mere_isprop (Σ (USym G) (g ↦ Id S (gset_usym_act G X g x) y)))
            (orbit_relation_from_path G X x y) m)))
