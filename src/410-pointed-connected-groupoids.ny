export "485-infinity-groups"
export "284-chapter-two-completions"

{` Chapter 4, sec:typegroup (group.tex 161-389): pointed connected
   groupoids, xca:defgroup, rem:aut, rem:symmetriesofnonconnectedgroupoids,
   and general identifications of automorphism groups used in the examples. `}

{` def:pt-conn-groupoid, margin note. U^{≤1} ≔ Groupoid ≔ Σ(A : U) isgrpd(A)
   is GroupoidTypes (module 284), its pointed variant U^{≤1}_* is
   PointedGroupoids (module 284) and U^{>0}_* is PointedConnectedType
   (module 485). The unpointed type of connected types: U^{>0} ≔ Σ(A : U) isconn(A). `}
def ConnectedTypes : Type ≔ Σ Type Connected

{` The book's literal U^{=1}_* ≔ Σ(A : U)(A × isconn(A) × isgrpd(A)), with
   A × B × C read as A × (B × C), is equivalent to the record
   PointedConnectedGroupoid; both round trips hold by reflexivity. `}
def PointedConnectedGroupoidSigma : Type
  ≔ Σ Type (A ↦ Product A (Product (Connected A) (isGroupoid A)))

def pcg_sigma_equiv : Equiv PointedConnectedGroupoid PointedConnectedGroupoidSigma
  ≔ quasi_inverse_equiv PointedConnectedGroupoid PointedConnectedGroupoidSigma
      (X ↦ (X .carrier, (X .point, (X .connected, X .groupoid))))
      (Y ↦ (Y .fst, Y .snd .fst, Y .snd .snd .fst, Y .snd .snd .snd))
      (X ↦ refl X) (Y ↦ refl Y)

{` Litmus: the circle-free unit example lies in U^{=1}_* and in the pointed
   groupoids of module 284. `}
def unit_pointed_groupoid : PointedGroupoids ≔ ((Unit, unit_groupoid), star.)

def unit_connected_type : ConnectedTypes ≔ (Unit, contractible_connected Unit unit_contraction)

{` xca:defgroup, first part: for a : A, A is connected iff Π(x : A) ‖a = x‖. `}
def connected_to_based (A : Type) (a : A) (h : Connected A) : (x : A) → Mere (Id A a x)
  ≔ x ↦ h .snd a x

def based_to_connected (A : Type) (a : A) (k : (x : A) → Mere (Id A a x)) : Connected A
  ≔ (mere A a, x y ↦ merely_paths_compose native_truncation A a x y (k x) (k y))

def based_connected_prop (A : Type) (a : A) : isProp ((x : A) → Mere (Id A a x))
  ≔ pi_prop A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x))

def connected_based_equiv (A : Type) (a : A) : Equiv (Connected A) ((x : A) → Mere (Id A a x))
  ≔ iff_equiv (Connected A) ((x : A) → Mere (Id A a x)) (connected_prop A) (based_connected_prop A a)
      (connected_to_based A a) (based_to_connected A a)

{` xca:defgroup, second part, in its correct form: if every x : A is merely
   equal to a (equivalently, A is connected), then A is a groupoid iff
   a = a is a set. Without this hypothesis only the forward direction
   holds (module 411 gives the counterexample A = U, a = ∅). `}
def groupoid_loops_set (A : Type) (a : A) (h : isGroupoid A) : isSet (Id A a a) ≔ h a a

def based_set_loops_groupoid (A : Type) (a : A) (k : (x : A) → Mere (Id A a x)) (s : isSet (Id A a a))
  : isGroupoid A
  ≔ x y ↦ mere_rec (Id A a x) (isSet (Id A x y)) (isset_isprop (Id A x y))
      (p ↦ mere_rec (Id A a y) (isSet (Id A x y)) (isset_isprop (Id A x y))
        (q ↦ transport A (z ↦ isSet (Id A z y)) a x p
          (transport A (z ↦ isSet (Id A a z)) a y q s)) (k y)) (k x)

def based_groupoid_loops_equiv (A : Type) (a : A) (k : (x : A) → Mere (Id A a x))
  : Equiv (isGroupoid A) (isSet (Id A a a))
  ≔ iff_equiv (isGroupoid A) (isSet (Id A a a)) (isgroupoid_isprop A) (isset_isprop (Id A a a))
      (groupoid_loops_set A a) (based_set_loops_groupoid A a k)

def connected_groupoid_loops_equiv (A : Type) (a : A) (h : Connected A)
  : Equiv (isGroupoid A) (isSet (Id A a a))
  ≔ based_groupoid_loops_equiv A a (connected_to_based A a h)

{` xca:defgroup, conclusion: U^{=1}_* ≃ Σ(A : U) Σ(a : A) ((Π(x : A) ‖a = x‖) × isSet(a = a)). `}
def DefGroupSigma : Type
  ≔ Σ Type (A ↦ Σ A (a ↦ Product ((x : A) → Mere (Id A a x)) (isSet (Id A a a))))

def pcg_defgroup_to (X : PointedConnectedGroupoid) : DefGroupSigma
  ≔ (X .carrier, (X .point, (connected_to_based (X .carrier) (X .point) (X .connected),
      X .groupoid (X .point) (X .point))))

def pcg_defgroup_from (Y : DefGroupSigma) : PointedConnectedGroupoid
  ≔ (Y .fst, Y .snd .fst, based_to_connected (Y .fst) (Y .snd .fst) (Y .snd .snd .fst),
      based_set_loops_groupoid (Y .fst) (Y .snd .fst) (Y .snd .snd .fst) (Y .snd .snd .snd))

def pcg_defgroup_equiv : Equiv PointedConnectedGroupoid DefGroupSigma
  ≔ quasi_inverse_equiv PointedConnectedGroupoid DefGroupSigma pcg_defgroup_to pcg_defgroup_from
      (X ↦ (refl (X .carrier), refl (X .point),
        connected_prop (X .carrier) (pcg_defgroup_from (pcg_defgroup_to X) .connected) (X .connected),
        isgroupoid_isprop (X .carrier) (pcg_defgroup_from (pcg_defgroup_to X) .groupoid) (X .groupoid)))
      (Y ↦ (refl (Y .fst), (refl (Y .snd .fst),
        (based_connected_prop (Y .fst) (Y .snd .fst)
           (pcg_defgroup_to (pcg_defgroup_from Y) .snd .snd .fst) (Y .snd .snd .fst),
         isset_isprop (Id (Y .fst) (Y .snd .fst) (Y .snd .fst))
           (pcg_defgroup_to (pcg_defgroup_from Y) .snd .snd .snd) (Y .snd .snd .snd)))))

{` Remark after xca:defgroup: a pointed connected groupoid (A, a, p, q) is
   determined by the pointed type (A, a), since isconn(A) and isgrpd(A) are
   propositions (connected_prop, isgroupoid_isprop). `}
def pcg_witnesses_unique (A : Type) (a : A) (c c' : Connected A) (g g' : isGroupoid A)
  : Id PointedConnectedGroupoid (A, a, c, g) (A, a, c', g')
  ≔ (refl A, refl a, connected_prop A c c', isgroupoid_isprop A g g')

{` rem:aut: U^{=1}_* is the subtype of U_* given by the proposition
   "connected groupoid" (as a Σ-type over Pointed, with refl round trips). `}
def PointedConnectedGroupoidStructure (X : Pointed) : Type
  ≔ Product (Connected (X .carrier)) (isGroupoid (X .carrier))

def pcg_structure_prop (X : Pointed) : isProp (PointedConnectedGroupoidStructure X)
  ≔ product_prop (Connected (X .carrier)) (isGroupoid (X .carrier))
      (connected_prop (X .carrier)) (isgroupoid_isprop (X .carrier))

def pcg_pointed_subtype_equiv
  : Equiv PointedConnectedGroupoid (Σ Pointed PointedConnectedGroupoidStructure)
  ≔ quasi_inverse_equiv PointedConnectedGroupoid (Σ Pointed PointedConnectedGroupoidStructure)
      (X ↦ (pcg_pointed X, (X .connected, X .groupoid)))
      (Y ↦ (Y .fst .carrier, Y .fst .point, Y .snd .fst, Y .snd .snd))
      (X ↦ refl X) (Y ↦ refl Y)

{` rem:aut, last sentence: (G = H) ≃ (BG = BH) as pointed types. `}
def group_path_pointed_equiv (G H : Group) : Equiv (Id Group G H) (Id Pointed (BG G) (BG H))
  ≔ compose_equiv (Id Group G H) (Id PointedConnectedGroupoid (group_B G) (group_B H)) (Id Pointed (BG G) (BG H))
      (group_path_classifying_equiv G H) (pcg_path_pointed_equiv (group_B G) (group_B H))

def group_path_pointed_refl (G : Group)
  : Id (Id Pointed (BG G) (BG G)) (group_path_pointed_equiv G G .map (refl G)) (refl (BG G))
  ≔ refl (refl (BG G))

{` def:group-symmetries, footnote: USym : Group → Set, mkgroup X ↦ ΩX. `}
def usym_set_type (G : Group) : SetTypes ≔ (USym G, usym_set G)

def usym_mkgroup (X : PointedConnectedGroupoid)
  : Id Type (usym_set_type (mkgroup X) .fst) (Omega (pcg_pointed X) .carrier)
  ≔ refl (Loop (pcg_pointed X))

{` rem:whypointedconngpoid: the map on loops induced by fst : A_(a) → A
   is an equivalence ((a,!) = (a,!)) ≃ (a = a); its underlying map is ap_fst. `}
def component_loops_equiv (A : Type) (a : A)
  : Equiv (Id (NativeComponent A a) (component_point A a) (component_point A a)) (Id A a a)
  ≔ component_path_equiv A a (component_point A a) (component_point A a)

def component_loops_equiv_map (A : Type) (a : A)
  (p : Id (NativeComponent A a) (component_point A a) (component_point A a))
  : Id (Id A a a) (component_loops_equiv A a .map p) (refl ((u ↦ u .fst) : NativeComponent A a → A) p)
  ≔ refl (component_loops_equiv A a .map p)

{` rem:symmetriesofnonconnectedgroupoids. For connected A, the first
   projection fst : A_(a) → A is an equivalence (its fibers ‖a = x‖ are
   inhabited propositions), pointed by refl a. `}
def connected_component_fst_equiv (A : Type) (hA : Connected A) (a : A)
  : BookIsEquiv (NativeComponent A a) A (u ↦ u .fst)
  ≔ x ↦ book_contractibility_equiv (Mere (Id A a x)) (BookFiber (NativeComponent A a) A (u ↦ u .fst) x)
      (canonical_inverse_equiv (BookFiber (NativeComponent A a) A (u ↦ u .fst) x) (Mere (Id A a x))
        (projection_book_fiber_equiv A (y ↦ Mere (Id A a y)) x))
      .map (hA .snd a x, t ↦ mere_isprop (Id A a x) (hA .snd a x) t)

def connected_component_pointed_equiv (A : Type) (hA : Connected A) (a : A)
  : BookPointedEquiv (NativeComponent A a, component_point A a) (A, a)
  ≔ ((u ↦ u .fst, refl a), connected_component_fst_equiv A hA a)

{` For G ≡ mkgroup (A, a) there is an identification G = Aut_A(a); in
   particular G = Aut_BG(sh_G) for every group G. `}
def pcg_automorphism_path (X : PointedConnectedGroupoid)
  : Id Group (mkgroup X) (automorphism_group (X .carrier) (X .groupoid) (X .point))
  ≔ inverse Group (automorphism_group (X .carrier) (X .groupoid) (X .point)) (mkgroup X)
      (group_path_from_pointed_equiv (automorphism_group (X .carrier) (X .groupoid) (X .point)) (mkgroup X)
        (connected_component_pointed_equiv (X .carrier) (X .connected) (X .point)))

def group_shape_automorphism_path (G : Group)
  : Id Group G (automorphism_group (BG G .carrier) (bg_groupoid G) (shape G))
  ≔ pcg_automorphism_path (G .classifying)

{` General identifications of automorphism groups. An equivalence
   e : A ≃ B of groupoids gives Aut_A(a) = Aut_B(e a) (the induced map of
   components, component_equiv of module 79, pointed by reflexivity). `}
def automorphism_group_equiv_path (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (e : Equiv A B) (a : A)
  : Id Group (automorphism_group A hA a) (automorphism_group B hB (e .map a))
  ≔ group_path_from_pointed_equiv (automorphism_group A hA a) (automorphism_group B hB (e .map a))
      ((component_equiv A B e a .map,
        component_path B (e .map a) (component_point B (e .map a)) (component_equiv A B e a .map (component_point A a))
          (refl (e .map a))),
       book_equivalence (NativeComponent A a) (NativeComponent B (e .map a)) (component_equiv A B e a) .equiv)

{` Aut_A(a) = Aut_A(b) for a = b. `}
def automorphism_group_point_path (A : Type) (hA : isGroupoid A) (a b : A) (p : Id A a b)
  : Id Group (automorphism_group A hA a) (automorphism_group A hA b)
  ≔ refl ((x ↦ automorphism_group A hA x) : A → Group) p

def automorphism_group_equiv_path_at (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (e : Equiv A B)
  (a : A) (b : B) (p : Id B (e .map a) b)
  : Id Group (automorphism_group A hA a) (automorphism_group B hB b)
  ≔ concat Group (automorphism_group A hA a) (automorphism_group B hB (e .map a)) (automorphism_group B hB b)
      (automorphism_group_equiv_path A B hA hB e a) (automorphism_group_point_path B hB (e .map a) b p)

{` A subtype Σ A P (P proposition-valued) has the same automorphism groups
   as A: Aut_{ΣAP}(u) = Aut_A(fst u) (component_subtype_equiv of module 38). `}
def automorphism_group_subtype_path (A : Type) (P : A → Type) (hP : (a : A) → isProp (P a))
  (hS : isGroupoid (Σ A P)) (hA : isGroupoid A) (u : Σ A P)
  : Id Group (automorphism_group (Σ A P) hS u) (automorphism_group A hA (u .fst))
  ≔ group_path_from_pointed_equiv (automorphism_group (Σ A P) hS u) (automorphism_group A hA (u .fst))
      ((component_subtype_equiv A P hP u .map,
        component_path A (u .fst) (component_point A (u .fst))
          (component_subtype_equiv A P hP u .map (component_point (Σ A P) u)) (refl (u .fst))),
       book_equivalence (NativeComponent (Σ A P) u) (NativeComponent A (u .fst)) (component_subtype_equiv A P hP u) .equiv)

{` Groups with contractible classifying types are all identified. `}
def contractible_classifying_groups_path (G H : Group)
  (hG : BookIsContr (BG G .carrier)) (hH : BookIsContr (BG H .carrier)) : Id Group G H
  ≔ group_path_from_pointed_equiv G H
      ((_ ↦ shape H, refl (shape H)),
       y ↦ contractible_map_book_fiber (BG G .carrier) (BG H .carrier) (_ ↦ shape H) hG hH y)

{` A connected type with contractible loop type at a point is contractible.
   Consequently a group whose symmetries form a contractible type is
   identified with the trivial group TG (module 414). `}
def paths_prop_from_loops (A : Type) (a x : A) (h : BookIsContr (Id A a a)) : isProp (Id A a x)
  ≔ y z ↦
    let w ≔ concat A a x a y (inverse A a x z) in
    calc
      y = concat A a x x y (refl x) by inverse (Id A a x) (concat A a x x y (refl x)) y (concat_p1 A a x y)
      = concat A a x x y (concat A x a x (inverse A a x z) z)
        by refl (concat A a x x y) (inverse (Id A x x) (concat A x a x (inverse A a x z) z) (refl x)
          (concat_inverse_left A a x z))
      = concat A a a x w z
        by inverse (Id A a x) (concat A a a x w z) (concat A a x x y (concat A x a x (inverse A a x z) z))
          (concat_assoc A a x a x y (inverse A a x z) z)
      = concat A a a x (refl a) z
        by refl ((l ↦ concat A a a x l z) : Id A a a → Id A a x)
          (concat (Id A a a) w (h .center) (refl a)
            (inverse (Id A a a) (h .center) w (h .contract w)) (h .contract (refl a)))
      = z by concat_1p A a x z ∎

def connected_loops_contractible (A : Type) (hA : Connected A) (a : A) (h : BookIsContr (Id A a a))
  : BookIsContr A
  ≔ (a, x ↦ mere_rec (Id A a x) (Id A a x) (paths_prop_from_loops A a x h) (p ↦ p) (hA .snd a x))

def usym_contractible_bg_contractible (G : Group) (h : BookIsContr (USym G)) : BookIsContr (BG G .carrier)
  ≔ connected_loops_contractible (BG G .carrier) (bg_connected G) (shape G) h

def usym_contractible_groups_path (G H : Group) (hG : BookIsContr (USym G)) (hH : BookIsContr (USym H))
  : Id Group G H
  ≔ contractible_classifying_groups_path G H (usym_contractible_bg_contractible G hG)
      (usym_contractible_bg_contractible H hH)
