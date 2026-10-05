export "414-trivial-and-permutation-groups"
export "193-replacement"

{` Chapter 4, ex:groups, the footnote on universes (group.tex 452-484), in the
   universe model of modules 190-193: a universe U is a replete smallness
   predicate on Narya's Type, and U : U' is a NestedUniverses pair.

   Group_U ≔ Copy(U^{=1}_*), the groups whose classifying type lies in U, is
   GroupIn U; it is equivalent to the book's Σ(A : U)(A × isconn(A) × isgrpd(A)). `}
def SmallPointedConnectedGroupoids (U : Universe) : Type
  ≔ Σ (UniverseType U) (A ↦ Product (A .fst) (Product (Connected (A .fst)) (isGroupoid (A .fst))))

def GroupIn (U : Universe) : Type ≔ Σ Group (G ↦ U .small (BG G .carrier))

def group_in_equiv (U : Universe) : Equiv (GroupIn U) (SmallPointedConnectedGroupoids U)
  ≔ quasi_inverse_equiv (GroupIn U) (SmallPointedConnectedGroupoids U)
      (G ↦ ((BG (G .fst) .carrier, G .snd), (shape (G .fst), (bg_connected (G .fst), bg_groupoid (G .fst)))))
      (Y ↦ (mkgroup (Y .fst .fst, Y .snd .fst, Y .snd .snd .fst, Y .snd .snd .snd), Y .fst .snd))
      (G ↦ refl G) (Y ↦ refl Y)

def connected_type_small (U : Universe) (A : Type) (s : U .small A) : U .small (Connected A)
  ≔ U .sigma_small (Mere A) (_ ↦ (x y : A) → Mere (Id A x y)) (U .trunc_small A s)
      (_ ↦ U .pi_small A (x ↦ (y : A) → Mere (Id A x y)) s
        (x ↦ U .pi_small A (y ↦ Mere (Id A x y)) s (y ↦ U .trunc_small (Id A x y) (U .id_small A s x y))))

def groupoid_type_small (U : Universe) (A : Type) (s : U .small A) : U .small (isGroupoid A)
  ≔ U .pi_small A (x ↦ (y : A) → isSet (Id A x y)) s
      (x ↦ U .pi_small A (y ↦ isSet (Id A x y)) s (y ↦ set_type_small U (Id A x y) (U .id_small A s x y)))

{` If U : U', then U^{=1}_* and hence Group_U lie in U' ("if U is U_1 then
   Group is in U_2"). `}
def small_pcg_in_upper (N : NestedUniverses) : N .upper .small (SmallPointedConnectedGroupoids (N .lower))
  ≔ N .upper .sigma_small (UniverseType (N .lower))
      (A ↦ Product (A .fst) (Product (Connected (A .fst)) (isGroupoid (A .fst))))
      (N .lower_in_upper)
      (A ↦ N .upper .sigma_small (A .fst) (_ ↦ Product (Connected (A .fst)) (isGroupoid (A .fst)))
        (N .cumulative (A .fst) (A .snd))
        (_ ↦ N .upper .sigma_small (Connected (A .fst)) (_ ↦ isGroupoid (A .fst))
          (connected_type_small (N .upper) (A .fst) (N .cumulative (A .fst) (A .snd)))
          (_ ↦ groupoid_type_small (N .upper) (A .fst) (N .cumulative (A .fst) (A .snd)))))

def group_in_upper (N : NestedUniverses) : EssentiallySmall (N .upper) (GroupIn (N .lower))
  ≔ essentially_small_equiv (N .upper) (SmallPointedConnectedGroupoids (N .lower)) (GroupIn (N .lower))
      (canonical_inverse_equiv (GroupIn (N .lower)) (SmallPointedConnectedGroupoids (N .lower)) (group_in_equiv (N .lower)))
      (small_essentially_small (N .upper) (SmallPointedConnectedGroupoids (N .lower)) (small_pcg_in_upper N))

{` Prop_0 ≔ Σ(P : U_0) isprop(P) is PropU U; true : Prop_U and Prop_U : U'
   (prop_u_in_upper). The trivial group Aut_{Prop_U}(true) is a group whose
   classifying type lies in U' (so the U of def:pt-conn-groupoid must be at
   least U'). `}
def small_true (U : Universe) : PropU U ≔ ((Unit, U .unit_small), unit_prop)

def small_trivial_group (U : Universe) : Group
  ≔ automorphism_group (PropU U) (set_is_groupoid (PropU U) (prop_u_set U)) (small_true U)

def small_trivial_group_trivial (U : Universe) : Id Group (small_trivial_group U) trivial_group
  ≔ usym_contractible_trivial (small_trivial_group U)
      (automorphism_group_usym_contractible (PropU U) (set_is_groupoid (PropU U) (prop_u_set U)) (small_true U)
        (set_loops_contractible (PropU U) (prop_u_set U) (small_true U)))

def small_trivial_group_in_upper (N : NestedUniverses) : N .upper .small (BG (small_trivial_group (N .lower)) .carrier)
  ≔ N .upper .sigma_small (PropU (N .lower)) (P ↦ Mere (Id (PropU (N .lower)) (small_true (N .lower)) P))
      (prop_u_in_upper N)
      (P ↦ N .upper .trunc_small (Id (PropU (N .lower)) (small_true (N .lower)) P)
        (N .upper .id_small (PropU (N .lower)) (prop_u_in_upper N) (small_true (N .lower)) P))

{` "The trivial group Aut_true(triv) is an element of Group_0": its
   classifying type is small in every universe. `}
def unit_automorphism_group : Group ≔ automorphism_group Unit (set_is_groupoid Unit unit_set) star.

def unit_automorphism_group_in (U : Universe) : GroupIn U
  ≔ (unit_automorphism_group,
     U .sigma_small Unit (x ↦ Mere (Id Unit star. x)) (U .unit_small)
       (x ↦ U .trunc_small (Id Unit star. x) (U .id_small Unit (U .unit_small) star. x)))

def unit_automorphism_group_trivial : Id Group unit_automorphism_group trivial_group
  ≔ set_automorphism_group_trivial Unit unit_set star.

{` Replacement gives Σ_S ∈ Group_U for S : Set_U: the component Set_(S) is
   the component of the locally small type Set_U at S (smallness transports
   along mere identifications), hence essentially small
   (component_essentially_small, xca:comp-loc-small-ess-small). `}
def small_set_code (U : Universe) (S : SetTypes) (s : U .small (S .fst)) : SetU U ≔ ((S .fst, s), S .snd)

def small_sets_forget (U : Universe) (X : SetU U) : SetTypes ≔ (X .fst .fst, X .snd)

def small_set_component_to (U : Universe) (S : SetTypes) (s : U .small (S .fst))
  (u : NativeComponent (SetU U) (small_set_code U S s)) : NativeComponent SetTypes S
  ≔ (small_sets_forget U (u .fst),
     mere_rec (Id (SetU U) (small_set_code U S s) (u .fst)) (Mere (Id SetTypes S (small_sets_forget U (u .fst))))
       (mere_isprop (Id SetTypes S (small_sets_forget U (u .fst))))
       (p ↦ mere (Id SetTypes S (small_sets_forget U (u .fst))) (refl (small_sets_forget U) p)) (u .snd))

def small_set_component_small (U : Universe) (S : SetTypes) (s : U .small (S .fst)) (v : NativeComponent SetTypes S)
  : U .small (v .fst .fst)
  ≔ mere_rec (Id SetTypes S (v .fst)) (U .small (v .fst .fst)) (U .small_prop (v .fst .fst))
      (p ↦ transport Type (U .small) (S .fst) (v .fst .fst) (p .fst) s) (v .snd)

def small_set_lift_path (U : Universe) (X Y : SetU U) (p : Id Type (X .fst .fst) (Y .fst .fst)) : Id (SetU U) X Y
  ≔ subtype_equal (UniverseType U) (Z ↦ isSet (Z .fst)) (Z ↦ isset_isprop (Z .fst)) X Y
      (subtype_equal Type (U .small) (U .small_prop) (X .fst) (Y .fst) p)

def small_set_component_from (U : Universe) (S : SetTypes) (s : U .small (S .fst)) (v : NativeComponent SetTypes S)
  : NativeComponent (SetU U) (small_set_code U S s)
  ≔ let Y : SetU U ≔ ((v .fst .fst, small_set_component_small U S s v), v .fst .snd) in
    (Y, mere_rec (Id SetTypes S (v .fst)) (Mere (Id (SetU U) (small_set_code U S s) Y))
      (mere_isprop (Id (SetU U) (small_set_code U S s) Y))
      (p ↦ mere (Id (SetU U) (small_set_code U S s) Y) (small_set_lift_path U (small_set_code U S s) Y (p .fst)))
      (v .snd))

def small_set_component_equiv (U : Universe) (S : SetTypes) (s : U .small (S .fst))
  : Equiv (NativeComponent (SetU U) (small_set_code U S s)) (NativeComponent SetTypes S)
  ≔ quasi_inverse_equiv (NativeComponent (SetU U) (small_set_code U S s)) (NativeComponent SetTypes S)
      (small_set_component_to U S s) (small_set_component_from U S s)
      (u ↦ component_path (SetU U) (small_set_code U S s)
        (small_set_component_from U S s (small_set_component_to U S s u)) u
        (small_set_lift_path U (small_set_component_from U S s (small_set_component_to U S s u) .fst) (u .fst)
          (refl (u .fst .fst .fst))))
      (v ↦ component_path SetTypes S (small_set_component_to U S s (small_set_component_from U S s v)) v
        (refl (v .fst)))

def permutation_group_essentially_small (U : Universe) (rep : Replacement U) (S : SetTypes) (s : U .small (S .fst))
  : EssentiallySmall U (BG (permutation_group S) .carrier)
  ≔ essentially_small_equiv U (NativeComponent (SetU U) (small_set_code U S s)) (NativeComponent SetTypes S)
      (small_set_component_equiv U S s)
      (component_essentially_small U rep (SetU U) (set_u_locally_small U) (small_set_code U S s))

def permutation_group_in (U : Universe) (rep : Replacement U) (S : SetTypes) (s : U .small (S .fst)) : GroupIn U
  ≔ (permutation_group S,
     essentially_small_is_small U (BG (permutation_group S) .carrier) (permutation_group_essentially_small U rep S s))

{` Replacement also gives Aut_Group(G) ∈ Group_U for G : Group_U: Group_U is
   locally U-small (identifications are pointed equivalences of U-small
   classifying types), so its component at G is essentially U-small, and it
   is the component of Group at G. `}
def book_contr_sigma_equiv (X : Type) : Equiv (BookIsContr X) (Σ X (c ↦ (x : X) → Id X c x))
  ≔ quasi_inverse_equiv (BookIsContr X) (Σ X (c ↦ (x : X) → Id X c x))
      (h ↦ (h .center, h .contract)) (t ↦ (t .fst, t .snd)) (h ↦ refl h) (t ↦ refl t)

def book_contr_small (U : Universe) (X : Type) (s : U .small X) : U .small (BookIsContr X)
  ≔ small_equiv U (Σ X (c ↦ (x : X) → Id X c x)) (BookIsContr X)
      (canonical_inverse_equiv (BookIsContr X) (Σ X (c ↦ (x : X) → Id X c x)) (book_contr_sigma_equiv X))
      (U .sigma_small X (c ↦ (x : X) → Id X c x) s (c ↦ U .pi_small X (x ↦ Id X c x) s (x ↦ U .id_small X s c x)))

def book_pointed_equiv_small (U : Universe) (X Y : Pointed) (sX : U .small (X .carrier)) (sY : U .small (Y .carrier))
  : U .small (BookPointedEquiv X Y)
  ≔ U .sigma_small (BookPointedMap X Y) (f ↦ BookIsEquiv (X .carrier) (Y .carrier) (f .fst))
      (U .sigma_small (X .carrier → Y .carrier) (f ↦ Id (Y .carrier) (Y .point) (f (X .point)))
        (U .pi_small (X .carrier) (_ ↦ Y .carrier) sX (_ ↦ sY))
        (f ↦ U .id_small (Y .carrier) sY (Y .point) (f (X .point))))
      (f ↦ U .pi_small (Y .carrier) (y ↦ BookIsContr (BookFiber (X .carrier) (Y .carrier) (f .fst) y)) sY
        (y ↦ book_contr_small U (BookFiber (X .carrier) (Y .carrier) (f .fst) y)
          (U .sigma_small (X .carrier) (x ↦ Id (Y .carrier) y (f .fst x)) sX
            (x ↦ U .id_small (Y .carrier) sY y (f .fst x)))))

def group_in_paths_equiv (U : Universe) (G H : GroupIn U)
  : Equiv (Id (GroupIn U) G H) (BookPointedEquiv (BG (G .fst)) (BG (H .fst)))
  ≔ compose_equiv (Id (GroupIn U) G H) (Id Group (G .fst) (H .fst)) (BookPointedEquiv (BG (G .fst)) (BG (H .fst)))
      (subtype_path_equiv Group (K ↦ U .small (BG K .carrier)) (K ↦ U .small_prop (BG K .carrier)) G H)
      (compose_equiv (Id Group (G .fst) (H .fst)) (GroupIso (G .fst) (H .fst)) (BookPointedEquiv (BG (G .fst)) (BG (H .fst)))
        (group_path_iso_equiv (G .fst) (H .fst))
        (canonical_inverse_equiv (BookPointedEquiv (BG (G .fst)) (BG (H .fst))) (GroupIso (G .fst) (H .fst))
          (book_pointed_equiv_group_iso_equiv (G .fst) (H .fst))))

def group_in_locally_small (U : Universe) : LocallySmall U (GroupIn U)
  ≔ G H ↦ essentially_small_equiv U (BookPointedEquiv (BG (G .fst)) (BG (H .fst))) (Id (GroupIn U) G H)
      (canonical_inverse_equiv (Id (GroupIn U) G H) (BookPointedEquiv (BG (G .fst)) (BG (H .fst)))
        (group_in_paths_equiv U G H))
      (small_essentially_small U (BookPointedEquiv (BG (G .fst)) (BG (H .fst)))
        (book_pointed_equiv_small U (BG (G .fst)) (BG (H .fst)) (G .snd) (H .snd)))

def group_component_small (U : Universe) (G : GroupIn U) (v : NativeComponent Group (G .fst))
  : U .small (BG (v .fst) .carrier)
  ≔ mere_rec (Id Group (G .fst) (v .fst)) (U .small (BG (v .fst) .carrier)) (U .small_prop (BG (v .fst) .carrier))
      (p ↦ transport Type (U .small) (BG (G .fst) .carrier) (BG (v .fst) .carrier)
        (refl ((K ↦ BG K .carrier) : Group → Type) p) (G .snd))
      (v .snd)

def group_component_to (U : Universe) (G : GroupIn U) (u : NativeComponent (GroupIn U) G)
  : NativeComponent Group (G .fst)
  ≔ (u .fst .fst, mere_rec (Id (GroupIn U) G (u .fst)) (Mere (Id Group (G .fst) (u .fst .fst)))
      (mere_isprop (Id Group (G .fst) (u .fst .fst)))
      (p ↦ mere (Id Group (G .fst) (u .fst .fst)) (refl ((K ↦ K .fst) : GroupIn U → Group) p)) (u .snd))

def group_component_from (U : Universe) (G : GroupIn U) (v : NativeComponent Group (G .fst))
  : NativeComponent (GroupIn U) G
  ≔ ((v .fst, group_component_small U G v),
     mere_rec (Id Group (G .fst) (v .fst)) (Mere (Id (GroupIn U) G (v .fst, group_component_small U G v)))
       (mere_isprop (Id (GroupIn U) G (v .fst, group_component_small U G v)))
       (p ↦ mere (Id (GroupIn U) G (v .fst, group_component_small U G v))
         (subtype_equal Group (K ↦ U .small (BG K .carrier)) (K ↦ U .small_prop (BG K .carrier))
           G (v .fst, group_component_small U G v) p))
       (v .snd))

def group_component_equiv (U : Universe) (G : GroupIn U)
  : Equiv (NativeComponent (GroupIn U) G) (NativeComponent Group (G .fst))
  ≔ quasi_inverse_equiv (NativeComponent (GroupIn U) G) (NativeComponent Group (G .fst))
      (group_component_to U G) (group_component_from U G)
      (u ↦ component_path (GroupIn U) G (group_component_from U G (group_component_to U G u)) u
        (subtype_equal Group (K ↦ U .small (BG K .carrier)) (K ↦ U .small_prop (BG K .carrier))
          (group_component_from U G (group_component_to U G u) .fst) (u .fst) (refl (u .fst .fst))))
      (v ↦ component_path Group (G .fst) (group_component_to U G (group_component_from U G v)) v (refl (v .fst)))

def group_aut_essentially_small (U : Universe) (rep : Replacement U) (G : GroupIn U)
  : EssentiallySmall U (BG (group_aut (G .fst)) .carrier)
  ≔ essentially_small_equiv U (NativeComponent (GroupIn U) G) (NativeComponent Group (G .fst))
      (group_component_equiv U G)
      (component_essentially_small U rep (GroupIn U) (group_in_locally_small U) G)

def group_aut_in (U : Universe) (rep : Replacement U) (G : GroupIn U) : GroupIn U
  ≔ (group_aut (G .fst), essentially_small_is_small U (BG (group_aut (G .fst)) .carrier) (group_aut_essentially_small U rep G))
