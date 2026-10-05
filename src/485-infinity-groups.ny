export "404-group-examples"

{` Chapter 4, sec:inftygps (∞-groups).

   def:inftygps. U^{>0}_* ≔ Σ(A : U) A × isconn(A), the pointed connected
   types, as a record with the components in the printed order, and the type
   of ∞-groups as a wrapped copy (a one-field record, as for Group in
   module 400) with constructor mk_infty_group and destructor infty_group_B. `}
def PointedConnectedType : Type ≔ sig (carrier : Type, point : carrier, connected : Connected carrier)

def InftyGroup : Type ≔ sig (classifying : PointedConnectedType)

def mk_infty_group (X : PointedConnectedType) : InftyGroup ≔ (classifying ≔ X)

def infty_group_B (G : InftyGroup) : PointedConnectedType ≔ G .classifying

{` rem:pointedtypes: an ∞-group is the same as a pointed connected type. `}
def infty_group_classifying_equiv : Equiv InftyGroup PointedConnectedType
  ≔ quasi_inverse_equiv InftyGroup PointedConnectedType infty_group_B mk_infty_group (G ↦ refl G) (X ↦ refl X)

{` def:classifyingspace. The classifying type BG : U_* and the designated shape. `}
def infty_BG (G : InftyGroup) : Pointed ≔ (G .classifying .carrier, G .classifying .point)

def infty_shape (G : InftyGroup) : infty_BG G .carrier ≔ G .classifying .point

{` The unnumbered definition after def:classifyingspace: the automorphism
   ∞-group Aut_A(a) ≔ mkgroup (A_(a), (a, !)) of any a : A. `}
def infty_automorphism_group (A : Type) (a : A) : InftyGroup
  ≔ mk_infty_group (NativeComponent A a, component_point A a, native_component_connected A a)

{` The last definition of the chapter: Hom(G, H) ≔ Copy(BG →* BH), again a
   one-field record; Bf is the classifying map. `}
def InftyGroupHom (G H : InftyGroup) : Type ≔ sig (classifying_map : BookPointedMap (infty_BG G) (infty_BG H))

def mk_infty_hom (G H : InftyGroup) (k : BookPointedMap (infty_BG G) (infty_BG H)) : InftyGroupHom G H
  ≔ (classifying_map ≔ k)

def infty_hom_B (G H : InftyGroup) (f : InftyGroupHom G H) : BookPointedMap (infty_BG G) (infty_BG H)
  ≔ f .classifying_map

{` rem:autinfgp, second paragraph: the inclusion U^{=1}_* ↪ U^{>0}_* gives an
   injection Group ↪ InftyGroup (it forgets the proposition isGroupoid). The
   map on identity types is an equivalence, so the map is an embedding in the
   book's sense (proposition-valued fibers). `}
def group_to_infty_group (G : Group) : InftyGroup
  ≔ mk_infty_group (G .classifying .carrier, G .classifying .point, G .classifying .connected)

def group_to_infty_group_bg (G : Group) : Id Pointed (infty_BG (group_to_infty_group G)) (BG G) ≔ refl (BG G)

def group_infty_paths_equiv (G H : Group)
  : Equiv (Id Group G H) (Id InftyGroup (group_to_infty_group G) (group_to_infty_group H))
  ≔ let gp : (s : Id Type (G .classifying .carrier) (H .classifying .carrier))
          → isContr (Id isGroupoid s (G .classifying .groupoid) (H .classifying .groupoid))
      ≔ s ↦ pcg_groupoid_pathover (group_B G) (group_B H) s in
    quasi_inverse_equiv (Id Group G H) (Id InftyGroup (group_to_infty_group G) (group_to_infty_group H))
      (p ↦ refl group_to_infty_group p)
      (q ↦ (classifying ≔ (q .classifying .carrier, q .classifying .point, q .classifying .connected,
        gp (q .classifying .carrier) .center)))
      (p ↦ (classifying ≔ (refl (p .classifying .carrier), refl (p .classifying .point),
        refl (p .classifying .connected),
        inverse (Id isGroupoid (p .classifying .carrier) (G .classifying .groupoid) (H .classifying .groupoid))
          (p .classifying .groupoid) (gp (p .classifying .carrier) .center)
          (gp (p .classifying .carrier) .contract (p .classifying .groupoid)))))
      (q ↦ refl q)

def group_to_infty_group_embedding : IsEmbedding Group InftyGroup group_to_infty_group
  ≔ path_equivalences_embedding Group InftyGroup group_to_infty_group
      (G H ↦ book_equivalence (Id Group G H) (Id InftyGroup (group_to_infty_group G) (group_to_infty_group H))
        (group_infty_paths_equiv G H) .equiv)

{` rem:autinfgp, first paragraph: for a set S, the component U_(S) of the
   universe is a groupoid (although U is not assumed to be one), so the
   automorphism ∞-group Aut_U(S) is an ordinary group. `}
def universe_component_set (S : Type) (hS : isSet S) (X : NativeComponent Type S) : isSet (X .fst)
  ≔ mere_rec (Id Type S (X .fst)) (isSet (X .fst)) (isset_isprop (X .fst))
      (p ↦ transport Type isSet S (X .fst) p hS) (X .snd)

def universe_set_component_groupoid (S : Type) (hS : isSet S) : isGroupoid (NativeComponent Type S)
  ≔ X Y ↦ hlevel_two_to_set (Id (NativeComponent Type S) X Y)
      (hlevel_equiv (suc. (suc. zero.)) (Equiv (X .fst) (Y .fst)) (Id (NativeComponent Type S) X Y)
        (canonical_inverse_equiv (Id (NativeComponent Type S) X Y) (Equiv (X .fst) (Y .fst))
          (compose_equiv (Id (NativeComponent Type S) X Y) (Id Type (X .fst) (Y .fst)) (Equiv (X .fst) (Y .fst))
            (component_path_equiv Type S X Y) (univalence_equiv (X .fst) (Y .fst))))
        (set_to_hlevel_two (Equiv (X .fst) (Y .fst))
          (equivalences_set (X .fst) (Y .fst) (universe_component_set S hS Y))))

def universe_set_automorphism_group (S : Type) (hS : isSet S) : Group
  ≔ mkgroup (NativeComponent Type S, component_point Type S, native_component_connected Type S,
      universe_set_component_groupoid S hS)

def universe_set_automorphism_group_infty (S : Type) (hS : isSet S)
  : Id InftyGroup (group_to_infty_group (universe_set_automorphism_group S hS)) (infty_automorphism_group Type S)
  ≔ refl (infty_automorphism_group Type S)

{` Litmus: the symmetries in Aut_U(A) are the self-equivalences of A
   (for every A, by univalence); for A = Fin n this is USym Σ_n. `}
def infty_universe_automorphisms_equiv (A : Type)
  : Equiv (Loop (infty_BG (infty_automorphism_group Type A))) (Equiv A A)
  ≔ compose_equiv (Loop (infty_BG (infty_automorphism_group Type A))) (Id Type A A) (Equiv A A)
      (component_path_equiv Type A (component_point Type A) (component_point Type A))
      (univalence_equiv A A)

def universe_fin_automorphisms_symmetric (n : Nat)
  : Equiv (USym (universe_set_automorphism_group (Fin n) (fin_set n))) (Equiv (Fin n) (Fin n))
  ≔ infty_universe_automorphisms_equiv (Fin n)
