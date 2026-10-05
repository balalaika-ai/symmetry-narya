export "402-group-identifications"

{` Chapter 4, sec:firstgroupexamples: the trivial group, permutation and
   symmetric groups, cyclic groups, products, and the group of a circle. `}

def set_is_groupoid (A : Type) (hA : isSet A) : isGroupoid A ≔ x y ↦ prop_is_set (Id A x y) (hA x y)

def set_loops_contractible (A : Type) (hA : isSet A) (a : A) : BookIsContr (Id A a a)
  ≔ (refl a, p ↦ hA a a (refl a) p)

def contractible_groupoid (A : Type) (h : BookIsContr A) : isGroupoid A
  ≔ set_is_groupoid A (prop_is_set A (contractible_prop A (native_contraction A h)))

{` Paths in components and in the type of sets, from paths of the
   underlying objects (lem:subtype-eq-=). The first component of the
   resulting path is the given path. `}
def component_path (A : Type) (a : A) (u v : NativeComponent A a) (p : Id A (u .fst) (v .fst))
  : Id (NativeComponent A a) u v
  ≔ subtype_equal A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x)) u v p

def set_types_path (S T : SetTypes) (e : Equiv (S .fst) (T .fst)) : Id SetTypes S T
  ≔ subtype_equal Type isSet isset_isprop S T (ua (S .fst) (T .fst) e)

{` ex:groups (ex:trivgroup). For a contractible type C and c : C,
   mkgroup (C, c) is a group; the unit group is the case (Unit, star). `}
def contractible_group (C : Type) (c : C) (h : BookIsContr C) : Group
  ≔ mkgroup (C, c, contractible_connected C h, contractible_groupoid C h)

def unit_contraction : BookIsContr Unit ≔ book_contraction Unit unit_contractible

def unit_group : Group ≔ contractible_group Unit star. unit_contraction

{` The book's definition of the trivial group: TG ≔ Aut_Prop(true), with
   true the proposition Unit. `}
def true_proposition : PropTypes ≔ (Unit, unit_prop)

def props_groupoid : isGroupoid PropTypes ≔ set_is_groupoid PropTypes propositions_set

def trivial_group : Group ≔ automorphism_group PropTypes props_groupoid true_proposition

{` Litmus: both trivial groups have contractible symmetries. `}
def unit_group_usym_contractible : BookIsContr (USym unit_group)
  ≔ set_loops_contractible Unit unit_set star.

def trivial_group_usym_contractible : BookIsContr (USym trivial_group)
  ≔ book_contractibility_equiv (Id PropTypes true_proposition true_proposition) (USym trivial_group)
      (canonical_inverse_equiv (USym trivial_group) (Id PropTypes true_proposition true_proposition)
        (automorphism_group_usym_equiv PropTypes props_groupoid true_proposition))
      .map (set_loops_contractible PropTypes propositions_set true_proposition)

{` ex:groups (ex:genpermgroup). Σ_S ≔ Aut_Set(S), with BΣ_S ≡ (Set_(S), S). `}
def permutation_group (S : SetTypes) : Group ≔ automorphism_group SetTypes sets_groupoid S

def permutation_group_usym_equiv (S : SetTypes)
  : Equiv (USym (permutation_group S)) (Equiv (S .fst) (S .fst))
  ≔ compose_equiv (USym (permutation_group S)) (Id SetTypes S S) (Equiv (S .fst) (S .fst))
      (automorphism_group_usym_equiv SetTypes sets_groupoid S) (set_paths_equiv S S)

{` The symmetry in Σ_S given by a permutation, and the action of a
   symmetry on S by transport; the action of the symmetry of e is e. `}
def permutation_symmetry (S : SetTypes) (e : Equiv (S .fst) (S .fst)) : USym (permutation_group S)
  ≔ component_path SetTypes S (component_point SetTypes S) (component_point SetTypes S) (set_types_path S S e)

def permutation_action (S : SetTypes) (p : USym (permutation_group S)) (x : S .fst) : S .fst
  ≔ transport Type (X ↦ X) (S .fst) (S .fst) (p .fst .fst) x

def permutation_symmetry_action (S : SetTypes) (e : Equiv (S .fst) (S .fst)) (x : S .fst)
  : Id (S .fst) (permutation_action S (permutation_symmetry S e) x) (e .map x)
  ≔ refl (e .map x)

{` The action is a group action in the book's orientation:
   (g · h)(x) = g(h(x)) and e(x) = x. `}
def permutation_action_mul (S : SetTypes) (g h : USym (permutation_group S)) (x : S .fst)
  : Id (S .fst) (permutation_action S (usym_mul (permutation_group S) g h) x)
      (permutation_action S g (permutation_action S h x))
  ≔ let P ≔ NativeComponent SetTypes S in let pt ≔ component_point SetTypes S in let X ≔ S .fst in
    concat X (permutation_action S (usym_mul (permutation_group S) g h) x)
      (transport Type (Y ↦ Y) X X (concat Type X X X (h .fst .fst) (g .fst .fst)) x)
      (permutation_action S g (permutation_action S h x))
      (refl ((q ↦ transport Type (Y ↦ Y) X X q x) : Id Type X X → X)
        (map_path_concat P Type (u ↦ u .fst .fst) pt pt pt h g))
      (transport_concat Type (Y ↦ Y) X X X (h .fst .fst) (g .fst .fst) x)

def permutation_action_unit (S : SetTypes) (x : S .fst)
  : Id (S .fst) (permutation_action S (usym_unit (permutation_group S)) x) x
  ≔ transport_refl Type (Y ↦ Y) (S .fst) x

{` ex:groups (ex:permgroup). Σ_n ≔ Aut_Set(Fin n). Its classifying type
   is the book's FinSet_n = Set_(Fin n) (BookFiniteSetsAt, module 186). `}
def standard_set (n : Nat) : SetTypes ≔ (Fin n, fin_set n)

def symmetric_group (n : Nat) : Group ≔ permutation_group (standard_set n)

def symmetric_group_classifying_type (n : Nat)
  : Id Type (BG (symmetric_group n) .carrier) (BookFiniteSetsAt n)
  ≔ refl (BookFiniteSetsAt n)

def symmetric_group_usym_equiv (n : Nat)
  : Equiv (USym (symmetric_group n)) (Equiv (Fin n) (Fin n))
  ≔ permutation_group_usym_equiv (standard_set n)

{` ex:cyclicgroups. C_m ≔ Aut_Cyc(Z/m, s), with BC_m ≡ (Cyc_m, (Z/m, s)),
   for every m : Nat, using the principal cycles of chapter 3: index 0 is the
   infinite cycle (Z, succ) (so C_0 ≃ Z) and m = n+1 is the standard
   (n+1)-cycle on Z/(n+1). Its classifying type is CycleComponent m by
   definition. cyclic_group_fin n is the book's literal Aut_Cyc(Fin (n+1), s)
   and is identified with cyclic_group (n+1). `}
def cyclic_group (m : Nat) : Group ≔ automorphism_group Cycles cycles_groupoid (principal_cycle m)

def cyclic_group_classifying_type (m : Nat) : Id Type (BG (cyclic_group m) .carrier) (CycleComponent m)
  ≔ refl (CycleComponent m)

def cyclic_group_fin (n : Nat) : Group ≔ automorphism_group Cycles cycles_groupoid (finite_fin_cycle n)

def cyclic_group_fin_path (n : Nat) : Id Group (cyclic_group_fin n) (cyclic_group (suc. n))
  ≔ refl ((c ↦ automorphism_group Cycles cycles_groupoid c) : Cycles → Group) (fin_remainder_cycle_path n)

{` cor:id-m-cycle: the symmetries of C_{n+1} are the n+1 elements of Fin (n+1)
   (evaluation at 0); so C_{n+1} is finite of cardinality n+1 (litmus). `}
def cyclic_group_fin_usym_equiv (n : Nat) : Equiv (USym (cyclic_group_fin n)) (Fin (suc. n))
  ≔ compose_equiv (USym (cyclic_group_fin n)) (Id Cycles (finite_fin_cycle n) (finite_fin_cycle n)) (Fin (suc. n))
      (automorphism_group_usym_equiv Cycles cycles_groupoid (finite_fin_cycle n))
      (native_equivalence (Id Cycles (finite_fin_cycle n) (finite_fin_cycle n)) (Fin (suc. n))
        (finite_cycle_loop_equiv n))

def cyclic_group_fin_finite (n : Nat) : IsFiniteGroup (cyclic_group_fin n)
  ≔ mere (Σ Nat (k ↦ Id Type (USym (cyclic_group_fin n)) (Fin k)))
      (suc. n, ua (USym (cyclic_group_fin n)) (Fin (suc. n)) (cyclic_group_fin_usym_equiv n))

def cyclic_group_fin_card (n : Nat)
  : Id Nat (group_card (cyclic_group_fin n) (cyclic_group_fin_finite n)) (suc. n)
  ≔ cardinality_from_path (USym (cyclic_group_fin n)) (cyclic_group_fin_finite n) (suc. n)
      (ua (USym (cyclic_group_fin n)) (Fin (suc. n)) (cyclic_group_fin_usym_equiv n))

{` ex:productofgroups. B(G × H) ≡ BG × BH pointed at (sh_G, sh_H). `}
def connected_product (A B : Type) (hA : Connected A) (hB : Connected B) : Connected (Product A B)
  ≔ (mere_rec A (Mere (Product A B)) (mere_isprop (Product A B))
       (a ↦ mere_rec B (Mere (Product A B)) (mere_isprop (Product A B))
         (b ↦ mere (Product A B) (a, b)) (hB .fst)) (hA .fst),
     u v ↦ mere_rec (Id A (u .fst) (v .fst)) (Mere (Id (Product A B) u v)) (mere_isprop (Id (Product A B) u v))
       (p ↦ mere_rec (Id B (u .snd) (v .snd)) (Mere (Id (Product A B) u v)) (mere_isprop (Id (Product A B) u v))
         (q ↦ mere (Id (Product A B) u v) (p, q)) (hB .snd (u .snd) (v .snd)))
       (hA .snd (u .fst) (v .fst)))

def groupoid_product (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) : isGroupoid (Product A B)
  ≔ hlevel_to_groupoid (Product A B)
      (hlevel_product (suc. (suc. (suc. zero.))) A B (groupoid_to_hlevel A hA) (groupoid_to_hlevel B hB))

def product_group (G H : Group) : Group
  ≔ mkgroup (Product (BG G .carrier) (BG H .carrier), (shape G, shape H),
      connected_product (BG G .carrier) (BG H .carrier) (bg_connected G) (bg_connected H),
      groupoid_product (BG G .carrier) (BG H .carrier) (bg_groupoid G) (bg_groupoid H))

{` lem:isEq-pair-bin=: USym(G × H) ≃ USym G × USym H, by the fieldwise
   identity types of pairs (as product_path_equiv of module 150). `}
def product_group_usym_equiv (G H : Group)
  : Equiv (USym (product_group G H)) (Product (USym G) (USym H))
  ≔ quasi_inverse_equiv (USym (product_group G H)) (Product (USym G) (USym H))
      (r ↦ (r .fst, r .snd)) (pq ↦ (pq .fst, pq .snd)) (r ↦ refl r) (pq ↦ refl pq)

{` ex:groups-morphisms, item 3: projections and inclusions, pointed by refl. `}
def product_group_proj1 (G H : Group) : GroupHom (product_group G H) G
  ≔ mkhom (product_group G H) G (t ↦ t .fst, refl (shape G))

def product_group_proj2 (G H : Group) : GroupHom (product_group G H) H
  ≔ mkhom (product_group G H) H (t ↦ t .snd, refl (shape H))

def product_group_incl1 (G H : Group) : GroupHom G (product_group G H)
  ≔ mkhom G (product_group G H) (z ↦ (z, shape H), refl (shape G, shape H))

def product_group_incl2 (G H : Group) : GroupHom H (product_group G H)
  ≔ mkhom H (product_group G H) (z ↦ (shape G, z), refl (shape G, shape H))

{` ex:groups-morphisms, item 2: the homomorphisms G → 1 and 1 → G. `}
def group_hom_to_unit (G : Group) : GroupHom G unit_group
  ≔ mkhom G unit_group (_ ↦ star., refl star.)

def group_hom_from_unit (G : Group) : GroupHom unit_group G
  ≔ mkhom unit_group G (_ ↦ shape G, refl (shape G))

{` ex:circlegroup, for every circle C: Z ≔ mkgroup (S¹, base). The
   constructed circle is instantiated in module 405. `}
def circle_pcg (C : CircleSignature) : PointedConnectedGroupoid
  ≔ (C .carrier, C .base, native_circle_connected C, circle_groupoid C)

def circle_group (C : CircleSignature) : Group ≔ mkgroup (circle_pcg C)

def circle_group_classifying (C : CircleSignature) : Id Pointed (BG (circle_group C)) (circle_pointed C)
  ≔ refl (circle_pointed C)

def circle_group_loop (C : CircleSignature) : USym (circle_group C) ≔ C .loop

{` cor:S1groupoid: n ↦ loopⁿ is an equivalence Z ≃ USym Z. `}
def circle_group_usym_integers (C : CircleSignature) : BookEquiv Int (USym (circle_group C))
  ≔ circle_integer_loop_equiv C
