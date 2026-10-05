export "../../../src/224-constructed-circle-checks"
export "../../../src/66-cycle-identity-classification"
export "../../../src/172-power-bundle-degree"
export "../../../src/162-pointed-maps"
export "../../../src/242-cycle-structures-count"
export "../../../src/284-chapter-two-completions"
export "../../../src/184-cyc-n-connected-coverings"
export "../../../src/175-permutation-factorial"
export "../../../src/81-circle-degree-coverings"
export "../../../src/150-paths-over-and-pairs"

{` Blind statements, chapter 4 (group.tex), section "The type of groups".
   Conventions: the book's truncation is native Mere, isconn is Connected,
   isgrpd is isGroupoid, pointed maps are BookPointedMap (pt_Y = f(pt_X)).
   The book's path product q·p (first p, then q) is concat p q. `}

{` Helper: sets are groupoids. `}
def blind_set_groupoid (A : Type) (h : isSet A) : isGroupoid A
  ≔ hlevel_to_groupoid A (hlevel_raise (suc. (suc. zero.)) A (set_to_hlevel_two A h))

{` def:pt-conn-groupoid (and the margin notations U^{<=1}, U^{>0}). `}
def BlindPtConnGroupoid : Type ≔ Σ Type (A ↦ Product A (Product (Connected A) (isGroupoid A)))
def BlindGroupoidTypes : Type ≔ Σ Type isGroupoid
def BlindConnectedTypes : Type ≔ Σ Type Connected

def blind_ptconn_pointed (X : BlindPtConnGroupoid) : Pointed ≔ (X .fst, X .snd .fst)

{` def:typegroup. `}
def BlindGroup : Type ≔ Copy BlindPtConnGroupoid
def blind_mkgroup (X : BlindPtConnGroupoid) : BlindGroup ≔ copy. X

{` def:classifying-type: destructor B, classifying type, designated shape. `}
def blind_B (G : BlindGroup) : BlindPtConnGroupoid ≔ copy_value BlindPtConnGroupoid G
def blind_BG (G : BlindGroup) : Pointed ≔ blind_ptconn_pointed (blind_B G)
def blind_shape (G : BlindGroup) : blind_B G .fst ≔ blind_B G .snd .fst

{` def:looptype: loops X = (a = a), pointed at refl a. `}
def blind_loops (X : Pointed) : Pointed ≔ (Loop X, refl (X .point))

{` def:group-symmetries. `}
def BlindUSym (G : BlindGroup) : Type ≔ blind_loops (blind_BG G) .carrier
def blind_usym_is_set : Type ≔ (G : BlindGroup) → isSet (BlindUSym G)

{` def:finite-group. `}
def BlindIsFiniteGroup (G : BlindGroup) : Type ≔ IsFinite (BlindUSym G)
def blind_group_card (G : BlindGroup) (h : BlindIsFiniteGroup G) : Nat ≔ cardinality (BlindUSym G) h

{` def:automorphism-group. `}
def blind_component_groupoid (A : Type) (hA : isGroupoid A) (a : A) : isGroupoid (NativeComponent A a)
  ≔ hlevel_to_groupoid (NativeComponent A a)
      (hlevel_sigma (suc. (suc. (suc. zero.)))  A (x ↦ Mere (Id A a x)) (groupoid_to_hlevel A hA)
        (x ↦ prop_hlevel (suc. (suc. zero.)) (Mere (Id A a x)) (mere_isprop (Id A a x))))

def blind_component_point (A : Type) (a : A) : NativeComponent A a ≔ (a, mere (Id A a a) (refl a))

def blind_Aut (A : Type) (hA : isGroupoid A) (a : A) : BlindGroup
  ≔ blind_mkgroup (NativeComponent A a,
      (blind_component_point A a, (native_component_connected A a, blind_component_groupoid A hA a)))

{` ---- Helpers (no book content). ---- `}
def BlindIff (P Q : Type) : Type ≔ Product (P → Q) (Q → P)
def blind_three : Nat ≔ suc. (suc. (suc. zero.))
def blind_four : Nat ≔ suc. blind_three

def blind_groupoid_sigma (A : Type) (B : A → Type) (hA : isGroupoid A) (hB : (a : A) → isGroupoid (B a))
  : isGroupoid (Σ A B)
  ≔ hlevel_to_groupoid (Σ A B)
      (hlevel_sigma blind_three A B (groupoid_to_hlevel A hA) (a ↦ groupoid_to_hlevel (B a) (hB a)))

def blind_groupoid_pi (A : Type) (B : A → Type) (hB : (a : A) → isGroupoid (B a))
  : isGroupoid ((a : A) → B a)
  ≔ hlevel_to_groupoid ((a : A) → B a) (hlevel_pi blind_three A B (a ↦ groupoid_to_hlevel (B a) (hB a)))

def blind_mere_pair (A B : Type) (a : Mere A) (b : Mere B) : Mere (Product A B)
  ≔ mere_rec A (Mere (Product A B)) (mere_isprop (Product A B))
      (x ↦ mere_rec B (Mere (Product A B)) (mere_isprop (Product A B)) (y ↦ mere (Product A B) (x, y)) b) a

def blind_connected_product (A B : Type) (hA : Connected A) (hB : Connected B) : Connected (Product A B)
  ≔ (blind_mere_pair A B (hA .fst) (hB .fst), u v ↦
      mere_rec (Product (Id A (u .fst) (v .fst)) (Id B (u .snd) (v .snd))) (Mere (Id (Product A B) u v))
        (mere_isprop (Id (Product A B) u v))
        (pq ↦ mere (Id (Product A B) u v) (product_pair_path A B (u .fst) (v .fst) (u .snd) (v .snd) pq))
        (blind_mere_pair (Id A (u .fst) (v .fst)) (Id B (u .snd) (v .snd))
          (hA .snd (u .fst) (v .fst)) (hB .snd (u .snd) (v .snd))))

{` Standard finite sets bn n as sets and as elements of FinSet_n
   (FiniteSetsAt n = Σ_{S:Set} ||Fin n = S||, def:groupoidFin). `}
def blind_bn_set (n : Nat) : SetTypes ≔ (Fin n, fin_set n)
def blind_bn_finset (n : Nat) : FiniteSetsAt n ≔ (blind_bn_set n, mere (Id Type (Fin n) (Fin n)) (refl (Fin n)))

def blind_finsetn_groupoid (n : Nat) : isGroupoid (FiniteSetsAt n)
  ≔ blind_groupoid_sigma SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) sets_groupoid
      (S ↦ blind_set_groupoid (Mere (Id Type (Fin n) (S .fst)))
        (prop_is_set (Mere (Id Type (Fin n) (S .fst))) (mere_isprop (Id Type (Fin n) (S .fst)))))

def blind_set_loop (S : SetTypes) (e : Equiv (S .fst) (S .fst)) : Id SetTypes S S
  ≔ subtype_equal Type isSet isset_isprop S S (ua (S .fst) (S .fst) e)

def blind_finset_loop (n : Nat) (e : Equiv (Fin n) (Fin n)) : Id (FiniteSetsAt n) (blind_bn_finset n) (blind_bn_finset n)
  ≔ subtype_equal SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ mere_isprop (Id Type (Fin n) (S .fst)))
      (blind_bn_finset n) (blind_bn_finset n) (blind_set_loop (blind_bn_set n) e)

{` The swap of bn 2 is the successor modulo 2. `}
def blind_swap2 : Equiv (Fin two) (Fin two) ≔ finite_fin_successor (suc. zero.)

{` ex:base=base: (base = base) ≃ Z, n ↦ loop^n, addition ↦ composition. `}
def blind_ex_base_eq_base : Type
  ≔ (C : CircleSignature) →
    Σ (BookEquiv Int (Id (C .carrier) (C .base) (C .base))) (e ↦
      Product ((n : Int) → Id (Id (C .carrier) (C .base) (C .base)) (e .map n) (loop_power (C .carrier) (C .base) (C .loop) n))
        ((m n : Int) → Id (Id (C .carrier) (C .base) (C .base)) (e .map (int_add m n))
          (concat (C .carrier) (C .base) (C .base) (C .base) (e .map m) (e .map n))))

{` Example after ex:base=base: the recalled xca:C2 facts on bn 2 = bn 2,
   and the map S1 → FinSet_2 sending base to bn 2 and loop to swap. `}
def blind_ex_fin_two_symmetries : Type
  ≔ let sw ≔ ua (Fin two) (Fin two) blind_swap2 in
    Product ((p : Id Type (Fin two) (Fin two)) → Sum (Id (Id Type (Fin two) (Fin two)) p (refl (Fin two)))
        (Id (Id Type (Fin two) (Fin two)) p sw))
      (Product (Not (Id (Id Type (Fin two) (Fin two)) (refl (Fin two)) sw))
        (Id (Id Type (Fin two) (Fin two)) (concat Type (Fin two) (Fin two) (Fin two) sw sw) (refl (Fin two))))

def blind_ex_circle_to_finset_two : Type
  ≔ (C : CircleSignature) →
    Σ (C .carrier → FiniteSetsAt two) (f ↦
      Id (FreeLoop (FiniteSetsAt two)) (f (C .base), refl f (C .loop))
        (blind_bn_finset two, blind_finset_loop two blind_swap2))

{` rem:heap-preview: transport along f : a = a' compares a = a' with a = a. `}
def blind_rem_heap_preview : Type
  ≔ (A : Type) (a a' : A) (f : Id A a a') →
    BookIsEquiv (Id A a a') (Id A a a) (p ↦ concat A a a' a p (inverse A a a' f))

{` rem:whypointedconngpoid: fst : A_(a) → A induces (a,!) = (a,!) ≃ a = a. `}
def blind_rem_component_loops : Type
  ≔ (A : Type) (a : A) →
    BookIsEquiv (Id (NativeComponent A a) (blind_component_point A a) (blind_component_point A a)) (Id A a a)
      (map_path (NativeComponent A a) A (u ↦ u .fst) (blind_component_point A a) (blind_component_point A a))

{` xca:defgroup. The second statement is literally for arbitrary A; the
   corrected variant assumes A connected (the context of the exercise). `}
def blind_xca_defgroup_connected : Type
  ≔ (A : Type) (a : A) → BlindIff (Connected A) ((x : A) → Mere (Id A a x))
def blind_xca_defgroup_groupoid : Type
  ≔ (A : Type) (a : A) → BlindIff (isGroupoid A) (isSet (Id A a a))
def blind_xca_defgroup_groupoid_corrected : Type
  ≔ (A : Type) (a : A) → Connected A → BlindIff (isGroupoid A) (isSet (Id A a a))
def blind_xca_defgroup_equiv : Type
  ≔ BookEquiv BlindPtConnGroupoid
      (Σ Type (A ↦ Σ A (a ↦ Product ((x : A) → Mere (Id A a x)) (isSet (Id A a a)))))

{` Remark after xca:defgroup: isconn and isgrpd are propositions. `}
def blind_rem_ptconn_props : Type ≔ (A : Type) → Product (isProp (Connected A)) (isProp (isGroupoid A))

{` def:group-symmetries footnote: USym is a set -- blind_usym_is_set above. `}

{` rem:aut. `}
def blind_rem_aut_equiv : Type ≔ BookIsEquiv BlindGroup BlindPtConnGroupoid blind_B
def blind_rem_aut_subtype : Type
  ≔ (X Y : BlindPtConnGroupoid) →
    BookIsEquiv (Id BlindPtConnGroupoid X Y) (Id Pointed (blind_ptconn_pointed X) (blind_ptconn_pointed Y))
      (map_path BlindPtConnGroupoid Pointed blind_ptconn_pointed X Y)
def blind_rem_aut_paths : Type
  ≔ (G H : BlindGroup) → BookEquiv (Id BlindGroup G H) (Id Pointed (blind_BG G) (blind_BG H))

{` rem:BG-convention: functions out of Group are determined on mkgroup X. `}
def blind_rem_bg_convention : Type
  ≔ (T : BlindGroup → Type) →
    BookIsEquiv ((G : BlindGroup) → T G) ((X : BlindPtConnGroupoid) → T (blind_mkgroup X))
      (f ↦ X ↦ f (blind_mkgroup X))

{` rem:symmetriesofnonconnectedgroupoids. `}
def blind_rem_component_fst_equiv : Type
  ≔ (A : Type) (a : A) → Connected A → BookIsEquiv (NativeComponent A a) A (u ↦ u .fst)
def blind_rem_group_is_aut_shape : Type
  ≔ (G : BlindGroup) → Id BlindGroup G (blind_Aut (blind_B G .fst) (blind_B G .snd .snd .snd) (blind_shape G))

{` ex:circlegroup. `}
def blind_ZZ (C : CircleSignature) : BlindGroup
  ≔ blind_mkgroup (C .carrier, (C .base, (native_circle_connected C, circle_groupoid C)))
def blind_ex_circlegroup_aut : Type
  ≔ (C : CircleSignature) → Id BlindGroup (blind_ZZ C) (blind_Aut (C .carrier) (circle_groupoid C) (C .base))

{` xca:groups: two different identifications Z = Aut_Cyc(Z, s). `}
def blind_xca_groups : Type
  ≔ (C : CircleSignature) →
    let A ≔ blind_Aut Cycles cycles_groupoid infinite_cycle in
    Σ (Id BlindGroup (blind_ZZ C) A) (p ↦ Σ (Id BlindGroup (blind_ZZ C) A) (q ↦
      Not (Id (Id BlindGroup (blind_ZZ C) A) p q)))

{` ex:groups. `}
def blind_true_prop : PropTypes ≔ (Unit, unit_prop)
def blind_props_groupoid : isGroupoid PropTypes ≔ blind_set_groupoid PropTypes propositions_set
def blind_TG : BlindGroup ≔ blind_Aut PropTypes blind_props_groupoid blind_true_prop
def blind_SG (n : Nat) : BlindGroup ≔ blind_Aut SetTypes sets_groupoid (blind_bn_set n)
def blind_SG_set (S : SetTypes) : BlindGroup ≔ blind_Aut SetTypes sets_groupoid S

def blind_ex_true_loops_contractible : Type ≔ BookIsContr (Id PropTypes blind_true_prop blind_true_prop)
def blind_ex_trivgroup_contractible : Type
  ≔ (X : BlindPtConnGroupoid) → BookIsContr (X .fst) → Id BlindGroup blind_TG (blind_mkgroup X)
def blind_ex_trivgroup_set : Type
  ≔ (S : SetTypes) (x : S .fst) → Id BlindGroup blind_TG (blind_Aut (S .fst) (blind_set_groupoid (S .fst) (S .snd)) x)
def blind_ex_permgroup_classifying : Type
  ≔ (n : Nat) → Id Pointed (blind_BG (blind_SG n)) (FiniteSetsAt n, blind_bn_finset n)
def blind_ex_permgroup_finset_n : Type
  ≔ (n : Nat) → Id BlindGroup (blind_SG n) (blind_Aut (FiniteSetsAt n) (blind_finsetn_groupoid n) (blind_bn_finset n))
def blind_ex_permgroup_universe : Type
  ≔ (n : Nat) → Σ (isGroupoid (NativeComponent Type (Fin n))) (h ↦
      Id BlindGroup (blind_SG n)
        (blind_mkgroup (NativeComponent Type (Fin n),
          (blind_component_point Type (Fin n), (native_component_connected Type (Fin n), h)))))

{` xca:group-example-details. `}
def blind_xca_aut_prop_trivial : Type
  ≔ (P : PropTypes) → Id BlindGroup blind_TG (blind_Aut PropTypes blind_props_groupoid P)
def blind_xca_sg0_trivial : Type ≔ Id BlindGroup (blind_SG zero.) blind_TG
def blind_xca_sg1_trivial : Type ≔ Id BlindGroup (blind_SG (suc. zero.)) blind_TG
def blind_xca_sgfalse_trivial : Type ≔ Id BlindGroup (blind_SG_set (Empty, empty_set)) blind_TG
def blind_xca_aut_finset_sg : Type
  ≔ (n : Nat) → Id BlindGroup (blind_Aut FiniteSets finite_sets_groupoid (standard_finite_set n)) (blind_SG n)
def blind_xca_aut_nat_int : Type
  ≔ Id BlindGroup (blind_SG_set (Nat, nat_set)) (blind_SG_set (Int, int_set))

{` ex:cyclicgroups. CG n is the cyclic group of order m = n+1,
   Aut_Cyc(bn m, s) with the literal standard cycle on Fin m. `}
def blind_CG (n : Nat) : BlindGroup ≔ blind_Aut Cycles cycles_groupoid (finite_fin_cycle n)

def BlindEndoSets : Type ≔ Σ SetTypes (X ↦ X .fst → X .fst)
def blind_endo_sets_groupoid : isGroupoid BlindEndoSets
  ≔ blind_groupoid_sigma SetTypes (X ↦ X .fst → X .fst) sets_groupoid
      (X ↦ blind_set_groupoid (X .fst → X .fst) (pi_set (X .fst) (_ ↦ X .fst) (_ ↦ X .snd)))

def blind_circle_families_groupoid (C : CircleSignature) : isGroupoid (C .carrier → SetTypes)
  ≔ blind_groupoid_pi (C .carrier) (_ ↦ SetTypes) (_ ↦ sets_groupoid)

def blind_ZmodmZ (C : CircleSignature) (n : Nat) : BlindGroup
  ≔ blind_Aut (C .carrier → SetTypes) (blind_circle_families_groupoid C) (power_circle_family C n)

def blind_positive_suc (n : Nat) : BookLt zero. (suc. n)
  ≔ (suc. n, (p ↦ nat_encode (suc. n) zero. p, refl (suc. n)))

def blind_ex_cyclicgroups_chain : Type
  ≔ (C : CircleSignature) (n : Nat) →
    let A1 ≔ blind_Aut BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map) in
    let A2 ≔ blind_Aut (Coverings (C .carrier)) (coverings_groupoid (C .carrier))
               (circle_degree_cover C (suc. n) (blind_positive_suc n)) in
    Product (Id BlindGroup (blind_CG n) A1) (Product (Id BlindGroup A1 A2) (Id BlindGroup A2 (blind_ZmodmZ C n)))

def blind_ex_cyclic_order_one : Type ≔ Id BlindGroup (blind_CG zero.) blind_TG
def blind_ex_cyclic_order_two : Type ≔ Id BlindGroup (blind_CG (suc. zero.)) (blind_SG two)
def blind_ex_cyclic_card : Type ≔ (n : Nat) → Mere (Id Type (Fin (suc. n)) (BlindUSym (blind_CG n)))
def blind_ex_symmetric_card : Type ≔ (n : Nat) → Mere (Id Type (Fin (factorial n)) (BlindUSym (blind_SG n)))

{` ex:Cm. R_m : S1 → FinSet_m (base ↦ bn m, loop ↦ s), m = n+1. The
   circle's recursion computes on base only up to the beta path, so the
   book's refl (bn m) becomes that path. `}
def blind_Rm_finset (C : CircleSignature) (n : Nat) : C .carrier → FiniteSetsAt (suc. n)
  ≔ circle_rec C (FiniteSetsAt (suc. n)) (blind_bn_finset (suc. n), blind_finset_loop (suc. n) (finite_fin_successor n))

def blind_Rm_finset_base (C : CircleSignature) (n : Nat)
  : Id (FiniteSetsAt (suc. n)) (blind_bn_finset (suc. n)) (blind_Rm_finset C n (C .base))
  ≔ inverse (FiniteSetsAt (suc. n)) (blind_Rm_finset C n (C .base)) (blind_bn_finset (suc. n))
      (circle_rec_beta C (FiniteSetsAt (suc. n))
        (blind_bn_finset (suc. n), blind_finset_loop (suc. n) (finite_fin_successor n)) .fst)

def BlindRmFiber (C : CircleSignature) (n : Nat) (X : FiniteSetsAt (suc. n)) : Type
  ≔ BookFiber (C .carrier) (FiniteSetsAt (suc. n)) (blind_Rm_finset C n) X

def BlindBCGprimeCarrier (C : CircleSignature) (n : Nat) : Type
  ≔ Σ (FiniteSetsAt (suc. n)) (X ↦ SetTrunc (BlindRmFiber C n X))

def blind_BCGprime (C : CircleSignature) (n : Nat) : Pointed
  ≔ (BlindBCGprimeCarrier C n,
      (blind_bn_finset (suc. n),
        set_trunc (BlindRmFiber C n (blind_bn_finset (suc. n))) (C .base, blind_Rm_finset_base C n)))

{` The projection Cyc_m → FinSet_m forgetting t, with fiber over X the
   set Σ_{t:X→X} ||(X,t) = (bn m, s)||. `}
def blind_ex_Cm_projection : Type
  ≔ (n : Nat) →
    Σ (NativeComponent Cycles (finite_fin_cycle n) → FiniteSetsAt (suc. n)) (prj ↦
      Product ((c : NativeComponent Cycles (finite_fin_cycle n)) → Id SetTypes (prj c .fst) (c .fst .fst .fst))
        ((X : FiniteSetsAt (suc. n)) →
          BookEquiv (BookFiber (NativeComponent Cycles (finite_fin_cycle n)) (FiniteSetsAt (suc. n)) prj X)
            (Σ (X .fst .fst → X .fst .fst) (t ↦
              Mere (Id (Σ Type (Y ↦ Y → Y)) (X .fst .fst, t) (Fin (suc. n), finite_fin_successor n .map))))))

{` BCG'_m is a pointed connected groupoid; CG'_m is parametrized by that fact. `}
def blind_ex_Cm_prime_ptconn : Type
  ≔ (C : CircleSignature) (n : Nat) → Product (Connected (BlindBCGprimeCarrier C n)) (isGroupoid (BlindBCGprimeCarrier C n))

def blind_CGprime (h : blind_ex_Cm_prime_ptconn) (C : CircleSignature) (n : Nat) : BlindGroup
  ≔ blind_mkgroup (BlindBCGprimeCarrier C n, (blind_BCGprime C n .point, (h C n .fst, h C n .snd)))

def blind_ex_Cm_prime_equiv : Type
  ≔ (C : CircleSignature) (n : Nat) → BookPointedEquiv (blind_BCGprime C n) (blind_BG (blind_CG n))

def blind_ex_Cm_cycle_structures : Type
  ≔ (C : CircleSignature) (n : Nat) (X : FiniteSetsAt (suc. n)) →
    BookEquiv (SetTrunc (BlindRmFiber C n X)) (CycleStructures (X .fst .fst))

{` xca:CG2isSG2. `}
def blind_xca_CG2isSG2 : Type
  ≔ (C : CircleSignature) → BookIsContr (SetTrunc (BlindRmFiber C (suc. zero.) (blind_bn_finset two)))

{` xca:RmloopCGm: the symmetries of the shape of BCG'_m are, via the
   underlying identification bn m = bn m, the permutations generated by s. `}
def blind_xca_RmloopCGm : Type
  ≔ (C : CircleSignature) (n : Nat) →
    let F ≔ Fin (suc. n) in
    let L ≔ Loop (blind_BCGprime C n) in
    Σ (BookEquiv L (Σ (Equiv F F) (σ ↦
        Mere (Σ Int (k ↦ Id (F → F) (σ .map) (permutation_power F (finite_fin_successor n) k)))))) (e ↦
      (l : L) → Id (F → F) (e .map l .fst .map)
        (transport Type (identity Type) F F
          (map_path (BlindBCGprimeCarrier C n) Type (u ↦ u .fst .fst .fst)
            (blind_BCGprime C n .point) (blind_BCGprime C n .point) l)))

{` ex:productofgroups. `}
def blind_group_product (G H : BlindGroup) : BlindGroup
  ≔ let A ≔ blind_B G in
    let B ≔ blind_B H in
    blind_mkgroup (Product (A .fst) (B .fst),
      ((A .snd .fst, B .snd .fst),
        (blind_connected_product (A .fst) (B .fst) (A .snd .snd .fst) (B .snd .snd .fst),
          hlevel_to_groupoid (Product (A .fst) (B .fst))
            (hlevel_product blind_three (A .fst) (B .fst)
              (groupoid_to_hlevel (A .fst) (A .snd .snd .snd)) (groupoid_to_hlevel (B .fst) (B .snd .snd .snd))))))

def blind_klein : BlindGroup ≔ blind_group_product (blind_SG two) (blind_SG two)
def blind_ex_klein_four : Type ≔ Mere (Id Type (Fin blind_four) (BlindUSym blind_klein))
def blind_ex_product_usym : Type
  ≔ (G H : BlindGroup) → BookEquiv (BlindUSym (blind_group_product G H)) (Product (BlindUSym G) (BlindUSym H))

{` xca:klein-not-cyclic. `}
def blind_xca_klein_not_cyclic : Type ≔ Not (Id BlindGroup (blind_CG blind_three) blind_klein)

{` xca:bigproductfunext (i): finite products of connected groupoids are connected. `}
def blind_xca_bigproduct_connected : Type
  ≔ (S : FiniteSets) (Y : S .fst .fst → Type) → ((s : S .fst .fst) → Connected (Y s))
    → ((s : S .fst .fst) → isGroupoid (Y s)) → Connected ((s : S .fst .fst) → Y s)

{` ex:bigproductofgroups, parametrized by (i), which makes the definition sensible. `}
def blind_group_bigproduct (h : blind_xca_bigproduct_connected) (S : FiniteSets) (G : S .fst .fst → BlindGroup)
  : BlindGroup
  ≔ blind_mkgroup ((s : S .fst .fst) → blind_B (G s) .fst,
      (s ↦ blind_shape (G s),
        (h S (s ↦ blind_B (G s) .fst) (s ↦ blind_B (G s) .snd .snd .fst) (s ↦ blind_B (G s) .snd .snd .snd),
          blind_groupoid_pi (S .fst .fst) (s ↦ blind_B (G s) .fst) (s ↦ blind_B (G s) .snd .snd .snd))))

def blind_ex_bigproduct_ptw : Type
  ≔ (h : blind_xca_bigproduct_connected) (S : FiniteSets) (G : S .fst .fst → BlindGroup) →
    BookIsEquiv (BlindUSym (blind_group_bigproduct h S G)) ((s : S .fst .fst) → BlindUSym (G s))
      (happly (S .fst .fst) (s ↦ blind_B (G s) .fst) (s ↦ blind_shape (G s)) (s ↦ blind_shape (G s)))

{` xca:bigproductfunext (ii), for the standard 2-element set bn 2. `}
def blind_fin_two_zero : Fin two ≔ inl. (inr. star.)
def blind_fin_two_one : Fin two ≔ inr. star.
def blind_xca_bigproduct_binary : Type
  ≔ (h : blind_xca_bigproduct_connected) (G : Fin two → BlindGroup) →
    Id BlindGroup (blind_group_bigproduct h (standard_finite_set two) G)
      (blind_group_product (G blind_fin_two_zero) (G blind_fin_two_one))

{` def:abgp. The book's product g·h is trans(h)(g) (first h, then g),
   i.e. concat h g. `}
def BlindIsAb (G : BlindGroup) : Type
  ≔ let A ≔ blind_B G .fst in
    let s ≔ blind_shape G in
    (g h : BlindUSym G) → Id (BlindUSym G) (concat A s s s h g) (concat A s s s g h)
def BlindAbGroup : Type ≔ Σ BlindGroup BlindIsAb
def blind_isab_prop : Type ≔ (G : BlindGroup) → isProp (BlindIsAb G)

{` exer:first examples. `}
def blind_xca_S2_abelian : Type ≔ BlindIsAb (blind_SG two)
def blind_xca_S3_not_abelian : Type ≔ Not (BlindIsAb (blind_SG blind_three))
def blind_xca_product_abelian : Type
  ≔ (G H : BlindGroup) → BlindIsAb G → BlindIsAb H → BlindIsAb (blind_group_product G H)

{` rem:whatAREabeliangroups. No wedge is available; by the universal
   property of BG ∨ BG a factorization of the fold map through
   BG ∨ BG → BG × BG is a map m : BG × BG → BG with m(x, sh) = x,
   m(sh, y) = y, agreeing at (sh, sh). Claim: this type is a proposition
   equivalent to isAb(G). `}
def BlindAbFoldFactorization (G : BlindGroup) : Type
  ≔ let A ≔ blind_B G .fst in
    let s ≔ blind_shape G in
    Σ (A → A → A) (m ↦ Σ ((x : A) → Id A (m x s) x) (l ↦ Σ ((y : A) → Id A (m s y) y) (r ↦
      Id (Id A (m s s) s) (l s) (r s))))
def blind_rem_abelian_fold : Type
  ≔ (G : BlindGroup) → Product (isProp (BlindAbFoldFactorization G)) (BlindIff (BlindAbFoldFactorization G) (BlindIsAb G))

{` xca (line 779): changing the base point gives a merely equal group. `}
def blind_xca_change_basepoint : Type
  ≔ (X : BlindPtConnGroupoid) (b : X .fst) →
    Mere (Id BlindGroup (blind_mkgroup X) (blind_mkgroup (X .fst, (b, X .snd .snd))))

{` xca:typegroupisgroupoid, and Aut(G) parametrized by it. `}
def blind_xca_group_paths_set : Type ≔ (G H : BlindGroup) → isSet (Id BlindGroup G H)
def blind_xca_typegroup_groupoid : Type ≔ isGroupoid BlindGroup
def blind_AutGroup (h : blind_xca_typegroup_groupoid) (G : BlindGroup) : BlindGroup ≔ blind_Aut BlindGroup h G
