export "bridge-01c-products"

{` Bridges for ex:Cm (line 568), xca:CG2isSG2 (line 653) and
   xca:RmloopCGm (line 658), blind file 01-groups.ny. The blind R_m maps
   into FiniteSetsAt (mere Type paths), ours (power_finset_map) into
   BookFiniteSetsAt (mere SetTypes paths). R_m^blind = to ∘ R_m^ours
   (bridge_rm_compare, by the universal property of the circle), and fibers
   over FiniteSetsAt and BookFiniteSetsAt are both fibers of paths of the
   underlying sets (subtype_path_equiv). `}

def BridgeFSA (n : Nat) : Type ≔ FiniteSetsAt n
def BridgeBFSA (n : Nat) : Type ≔ BookFiniteSetsAt n

def bridge_fsa_path_equiv (n : Nat) (X Y : FiniteSetsAt n) : Equiv (Id (FiniteSetsAt n) X Y) (Id SetTypes (X .fst) (Y .fst))
  ≔ subtype_path_equiv SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ mere_isprop (Id Type (Fin n) (S .fst))) X Y

def bridge_bfsa_path_equiv (n : Nat) (X Y : BookFiniteSetsAt n) : Equiv (Id (BookFiniteSetsAt n) X Y) (Id SetTypes (X .fst) (Y .fst))
  ≔ subtype_path_equiv SetTypes (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S)) (S ↦ mere_isprop (Id SetTypes (Fin n, fin_set n) S)) X Y

def bridge_finset_equiv_inv (n : Nat) : Equiv (FiniteSetsAt n) (BookFiniteSetsAt n)
  ≔ canonical_inverse_equiv (BookFiniteSetsAt n) (FiniteSetsAt n) (bridge_finset_equiv n)

{` R_m^blind = to ∘ R_m^ours. `}
def bridge_rm_loop_compare (n : Nat)
  : Id (Id (FiniteSetsAt (suc. n)) (blind_bn_finset (suc. n)) (blind_bn_finset (suc. n)))
      (blind_finset_loop (suc. n) (finite_fin_successor n))
      (refl (bridge_finset_to (suc. n)) (finite_successor_symmetry n))
  ≔ let F ≔ FiniteSetsAt (suc. n) in let b ≔ blind_bn_finset (suc. n) in
    let S ≔ standard_set (suc. n) in
    let E ≔ bridge_fsa_path_equiv (suc. n) b b in
    let E' ≔ bridge_bfsa_path_equiv (suc. n) (component_point SetTypes S) (component_point SetTypes S) in
    equivalence_injective (Id F b b) (Id SetTypes S S) E
      (blind_finset_loop (suc. n) (finite_fin_successor n)) (refl (bridge_finset_to (suc. n)) (finite_successor_symmetry n))
      (concat (Id SetTypes S S) (E .map (blind_finset_loop (suc. n) (finite_fin_successor n))) (set_types_path S S (finite_fin_successor n))
        (E' .map (finite_successor_symmetry n))
        (equiv_counit (Id F b b) (Id SetTypes S S) E (set_types_path S S (finite_fin_successor n)))
        (inverse (Id SetTypes S S) (E' .map (finite_successor_symmetry n)) (set_types_path S S (finite_fin_successor n))
          (equiv_counit (Id (BookFiniteSetsAt (suc. n)) (component_point SetTypes S) (component_point SetTypes S)) (Id SetTypes S S) E'
            (set_types_path S S (finite_fin_successor n)))))

def bridge_rm_compare (C : CircleSignature) (n : Nat)
  : Id (C .carrier → FiniteSetsAt (suc. n)) (blind_Rm_finset C n) (x ↦ bridge_finset_to (suc. n) (power_finset_map C n x))
  ≔ let F ≔ FiniteSetsAt (suc. n) in let B ≔ BookFiniteSetsAt (suc. n) in
    let to ≔ bridge_finset_to (suc. n) in
    let db : FreeLoop F ≔ (blind_bn_finset (suc. n), blind_finset_loop (suc. n) (finite_fin_successor n)) in
    let dout : FreeLoop B ≔ (shape (symmetric_group (suc. n)), finite_successor_symmetry n) in
    let fl : FreeLoop B → FreeLoop F ≔ u ↦ (to (u .fst), refl to (u .snd)) in
    equivalence_injective (C .carrier → F) (FreeLoop F) (circle_universal_property C F)
      (blind_Rm_finset C n) (x ↦ to (power_finset_map C n x))
      (concat (FreeLoop F) (circle_eval C F (blind_Rm_finset C n)) db (fl (circle_eval C B (power_finset_map C n)))
        (circle_rec_beta C F db)
        (concat (FreeLoop F) db (fl dout) (fl (circle_eval C B (power_finset_map C n)))
          (refl (blind_bn_finset (suc. n)), bridge_rm_loop_compare n)
          (refl fl (inverse (FreeLoop B) (circle_eval C B (power_finset_map C n)) dout (circle_rec_beta C B dout)))))

{` Fibers. `}
def bridge_rm_fiber_equiv (C : CircleSignature) (n : Nat) (X : FiniteSetsAt (suc. n))
  : Equiv (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) (bridge_finset_from (suc. n) X))
      (BlindRmFiber C n X)
  ≔ let F ≔ FiniteSetsAt (suc. n) in let B ≔ BookFiniteSetsAt (suc. n) in
    let to ≔ bridge_finset_to (suc. n) in
    let Z ≔ C .carrier in
    let mid ≔ Σ Z (z ↦ Id SetTypes (X .fst) (power_finset_map C n z .fst)) in
    compose_equiv (BookFiber Z B (power_finset_map C n) (bridge_finset_from (suc. n) X)) mid (BlindRmFiber C n X)
      (family_equiv Z (z ↦ Id B (bridge_finset_from (suc. n) X) (power_finset_map C n z))
        (z ↦ Id SetTypes (X .fst) (power_finset_map C n z .fst))
        (z ↦ bridge_bfsa_path_equiv (suc. n) (bridge_finset_from (suc. n) X) (power_finset_map C n z)))
      (compose_equiv mid (BookFiber Z F (x ↦ to (power_finset_map C n x)) X) (BlindRmFiber C n X)
        (canonical_inverse_equiv (BookFiber Z F (x ↦ to (power_finset_map C n x)) X) mid
          (family_equiv Z (z ↦ Id F X (to (power_finset_map C n z))) (z ↦ Id SetTypes (X .fst) (power_finset_map C n z .fst))
            (z ↦ bridge_fsa_path_equiv (suc. n) X (to (power_finset_map C n z)))))
        (id_to_equiv (BookFiber Z F (x ↦ to (power_finset_map C n x)) X) (BlindRmFiber C n X)
          (refl ((f ↦ BookFiber Z F f X) : (Z → F) → Type)
            (inverse (Z → F) (blind_Rm_finset C n) (x ↦ to (power_finset_map C n x)) (bridge_rm_compare C n)))))

def bridge_set_trunc_equiv (A B : Type) (e : Equiv A B) : Equiv (SetTrunc A) (SetTrunc B)
  ≔ id_to_equiv (SetTrunc A) (SetTrunc B) (refl SetTrunc (ua A B e))

def bridge_rm_trunc_fiber_equiv (C : CircleSignature) (n : Nat) (X : FiniteSetsAt (suc. n))
  : Equiv (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) (bridge_finset_from (suc. n) X)))
      (SetTrunc (BlindRmFiber C n X))
  ≔ bridge_set_trunc_equiv (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) (bridge_finset_from (suc. n) X))
      (BlindRmFiber C n X) (bridge_rm_fiber_equiv C n X)

{` ex:Cm: BC'_m. `}
def bridge_cm_carrier_equiv (C : CircleSignature) (n : Nat)
  : Equiv (ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n)) (BlindBCGprimeCarrier C n)
  ≔ let F ≔ FiniteSetsAt (suc. n) in let B ≔ BookFiniteSetsAt (suc. n) in
    let P : B → Type ≔ Y ↦ SetTrunc (BookFiber (C .carrier) B (power_finset_map C n) Y) in
    compose_equiv (ZeroImage (C .carrier) B (power_finset_map C n)) (Σ F (X ↦ P (bridge_finset_from (suc. n) X)))
      (BlindBCGprimeCarrier C n)
      (canonical_inverse_equiv (Σ F (X ↦ P (bridge_finset_from (suc. n) X))) (ZeroImage (C .carrier) B (power_finset_map C n))
        (sigma_pullback_equiv F B (bridge_finset_equiv_inv (suc. n)) P))
      (family_equiv F (X ↦ P (bridge_finset_from (suc. n) X)) (X ↦ SetTrunc (BlindRmFiber C n X))
        (bridge_rm_trunc_fiber_equiv C n))

def bridge_ex_Cm_prime_ptconn : blind_ex_Cm_prime_ptconn
  ≔ C n ↦
    let Z ≔ ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) in
    let X ≔ circle_map_image_pcg C n (power_finset_pointed C n) in
    (connected_equiv Z (BlindBCGprimeCarrier C n) (bridge_cm_carrier_equiv C n) .map (X .connected),
     hlevel_to_groupoid (BlindBCGprimeCarrier C n)
       (hlevel_equiv (suc. (suc. (suc. zero.))) Z (BlindBCGprimeCarrier C n) (bridge_cm_carrier_equiv C n)
         (groupoid_to_hlevel Z (X .groupoid))))

{` ex:Cm: cycle structures. Ours: power_fiber_cycle_structures (to
   CycleStructuresOn, structures merely equal to the standard cycle); the
   blind target is chapter 3's CycleStructures (cyclic permutations), the
   same for an (n+1)-element set by the period classification
   (cycle_periods_imply_paths, finite_cycle_periods_multiples). `}
def bridge_cycle_structures_iff (n : Nat) (Y : BookFiniteSetsAt (suc. n)) (h : Mere (Id Type (Y .fst .fst) (Fin (suc. n))))
  (t : Equiv (Y .fst .fst) (Y .fst .fst))
  : Product (Cyclic (Y .fst .fst) t → Mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)))
      (Mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)) → Cyclic (Y .fst .fst) t)
  ≔ let X ≔ Y .fst .fst in
    (cyc ↦ let c : Cycles ≔ ((Y .fst, t), cyc) in
       mere_rec (Id Cycles (finite_fin_cycle n) c) (Mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)))
         (mere_isprop (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)))
         (p ↦ mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)) (refl ((u ↦ u .fst) : Cycles → Permutations) p))
         (cycle_periods_imply_paths (finite_fin_cycle n) c
           (concat (Subtypes Int) (CyclePeriods (finite_fin_cycle n)) (Multiples (suc. n)) (CyclePeriods c)
             (fin_standard_periods n)
             (inverse (Subtypes Int) (CyclePeriods c) (Multiples (suc. n)) (finite_cycle_periods_multiples c n h)))),
     m ↦ mere_rec (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t)) (Cyclic X t) (cyclic_prop X t)
       (p ↦ transport Permutations (u ↦ Cyclic (u .fst .fst) (u .snd)) (finite_fin_cycle n .fst) (Y .fst, t) p
         (finite_fin_successor_cyclic n))
       m)

def bridge_ex_Cm_cycle_structures : blind_ex_Cm_cycle_structures
  ≔ C n X ↦
    let Y ≔ bridge_finset_from (suc. n) X in
    let T ≔ X .fst .fst in
    let h : Mere (Id Type T (Fin (suc. n)))
      ≔ mere_rec (Id Type (Fin (suc. n)) T) (Mere (Id Type T (Fin (suc. n)))) (mere_isprop (Id Type T (Fin (suc. n))))
          (p ↦ mere (Id Type T (Fin (suc. n))) (inverse Type (Fin (suc. n)) T p)) (X .snd) in
    book_equivalence (SetTrunc (BlindRmFiber C n X)) (CycleStructures T)
      (compose_equiv (SetTrunc (BlindRmFiber C n X))
        (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) Y)) (CycleStructures T)
        (canonical_inverse_equiv (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) Y))
          (SetTrunc (BlindRmFiber C n X)) (bridge_rm_trunc_fiber_equiv C n X))
        (compose_equiv (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) Y))
          (CycleStructuresOn n Y) (CycleStructures T)
          (power_fiber_cycle_structures C n Y)
          (family_equiv (Equiv T T) (t ↦ Mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t))) (Cyclic T)
            (t ↦ iff_equiv (Mere (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t))) (Cyclic T t)
              (mere_isprop (Id Permutations (finite_fin_cycle n .fst) (Y .fst, t))) (cyclic_prop T t)
              (bridge_cycle_structures_iff n Y h t .snd) (bridge_cycle_structures_iff n Y h t .fst)))))

{` xca:CG2isSG2 (line 653). `}
def bridge_xca_CG2isSG2 : blind_xca_CG2isSG2
  ≔ C ↦
    let B ≔ BookFiniteSetsAt two in
    let P : B → Type ≔ Y ↦ BookIsContr (SetTrunc (BookFiber (C .carrier) B (power_finset_map C (suc. zero.)) Y)) in
    let Y0 ≔ bridge_finset_from two (blind_bn_finset two) in
    let p : Id B (shape (symmetric_group two)) Y0
      ≔ equiv_inverse_map (Id B (shape (symmetric_group two)) Y0) (Id SetTypes (standard_set two) (standard_set two))
          (bridge_bfsa_path_equiv two (shape (symmetric_group two)) Y0) (refl (standard_set two)) in
    book_contractibility_equiv (SetTrunc (BookFiber (C .carrier) B (power_finset_map C (suc. zero.)) Y0))
      (SetTrunc (BlindRmFiber C (suc. zero.) (blind_bn_finset two)))
      (bridge_rm_trunc_fiber_equiv C (suc. zero.) (blind_bn_finset two))
      .map (transport B P (shape (symmetric_group two)) Y0 p (rm_two_fiber_contractible C))

{` ex:Cm: the projection Cyc_m → FinSet_m (line 568). prj = to ∘ (our
   cycle_forget_set); its fibers are ours (cycle_forget_fiber_equiv) up to
   the translation of structures merely equal to (bn m, s): ours are
   equivalences in Permutations, the blind ones endomaps in Σ Type (Y → Y). `}
def BridgeEndoT : Type ≔ Σ Type (Y ↦ Y → Y)

def bridge_perm_to_endo (p : Permutations) : BridgeEndoT ≔ (p .fst .fst, p .snd .map)

def bridge_endo_to_perm (n : Nat) (u : BridgeEndoT)
  (q : Id BridgeEndoT (Fin (suc. n), finite_fin_successor n .map) u)
  : (hs : isSet (u .fst)) (he : isEquiv (u .fst) (u .fst) (u .snd)) →
    Id Permutations (finite_fin_cycle n .fst) ((u .fst, hs), (u .snd, he))
  ≔ J BridgeEndoT (Fin (suc. n), finite_fin_successor n .map)
      (v q ↦ (hs : isSet (v .fst)) (he : isEquiv (v .fst) (v .fst) (v .snd)) →
        Id Permutations (finite_fin_cycle n .fst) ((v .fst, hs), (v .snd, he)))
      (hs he ↦ ((refl (Fin (suc. n)), isset_isprop (Fin (suc. n)) (fin_set (suc. n)) hs),
                (refl (finite_fin_successor n .map),
                 isequiv_isprop (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n .map) (finite_fin_successor n .equiv) he)))
      u q

def bridge_endo_isequiv (n : Nat) (u : BridgeEndoT) (m : Mere (Id BridgeEndoT u (Fin (suc. n), finite_fin_successor n .map)))
  : isEquiv (u .fst) (u .fst) (u .snd)
  ≔ mere_rec (Id BridgeEndoT u (Fin (suc. n), finite_fin_successor n .map)) (isEquiv (u .fst) (u .fst) (u .snd))
      (isequiv_isprop (u .fst) (u .fst) (u .snd))
      (q ↦ transport BridgeEndoT (v ↦ isEquiv (v .fst) (v .fst) (v .snd)) (Fin (suc. n), finite_fin_successor n .map) u
        (inverse BridgeEndoT u (Fin (suc. n), finite_fin_successor n .map) q) (finite_fin_successor n .equiv))
      m

def BridgeBlindStructures (n : Nat) (S : SetTypes) : Type
  ≔ Σ (S .fst → S .fst) (t ↦ Mere (Id BridgeEndoT (S .fst, t) (Fin (suc. n), finite_fin_successor n .map)))

def bridge_structures_equiv (n : Nat) (Y : BookFiniteSetsAt (suc. n))
  : Equiv (CycleStructuresOn n Y) (BridgeBlindStructures n (Y .fst))
  ≔ let X ≔ Y .fst .fst in let S ≔ Y .fst in
    let s0 ≔ finite_fin_cycle n .fst in
    let e0 : BridgeEndoT ≔ (Fin (suc. n), finite_fin_successor n .map) in
    let M ≔ (t : X → X) ↦ Mere (Id BridgeEndoT (X, t) e0) in
    let M' ≔ (t : Equiv X X) ↦ Mere (Id Permutations s0 (S, t)) in
    let fwd : CycleStructuresOn n Y → BridgeBlindStructures n S
      ≔ u ↦ (u .fst .map,
          mere_rec (Id Permutations s0 (S, u .fst)) (M (u .fst .map)) (mere_isprop (Id BridgeEndoT (X, u .fst .map) e0))
            (p ↦ mere (Id BridgeEndoT (X, u .fst .map) e0)
              (inverse BridgeEndoT e0 (X, u .fst .map) (refl bridge_perm_to_endo p)))
            (u .snd)) in
    let bwd : BridgeBlindStructures n S → CycleStructuresOn n Y
      ≔ u ↦ let he ≔ bridge_endo_isequiv n (X, u .fst) (u .snd) in
        ((u .fst, he),
         mere_rec (Id BridgeEndoT (X, u .fst) e0) (M' (u .fst, he)) (mere_isprop (Id Permutations s0 (S, (u .fst, he))))
           (q ↦ mere (Id Permutations s0 (S, (u .fst, he)))
             (bridge_endo_to_perm n (X, u .fst) (inverse BridgeEndoT (X, u .fst) e0 q) (S .snd) he))
           (u .snd)) in
    quasi_inverse_equiv (CycleStructuresOn n Y) (BridgeBlindStructures n S) fwd bwd
      (u ↦ subtype_equal (Equiv X X) M' (t ↦ mere_isprop (Id Permutations s0 (S, t))) (bwd (fwd u)) u
        (equiv_path X X (bwd (fwd u) .fst) (u .fst) (refl (u .fst .map))))
      (u ↦ subtype_equal (X → X) M (t ↦ mere_isprop (Id BridgeEndoT (X, t) e0)) (fwd (bwd u)) u (refl (u .fst)))

def bridge_cm_prj (n : Nat) (c : NativeComponent Cycles (finite_fin_cycle n)) : FiniteSetsAt (suc. n)
  ≔ bridge_finset_to (suc. n) (cycle_forget_set n c)

def bridge_ex_Cm_projection : blind_ex_Cm_projection
  ≔ n ↦
    let K ≔ NativeComponent Cycles (finite_fin_cycle n) in
    let F ≔ FiniteSetsAt (suc. n) in let B ≔ BookFiniteSetsAt (suc. n) in
    (bridge_cm_prj n,
     (c ↦ refl (c .fst .fst .fst),
      X ↦
        let Y ≔ bridge_finset_from (suc. n) X in
        let mid ≔ Σ K (c ↦ Id SetTypes (X .fst) (c .fst .fst .fst)) in
        book_equivalence (BookFiber K F (bridge_cm_prj n) X) (BridgeBlindStructures n (X .fst))
          (compose_equiv (BookFiber K F (bridge_cm_prj n) X) mid (BridgeBlindStructures n (X .fst))
            (family_equiv K (c ↦ Id F X (bridge_cm_prj n c)) (c ↦ Id SetTypes (X .fst) (c .fst .fst .fst))
              (c ↦ bridge_fsa_path_equiv (suc. n) X (bridge_cm_prj n c)))
            (compose_equiv mid (BookFiber K B (cycle_forget_set n) Y) (BridgeBlindStructures n (X .fst))
              (canonical_inverse_equiv (BookFiber K B (cycle_forget_set n) Y) mid
                (family_equiv K (c ↦ Id B Y (cycle_forget_set n c)) (c ↦ Id SetTypes (X .fst) (c .fst .fst .fst))
                  (c ↦ bridge_bfsa_path_equiv (suc. n) Y (cycle_forget_set n c))))
              (compose_equiv (BookFiber K B (cycle_forget_set n) Y) (CycleStructuresOn n Y) (BridgeBlindStructures n (X .fst))
                (cycle_forget_fiber_equiv n Y) (bridge_structures_equiv n Y))))))

{` ex:Cm: BC'_m ≃ BC_m as pointed types. Both are images of pointed maps
   S¹ →* FinSet_m (Q below); along a pointed equivalence of targets the
   images agree (bridge_image_compose, by pointed-equivalence induction);
   R_m^blind is to ∘ R_m^ours as pointed maps (pointed universal property
   of the circle); then ours (cyclic_image_path). `}
def BridgeImageQ (C : CircleSignature) (B : Type) (b : B) (k : BookPointedMap (circle_pointed C) (B, b)) : Pointed
  ≔ (ZeroImage (C .carrier) B (k .fst), (b, set_trunc (BookFiber (C .carrier) B (k .fst) b) (C .base, k .snd)))

def bridge_pointed_right_unit (X : Pointed) (B : Type) (b : B) (k : BookPointedMap X (B, b))
  : Id (BookPointedMap X (B, b)) k (book_pointed_compose X (B, b) (B, b) k (identity B, refl b))
  ≔ (refl (k .fst), inverse (Id B b (k .fst (X .point)))
      (concat B b b (k .fst (X .point)) (refl b) (k .snd)) (k .snd) (concat_1p B b (k .fst (X .point)) (k .snd)))

def bridge_pointed_equiv_induction (B : Type) (b : B)
  (P : (B' : Type) (b' : B') (e : Equiv B B') (ep : Id B' b' (e .map b)) → Type)
  (base : P B b (identity_equiv B) (refl b))
  (B' : Type) (b' : B') (e : Equiv B B') (ep : Id B' b' (e .map b)) : P B' b' e ep
  ≔ equivalence_induction B (B'' e' ↦ (b'' : B'') (ep' : Id B'' b'' (e' .map b)) → P B'' b'' e' ep')
      (b'' ep' ↦
        transport (Id B b'' b) (P B b'' (identity_equiv B)) (inverse B b b'' (inverse B b'' b ep')) ep'
          (inverse_inverse B b'' b ep')
          (J B b (y q ↦ P B y (identity_equiv B) (inverse B b y q)) (transport (Id B b b) (P B b (identity_equiv B)) (refl b) (inverse B b b (refl b))
              (inverse (Id B b b) (inverse B b b (refl b)) (refl b) (inverse_refl B b)) base)
            b'' (inverse B b'' b ep')))
      B' e b' ep

def bridge_image_compose (C : CircleSignature) (B : Type) (b : B) (k : BookPointedMap (circle_pointed C) (B, b))
  (B' : Type) (b' : B') (e : Equiv B B') (ep : Id B' b' (e .map b))
  : Id Pointed (BridgeImageQ C B b k)
      (BridgeImageQ C B' b' (book_pointed_compose (circle_pointed C) (B, b) (B', b') k (e .map, ep)))
  ≔ bridge_pointed_equiv_induction B b
      (B'' b'' e' ep' ↦ Id Pointed (BridgeImageQ C B b k)
        (BridgeImageQ C B'' b'' (book_pointed_compose (circle_pointed C) (B, b) (B'', b'') k (e' .map, ep'))))
      (refl (BridgeImageQ C B b) (bridge_pointed_right_unit (circle_pointed C) B b k))
      B' b' e ep

def bridge_rm_pointed_compare (C : CircleSignature) (n : Nat)
  : Id (BookPointedMap (circle_pointed C) (FiniteSetsAt (suc. n), blind_bn_finset (suc. n)))
      (book_pointed_compose (circle_pointed C) (BG (symmetric_group (suc. n))) (FiniteSetsAt (suc. n), blind_bn_finset (suc. n))
        (power_finset_pointed C n) (bridge_finset_to (suc. n), refl (blind_bn_finset (suc. n))))
      (blind_Rm_finset C n, blind_Rm_finset_base C n)
  ≔ let F ≔ FiniteSetsAt (suc. n) in let b ≔ blind_bn_finset (suc. n) in
    let X ≔ circle_pointed C in let Y ≔ BG (symmetric_group (suc. n)) in let Z : Pointed ≔ (F, b) in
    let tp : BookPointedMap Y Z ≔ (bridge_finset_to (suc. n), refl b) in
    let k' ≔ book_pointed_compose X Y Z (power_finset_pointed C n) tp in
    let kb : BookPointedMap X Z ≔ (blind_Rm_finset C n, blind_Rm_finset_base C n) in
    let L ≔ Id F b b in
    let fss ≔ finite_successor_symmetry n in
    equivalence_injective (BookPointedMap X Z) L (pointed_circle_universal_property C F b) k' kb
      (calc
        loops_map X Z k' (C .loop)
        = loops_map Y Z tp (loops_map X Y (power_finset_pointed C n) (C .loop))
          by loops_map_compose_pointwise X Y Z (power_finset_pointed C n) tp (C .loop)
        = loops_map Y Z tp fss
          by refl (loops_map Y Z tp) (pointed_circle_loop_rec_beta C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) fss)
        = refl (bridge_finset_to (suc. n)) fss
          by loop_conjugate_at_refl F b (refl (bridge_finset_to (suc. n)) fss)
        = blind_finset_loop (suc. n) (finite_fin_successor n)
          by inverse L (blind_finset_loop (suc. n) (finite_fin_successor n)) (refl (bridge_finset_to (suc. n)) fss)
            (bridge_rm_loop_compare n)
        = loops_map X Z kb (C .loop)
          by inverse L (loops_map X Z kb (C .loop)) (blind_finset_loop (suc. n) (finite_fin_successor n))
            (pointed_circle_loop_rec_beta C F b (blind_finset_loop (suc. n) (finite_fin_successor n))) ∎)

def bridge_pointed_path_equiv (X Y : Pointed) (p : Id Pointed X Y) : BookPointedEquiv X Y
  ≔ transport Pointed (Y' ↦ BookPointedEquiv X Y') X Y p
      ((identity (X .carrier), refl (X .point)), identity_book_equiv (X .carrier) .equiv)

def bridge_cm_prime_path (C : CircleSignature) (n : Nat) : Id Pointed (blind_BCGprime C n) (blind_BG (blind_CG n))
  ≔ let F ≔ FiniteSetsAt (suc. n) in let b ≔ blind_bn_finset (suc. n) in
    let B ≔ BookFiniteSetsAt (suc. n) in let sh ≔ shape (symmetric_group (suc. n)) in
    let k' ≔ book_pointed_compose (circle_pointed C) (B, sh) (F, b) (power_finset_pointed C n)
      (bridge_finset_to (suc. n), refl b) in
    let kb : BookPointedMap (circle_pointed C) (F, b) ≔ (blind_Rm_finset C n, blind_Rm_finset_base C n) in
    concat Pointed (blind_BCGprime C n) (BridgeImageQ C B sh (power_finset_pointed C n)) (blind_BG (blind_CG n))
      (concat Pointed (BridgeImageQ C F b kb) (BridgeImageQ C F b k') (BridgeImageQ C B sh (power_finset_pointed C n))
        (refl (BridgeImageQ C F b) (inverse (BookPointedMap (circle_pointed C) (F, b)) k' kb (bridge_rm_pointed_compare C n)))
        (inverse Pointed (BridgeImageQ C B sh (power_finset_pointed C n)) (BridgeImageQ C F b k')
          (bridge_image_compose C B sh (power_finset_pointed C n) F b (bridge_finset_equiv (suc. n)) (refl b))))
      (group_path_pointed_equiv (cyclic_image_group C n) (cyclic_group_fin n) .map (cyclic_image_path C n))

def bridge_ex_Cm_prime_equiv : blind_ex_Cm_prime_equiv
  ≔ C n ↦ bridge_pointed_path_equiv (blind_BCGprime C n) (blind_BG (blind_CG n)) (bridge_cm_prime_path C n)
