export "872-bouquet-induction"
export "873-s-action-paths"
export "410-pointed-connected-groupoids"

{` The classifying type of a free S-set (generalizing modules 221-223):
   B ≔ the component of (R, s) in the type of types with S-indexed
   endomaps, based at (R, s).  Loops at the base are S-equivariant
   automorphisms of (R, s), hence (every S-endomap being invertible) the
   points of R, by evaluation at r0 of the transport along the loop
   (fsc_loops_equiv).  loop_a is the automorphism φ_{s_a(r0)}, and
   evaluation turns left composition with loop_a into s_a (fsc_loop_left),
   so the S-set of loops is identified with (R, s) and is free.  With
   module 871/872 this gives a FreeGroupSignature S for every free S-set,
   without higher inductive types or axioms
   (free_group_signature_from_free_sset), and a group when R is a set. `}

def fsc_actions (S : Type) (D : FreeSSet S) : SActionTypes S ≔ (D .carrier, a x ↦ D .act a .map x)

def FreeSSetClassifying (S : Type) (D : FreeSSet S) : Type ≔ NativeComponent (SActionTypes S) (fsc_actions S D)

def fsc_base (S : Type) (D : FreeSSet S) : FreeSSetClassifying S D
  ≔ component_point (SActionTypes S) (fsc_actions S D)

def FscLoops (S : Type) (D : FreeSSet S) : Type
  ≔ Id (FreeSSetClassifying S D) (fsc_base S D) (fsc_base S D)

def FscIsos (S : Type) (D : FreeSSet S) : Type ≔ SActionIsos S (fsc_actions S D) (fsc_actions S D)

{` S-automorphisms of (R, s) are the points of R, by evaluation at r0. `}
def fsc_iso_eval (S : Type) (D : FreeSSet S) (i : FscIsos S D) : D .carrier ≔ i .fst .map (D .origin)

def fsc_endo_iso (S : Type) (D : FreeSSet S) (m : SSetMaps S (D .carrier) (D .carrier) (D .act) (D .act))
  : FscIsos S D
  ≔ (free_sset_endo_equiv S D m, m .snd)

def fsc_iso_inv (S : Type) (D : FreeSSet S) (u : D .carrier) : FscIsos S D
  ≔ fsc_endo_iso S D (free_sset_endo S D u)

def fsc_endo_iso_eta (S : Type) (D : FreeSSet S) (i : FscIsos S D)
  : Id (FscIsos S D) (fsc_endo_iso S D (i .fst .map, i .snd)) i
  ≔ (equiv_path (D .carrier) (D .carrier) (free_sset_endo_equiv S D (i .fst .map, i .snd)) (i .fst) (refl (i .fst .map)),
     refl (i .snd))

def fsc_iso_eval_equiv (S : Type) (D : FreeSSet S) : Equiv (FscIsos S D) (D .carrier)
  ≔ let R ≔ D .carrier in
    quasi_inverse_equiv (FscIsos S D) R (fsc_iso_eval S D) (fsc_iso_inv S D)
      (i ↦ concat (FscIsos S D) (fsc_iso_inv S D (fsc_iso_eval S D i)) (fsc_endo_iso S D (i .fst .map, i .snd)) i
        (refl (fsc_endo_iso S D)
          (free_sset_maps_equal S D R (D .act) (free_sset_endo S D (i .fst .map (D .origin))) (i .fst .map, i .snd)
            (free_sset_endo_origin S D (i .fst .map (D .origin)))))
        (fsc_endo_iso_eta S D i))
      (u ↦ free_sset_endo_origin S D u)

{` Loops of the base ≃ R: t ↦ transport of r0 along the carrier path of t. `}
def fsc_loops_equiv (S : Type) (D : FreeSSet S) : Equiv (FscLoops S D) (D .carrier)
  ≔ let A ≔ SActionTypes S in let rho ≔ fsc_actions S D in
    compose_equiv (FscLoops S D) (Id A rho rho) (D .carrier)
      (component_path_equiv A rho (fsc_base S D) (fsc_base S D))
      (compose_equiv (Id A rho rho) (FscIsos S D) (D .carrier) (s_action_paths_equiv S rho rho) (fsc_iso_eval_equiv S D))

def fsc_loop_eval (S : Type) (D : FreeSSet S) (t : FscLoops S D) : D .carrier ≔ fsc_loops_equiv S D .map t

{` Litmus: the evaluation is literally transport of r0 along the loop. `}
def fsc_loop_eval_transport (S : Type) (D : FreeSSet S) (t : FscLoops S D)
  : Id (D .carrier) (fsc_loop_eval S D t) (t .fst .fst .trr (D .origin))
  ≔ refl (t .fst .fst .trr (D .origin))

{` The generating loops. `}
def fsc_letter_iso (S : Type) (D : FreeSSet S) (a : S) : FscIsos S D
  ≔ fsc_iso_inv S D (D .act a .map (D .origin))

def fsc_letter_path (S : Type) (D : FreeSSet S) (a : S) : Id (SActionTypes S) (fsc_actions S D) (fsc_actions S D)
  ≔ equiv_inverse_map (Id (SActionTypes S) (fsc_actions S D) (fsc_actions S D)) (FscIsos S D)
      (s_action_paths_equiv S (fsc_actions S D) (fsc_actions S D)) (fsc_letter_iso S D a)

def fsc_loop (S : Type) (D : FreeSSet S) (a : S) : FscLoops S D
  ≔ component_path (SActionTypes S) (fsc_actions S D) (fsc_base S D) (fsc_base S D) (fsc_letter_path S D a)

def fsc_loop_eval_letter (S : Type) (D : FreeSSet S) (a : S)
  : Id (D .carrier) (fsc_loop_eval S D (fsc_loop S D a)) (D .act a .map (D .origin))
  ≔ let rho ≔ fsc_actions S D in
    concat (D .carrier) (fsc_loop_eval S D (fsc_loop S D a)) (fsc_iso_eval S D (fsc_letter_iso S D a))
      (D .act a .map (D .origin))
      (refl (fsc_iso_eval S D)
        (equiv_counit (Id (SActionTypes S) rho rho) (FscIsos S D) (s_action_paths_equiv S rho rho) (fsc_letter_iso S D a)))
      (free_sset_endo_origin S D (D .act a .map (D .origin)))

{` Evaluation turns left composition with loop_a into s_a. `}
def fsc_loop_left (S : Type) (D : FreeSSet S) (a : S) (t : FscLoops S D)
  : Id (D .carrier)
      (fsc_loop_eval S D (concat (FreeSSetClassifying S D) (fsc_base S D) (fsc_base S D) (fsc_base S D) (fsc_loop S D a) t))
      (D .act a .map (fsc_loop_eval S D t))
  ≔ let A ≔ SActionTypes S in let rho ≔ fsc_actions S D in
    let B ≔ FreeSSetClassifying S D in let b ≔ fsc_base S D in
    let r0 ≔ D .origin in
    let ev ≔ ((p ↦ s_action_path_evaluate S rho rho p r0) : Id A rho rho → D .carrier) in
    calc
      fsc_loop_eval S D (concat B b b b (fsc_loop S D a) t)
      = ev (concat A rho rho rho (fsc_loop S D a .fst) (t .fst))
        by refl ev (map_path_concat B A (u ↦ u .fst) b b b (fsc_loop S D a) t)
      = s_action_path_evaluate S rho rho (t .fst) (ev (fsc_loop S D a .fst))
        by carrier_path_evaluate_concat A (u ↦ u .fst) rho rho rho (fsc_loop S D a .fst) (t .fst) r0
      = s_action_path_evaluate S rho rho (t .fst) (D .act a .map r0)
        by refl (s_action_path_evaluate S rho rho (t .fst)) (fsc_loop_eval_letter S D a)
      = D .act a .map (ev (t .fst))
        by s_action_paths_equiv S rho rho .map (t .fst) .snd a r0 ∎

{` The S-set of loops (left composition with the loops) is (R, s). `}
def fsc_loop_sset (S : Type) (D : FreeSSet S) : SSets S
  ≔ (FscLoops S D, loop_sset S (FreeSSetClassifying S D) (fsc_base S D) (fsc_loop S D) (fsc_base S D))

def fsc_loop_intertwine (S : Type) (D : FreeSSet S) (a : S) (x : D .carrier)
  : Id (FscLoops S D) (equiv_inverse_map (FscLoops S D) (D .carrier) (fsc_loops_equiv S D) (D .act a .map x))
      (concat (FreeSSetClassifying S D) (fsc_base S D) (fsc_base S D) (fsc_base S D) (fsc_loop S D a)
        (equiv_inverse_map (FscLoops S D) (D .carrier) (fsc_loops_equiv S D) x))
  ≔ let B ≔ FreeSSetClassifying S D in let b ≔ fsc_base S D in
    let psi ≔ equiv_inverse_map (FscLoops S D) (D .carrier) (fsc_loops_equiv S D) in
    inverse_at_known_point (FscLoops S D) (D .carrier) (fsc_loops_equiv S D)
      (concat B b b b (fsc_loop S D a) (psi x)) (D .act a .map x)
      (concat (D .carrier) (fsc_loop_eval S D (concat B b b b (fsc_loop S D a) (psi x)))
        (D .act a .map (fsc_loop_eval S D (psi x))) (D .act a .map x)
        (fsc_loop_left S D a (psi x))
        (refl (D .act a .map) (equiv_counit (FscLoops S D) (D .carrier) (fsc_loops_equiv S D) x)))

def fsc_loop_sset_path (S : Type) (D : FreeSSet S) : Id (SSets S) (D .carrier, D .act) (fsc_loop_sset S D)
  ≔ sset_path_from_equiv S (D .carrier) (D .act) (FscLoops S D)
      (canonical_inverse_equiv (FscLoops S D) (D .carrier) (fsc_loops_equiv S D))
      (loop_sset S (FreeSSetClassifying S D) (fsc_base S D) (fsc_loop S D) (fsc_base S D))
      (fsc_loop_intertwine S D)

def fsc_merely_based (S : Type) (D : FreeSSet S) (x : FreeSSetClassifying S D)
  : Mere (Id (FreeSSetClassifying S D) (fsc_base S D) x)
  ≔ let A ≔ SActionTypes S in let rho ≔ fsc_actions S D in
    mere_rec (Id A rho (x .fst)) (Mere (Id (FreeSSetClassifying S D) (fsc_base S D) x))
      (mere_isprop (Id (FreeSSetClassifying S D) (fsc_base S D) x))
      (p ↦ mere (Id (FreeSSetClassifying S D) (fsc_base S D) x) (component_path A rho (fsc_base S D) x p))
      (x .snd)

def fsc_free_loops_bouquet (S : Type) (D : FreeSSet S) : FreeLoopsBouquet S
  ≔ (FreeSSetClassifying S D, fsc_base S D, fsc_loop S D, fsc_merely_based S D,
     sset_weakly_free_transfer S (D .carrier, D .act) (fsc_loop_sset S D) (fsc_loop_sset_path S D)
       (free_sset_weakly_free S D))

{` Every free S-set on one generator yields a free group signature on S
   (no HITs, no axioms): carrier B, base, loops loop_a. `}
def free_group_signature_from_free_sset (S : Type) (D : FreeSSet S) : FreeGroupSignature S
  ≔ free_group_signature_from_free_loops S (fsc_free_loops_bouquet S D)

{` Litmus: the signature's carrier, base and loops are the constructed ones
   (judgmentally), and its universal property is evaluation. `}
def free_sset_signature_loop (S : Type) (D : FreeSSet S) (a : S)
  : Id (FscLoops S D) (free_group_signature_from_free_sset S D .loop a) (fsc_loop S D a)
  ≔ refl (fsc_loop S D a)

{` When R is a set, B is a groupoid and (B, base) is a group whose
   symmetries are the points of R. `}
def fsc_loops_set (S : Type) (D : FreeSSet S) (hR : isSet (D .carrier)) : isSet (FscLoops S D)
  ≔ hlevel_two_to_set (FscLoops S D)
      (hlevel_equiv (suc. (suc. zero.)) (D .carrier) (FscLoops S D)
        (canonical_inverse_equiv (FscLoops S D) (D .carrier) (fsc_loops_equiv S D))
        (set_to_hlevel_two (D .carrier) hR))

def free_sset_classifying_groupoid (S : Type) (D : FreeSSet S) (hR : isSet (D .carrier))
  : isGroupoid (FreeSSetClassifying S D)
  ≔ based_set_loops_groupoid (FreeSSetClassifying S D) (fsc_base S D) (fsc_merely_based S D) (fsc_loops_set S D hR)

def free_sset_group (S : Type) (D : FreeSSet S) (hR : isSet (D .carrier)) : Group
  ≔ mkgroup (FreeSSetClassifying S D, fsc_base S D,
      native_component_connected (SActionTypes S) (fsc_actions S D),
      free_sset_classifying_groupoid S D hR)

def free_sset_group_usym_equiv (S : Type) (D : FreeSSet S) (hR : isSet (D .carrier))
  : Equiv (USym (free_sset_group S D hR)) (D .carrier)
  ≔ fsc_loops_equiv S D

def free_sset_group_generator (S : Type) (D : FreeSSet S) (hR : isSet (D .carrier)) (a : S)
  : USym (free_sset_group S D hR)
  ≔ fsc_loop S D a
