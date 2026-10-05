export "07-o-functor"
export "../../../src/1333-pointed-circle-evaluation"

{` Bridges for fields.tex, the functor O (blocks 383, 420, 426, 466). blind_O is circle_pointed_maps
   by refl. blind_O_map and o_functor_map have the same underlying map; their pointing paths are both
   ap_{cst_*} of paths in the contractible Σ (x : B)(pt_B = x) (blind: pathover_of_eq of ρ'; ours: path
   induction), identified by o_constant_paths_agree. The blind ρ' (blind_O_rho) and the pointing of
   o_point_homotopy are the same term. blind_ev and pointed_circle_ev_pointed have the same underlying
   map and different (both path-induction) pointing paths; as maps into ΩA they are identified by
   cor:Id-(B->*loopsA). `}

{` def:O-functor (fields.tex:383). `}
def bridge_def_O (C : CircleSignature) (A : Pointed) : Id Pointed (blind_O C A) (circle_pointed_maps C A)
  ≔ refl (circle_pointed_maps C A)

def bridge_def_O_map_pt (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
        (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f))
      (blind_O_map_pt C A B f) (o_functor_map C A B f .snd)
  ≔ let fa ≔ f .fst (A .point) in
    o_constant_paths_agree C B fa (concat (B .carrier) (B .point) fa fa (f .snd) (refl fa))
      (blind_O_sigma_path (B .carrier) (B .point) fa (f .snd)) (o_point_path (B .carrier) (B .point) fa (f .snd))

def bridge_def_O_map (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap (blind_O C A) (blind_O C B)) (blind_O_map C A B f) (o_functor_map C A B f)
  ≔ (refl ((g ↦ book_pointed_compose (circle_pointed C) A B g f)
        : BookPointedMap (circle_pointed C) A → BookPointedMap (circle_pointed C) B),
     bridge_def_O_map_pt C A B f)

{` xca:O-functor (fields.tex:420). `}
def bridge_xca_O_functor_wild : blind_xca_O_functor_wild
  ≔ C ↦
    (A ↦ concat (BookPointedMap (blind_O C A) (blind_O C A))
       (blind_O_map C A A (book_pointed_identity A)) (o_functor_map C A A (book_pointed_identity A))
       (book_pointed_identity (blind_O C A))
       (bridge_def_O_map C A A (book_pointed_identity A)) (o_functor_map_id C A),
     A B D f g ↦
       let OA ≔ blind_O C A in let OB ≔ blind_O C B in let OD ≔ blind_O C D in
       concat (BookPointedMap OA OD)
         (blind_O_map C A D (book_pointed_compose A B D f g)) (o_functor_map C A D (book_pointed_compose A B D f g))
         (book_pointed_compose OA OB OD (blind_O_map C A B f) (blind_O_map C B D g))
         (bridge_def_O_map C A D (book_pointed_compose A B D f g))
         (concat (BookPointedMap OA OD)
           (o_functor_map C A D (book_pointed_compose A B D f g))
           (book_pointed_compose OA OB OD (o_functor_map C A B f) (o_functor_map C B D g))
           (book_pointed_compose OA OB OD (blind_O_map C A B f) (blind_O_map C B D g))
           (o_functor_map_comp C A B D f g)
           (inverse (BookPointedMap OA OD)
             (book_pointed_compose OA OB OD (blind_O_map C A B f) (blind_O_map C B D g))
             (book_pointed_compose OA OB OD (o_functor_map C A B f) (o_functor_map C B D g))
             (refl (book_pointed_compose OA OB OD) (bridge_def_O_map C A B f) (bridge_def_O_map C B D g)))))

def bridge_xca_O_functor_pt : blind_xca_O_functor_pt
  ≔ C A B f ↦
    let S ≔ circle_pointed C in
    let c ≔ book_pointed_constant S B in
    let Ofc ≔ book_pointed_compose S A B (book_pointed_constant S A) f in
    concat (Id (BookPointedMap S B) c Ofc) (blind_O_map_pt C A B f) (o_functor_map C A B f .snd)
      (equiv_inverse_map (Id (BookPointedMap S B) c Ofc) (PointedHomotopy S B c Ofc)
        (pointed_map_path_equiv S B c Ofc) (o_point_homotopy C B (f .fst (A .point)) (f .snd)))
      (bridge_def_O_map_pt C A B f) (o_functor_point_ptw C A B f)

{` rem:pointing-ev (fields.tex:426). `}
def bridge_def_ev (C : CircleSignature) (A : Pointed)
  : Id (BookPointedMap (blind_O C A) (Omega A)) (blind_ev C A) (pointed_circle_ev_pointed C A)
  ≔ loops_pointed_map_path_from_underlying A (circle_pointed_maps C A) (blind_ev C A) (pointed_circle_ev_pointed C A)
      (refl (pointed_circle_ev C A))

def bridge_rem_pointing_ev : blind_rem_pointing_ev
  ≔ C A ↦ (pointed_circle_ev_book_equiv C A, p ↦ pointed_circle_ev_inverse_beta C A p)

{` con:Omega-O (fields.tex:466). `}
def bridge_con_Omega_O_square : blind_con_Omega_O_square
  ≔ C A B f ↦
    loops_pointed_map_path_from_underlying B (circle_pointed_maps C A)
      (book_pointed_compose (blind_O C A) (Omega A) (Omega B) (blind_ev C A) (loops_pointed_map A B f))
      (book_pointed_compose (blind_O C A) (blind_O C B) (Omega B) (blind_O_map C A B f) (blind_ev C B))
      (omega_o_square C A B f .fst)

def bridge_con_Omega_O_equiv : blind_con_Omega_O_equiv
  ≔ C A B ↦
    let OA ≔ circle_pointed_maps C A in let OB ≔ circle_pointed_maps C B in
    let OAB ≔ BookPointedMap OA OB in let OAΩ ≔ BookPointedMap OA (Omega B) in
    let K ≔ omega_o_postcompose_equiv C A B in
    let e ≔ omega_o_equiv C A B in
    (book_equivalence (BookPointedMap (Omega A) (Omega B)) OAB e,
     (φ ↦ loops_pointed_map_path_from_underlying B OA
        (book_pointed_compose OA OB (Omega B) (e .map φ) (blind_ev C B))
        (book_pointed_compose OA (Omega A) (Omega B) (blind_ev C A) φ)
        (equiv_counit OAB OAΩ K (omega_o_precompose_equiv C A B .map φ) .fst),
      concat (BookPointedMap A B → OAB) (blind_O_map C A B) (o_functor_map C A B)
        (f ↦ e .map (loops_pointed_map A B f))
        (funext (BookPointedMap A B) (_ ↦ OAB) (blind_O_map C A B) (o_functor_map C A B)
          (f ↦ bridge_def_O_map C A B f))
        (o_functor_omega C A B)))
