export "03-ptd-homotopies"
export "../../../src/1335-swap-and-loops"

{` Bridges for fields.tex, pointed homotopies (blocks 188, 223, 244, 257).
   blind_ptw is pointed_map_path_equiv .map by refl. The blind composite k' ·ptw k differs from
   pointed_homotopy_compose only in the bracketing of the three 2-paths of its pointing path
   ((assoc⁻¹ · ap) · k'_pt versus assoc⁻¹ · (ap · k'_pt)), bridged by one concat_assoc.
   blind_cst_ptd is pointed_constant_at by refl; blind_ptd_maps is pointed_maps_pointed by refl;
   blind_H_cst_equiv is constant_pointed_homotopy_equiv (module 1207) by refl. The blind variant ptw_* is
   built on pointed_map_path_equiv, ours (constant_loops_pointed_equiv) on the explicit
   pointed_map_path_explicit_equiv; their maps agree pointwise by pointed_map_path_equiv_ptw
   (module 289), hence so do their inverses. `}

{` Definition-level helper: two equivalences with pointwise equal maps have equal inverse maps. `}
def bridge_equiv_inverse_agree (A B : Type) (e e' : Equiv A B) (h : (a : A) → Id B (e .map a) (e' .map a)) (b : B)
  : Id A (equiv_inverse_map A B e b) (equiv_inverse_map A B e' b)
  ≔ let g ≔ equiv_inverse_map A B e in let g' ≔ equiv_inverse_map A B e' in
    concat A (g b) (g (e .map (g' b))) (g' b)
      (refl g (inverse B (e .map (g' b)) b
        (concat B (e .map (g' b)) (e' .map (g' b)) b (h (g' b)) (equiv_counit A B e' b))))
      (equiv_retraction A B e (g' b))

{` def:ptd-homotopy-compo (fields.tex:188). `}
def bridge_def_ptw (X Y : Pointed) (f g : BookPointedMap X Y) (p : Id (BookPointedMap X Y) f g)
  : Id (PointedHomotopy X Y f g) (blind_ptw X Y f g p) (pointed_map_path_equiv X Y f g .map p)
  ≔ refl (pointed_map_path_equiv X Y f g .map p)

def bridge_def_ptw_compose (X Y : Pointed) (f g h : BookPointedMap X Y)
  (k : PointedHomotopy X Y f g) (k' : PointedHomotopy X Y g h)
  : Id (PointedHomotopy X Y f h) (blind_ptw_compose X Y f g h k k') (pointed_homotopy_compose X Y f g h k k')
  ≔ let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let fa ≔ f .fst a in let ga ≔ g .fst a in let ha ≔ h .fst a in
    let X1 ≔ concat B y fa ha (f .snd) (concat B fa ga ha (k .fst a) (k' .fst a)) in
    let X3 ≔ concat B y ga ha (concat B y fa ga (f .snd) (k .fst a)) (k' .fst a) in
    let X2 ≔ concat B y ga ha (g .snd) (k' .fst a) in
    (refl (blind_ptw_compose X Y f g h k k' .fst),
     concat_assoc (Id B y ha) X1 X3 X2 (h .snd)
       (inverse (Id B y ha) X3 X1 (concat_assoc B y fa ga ha (f .snd) (k .fst a) (k' .fst a)))
       (refl ((r ↦ concat B y ga ha r (k' .fst a)) : Id B y ga → Id B y ha) (k .snd))
       (k' .snd))

{` con:ptd-homotopy-compo (fields.tex:223). `}
def bridge_con_ptd_homotopy_compo : blind_con_ptd_homotopy_compo
  ≔ X Y f g h p q ↦
    concat (PointedHomotopy X Y f h)
      (pointed_map_path_equiv X Y f h .map (concat (BookPointedMap X Y) f g h p q))
      (pointed_homotopy_compose X Y f g h (pointed_map_path_equiv X Y f g .map p) (pointed_map_path_equiv X Y g h .map q))
      (blind_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q))
      (ptw_concat_compose X Y f g h p q)
      (inverse (PointedHomotopy X Y f h)
        (blind_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q))
        (pointed_homotopy_compose X Y f g h (pointed_map_path_equiv X Y f g .map p) (pointed_map_path_equiv X Y g h .map q))
        (bridge_def_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q)))

{` Converse: our statement from the blind one. `}
def bridge_con_ptd_homotopy_compo_converse (b : blind_con_ptd_homotopy_compo) (X Y : Pointed) (f g h : BookPointedMap X Y)
  (p : Id (BookPointedMap X Y) f g) (q : Id (BookPointedMap X Y) g h)
  : Id (PointedHomotopy X Y f h) (pointed_map_path_equiv X Y f h .map (concat (BookPointedMap X Y) f g h p q))
      (pointed_homotopy_compose X Y f g h (pointed_map_path_equiv X Y f g .map p) (pointed_map_path_equiv X Y g h .map q))
  ≔ concat (PointedHomotopy X Y f h)
      (pointed_map_path_equiv X Y f h .map (concat (BookPointedMap X Y) f g h p q))
      (blind_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q))
      (pointed_homotopy_compose X Y f g h (pointed_map_path_equiv X Y f g .map p) (pointed_map_path_equiv X Y g h .map q))
      (b X Y f g h p q)
      (bridge_def_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q))

{` def:cst-ptd (fields.tex:244). `}
def bridge_def_cst_ptd (A B : Pointed)
  : Id ((u : Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x)) → BookPointedMap A B)
      (blind_cst_ptd A B) (pointed_constant_at A B)
  ≔ refl (pointed_constant_at A B)

def bridge_def_cst_ptd_domain_contr : blind_def_cst_ptd_domain_contr
  ≔ B ↦ pointed_constant_domain_contractible B

{` rem:loops-at-ptd-cst (fields.tex:257). `}
def bridge_def_ptd_maps (X Y : Pointed) : Id Pointed (blind_ptd_maps X Y) (pointed_maps_pointed X Y)
  ≔ refl (pointed_maps_pointed X Y)

def bridge_def_H_cst_equiv (X Y : Pointed)
  : Id (Equiv (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y)) (BookPointedMap X (Omega Y)))
      (blind_H_cst_equiv X Y) (constant_pointed_homotopy_equiv X Y)
  ≔ refl (constant_pointed_homotopy_equiv X Y)

def bridge_def_ptw_loops (X Y : Pointed) (r : Loop (blind_ptd_maps X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map r) (constant_loops_pointed_equiv X Y .map r)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) r)

def bridge_def_ptw_loops_inv (X Y : Pointed) (k : BookPointedMap X (Omega Y))
  : Id (Loop (blind_ptd_maps X Y)) (blind_ptw_loops_inv X Y k)
      (equiv_inverse_map (Loop (pointed_maps_pointed X Y)) (BookPointedMap X (Omega Y)) (constant_loops_pointed_equiv X Y) k)
  ≔ bridge_equiv_inverse_agree (Loop (pointed_maps_pointed X Y)) (BookPointedMap X (Omega Y))
      (blind_ptw_loops X Y) (constant_loops_pointed_equiv X Y) (bridge_def_ptw_loops X Y) k

def bridge_rem_loops_at_ptd_cst : blind_rem_loops_at_ptd_cst
  ≔ X Y ↦
    (book_equivalence (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
       (BookPointedMap X (Omega Y)) (constant_pointed_homotopy_equiv X Y),
     book_equivalence (Loop (pointed_maps_pointed X Y)) (BookPointedMap X (Omega Y)) (constant_loops_pointed_equiv X Y))
