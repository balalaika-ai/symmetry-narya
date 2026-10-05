export "503-orbits-and-stabilizers"

{` Chapter 5, sec:torsors: G-torsors (def:Gtorsor), the map
   P_- : BG →* (Torsors_G, P_G) (def:BG2TorsG), lem:pathsptransportiseq and
   lem:BGbytorsor (BG ≃ Torsors_G). `}

{` def:Gtorsor. Torsor_G ≔ Σ_{X : GSet} ‖P_G = X‖. `}
def Torsors (G : Group) : Type
  ≔ Σ (GSet G) (X ↦ Mere (Id (GSet G) (principal_gset G) X))

{` def:BG2TorsG. Each P_y is a G-torsor. The book argues via contractibility
   of the action type of P_y; here ‖P_G = P_y‖ is obtained directly from
   ‖sh_G = y‖ (connectedness of BG) and ap of P_-. `}
def gset_paths_is_torsor (G : Group) (y : BG G .carrier)
  : Mere (Id (GSet G) (principal_gset G) (gset_paths G y))
  ≔ mere_rec (Id (BG G .carrier) (shape G) y) (Mere (Id (GSet G) (principal_gset G) (gset_paths G y)))
      (mere_isprop (Id (GSet G) (principal_gset G) (gset_paths G y)))
      (p ↦ mere (Id (GSet G) (principal_gset G) (gset_paths G y))
        (map_path (BG G .carrier) (GSet G) (gset_paths G) (shape G) y p))
      (bg_connected G .snd (shape G) y)

def bg_to_torsors (G : Group) (y : BG G .carrier) : Torsors G ≔ (gset_paths G y, gset_paths_is_torsor G y)

def principal_torsor (G : Group) : Torsors G ≔ bg_to_torsors G (shape G)

def torsors_pointed (G : Group) : Pointed ≔ (Torsors G, principal_torsor G)

{` def:BG2TorsG. P_- : BG →* (Torsor_G, P_G), pointed by reflexivity. `}
def bg_to_torsors_pointed (G : Group) : BookPointedMap (BG G) (torsors_pointed G)
  ≔ (bg_to_torsors G, refl (principal_torsor G))

{` The action type of P_y is contractible, so P_y is transitive. `}
def gset_paths_action_type_contractible (G : Group) (y : BG G .carrier)
  : BookIsContr (ActionType G (gset_paths G y))
  ≔ book_pathspace_contractible (BG G .carrier) y

def gset_paths_transitive (G : Group) (y : BG G .carrier) : IsTransitive G (gset_paths G y)
  ≔ connected_action_type_transitive G (gset_paths G y)
      (contractible_connected (ActionType G (gset_paths G y)) (gset_paths_action_type_contractible G y))

{` rem:pathsptransport. Transport of p : y = x along q : y = z in the family
   P_-(x) is p q⁻¹ = concat q⁻¹ p, so in particular
   ev_{refl}(ap_{P_-}(q)) = q⁻¹ (typal). `}
def gset_paths_transport (G : Group) (y z x : BG G .carrier) (q : Id (BG G .carrier) y z)
  (p : Id (BG G .carrier) y x)
  : Id (Id (BG G .carrier) z x)
      (gset_path_transport G (gset_paths G y) (gset_paths G z) (map_path (BG G .carrier) (GSet G) (gset_paths G) y z q) x p)
      (concat (BG G .carrier) z y x (inverse (BG G .carrier) y z q) p)
  ≔ let B ≔ BG G .carrier in
    J B y
      (z q ↦ Id (Id B z x)
        (gset_path_transport G (gset_paths G y) (gset_paths G z) (map_path B (GSet G) (gset_paths G) y z q) x p)
        (concat B z y x (inverse B y z q) p))
      (concat (Id B y x)
        (gset_path_transport G (gset_paths G y) (gset_paths G y) (map_path B (GSet G) (gset_paths G) y y (refl y)) x p)
        p (concat B y y x (inverse B y y (refl y)) p)
        (transport_refl (GSet G) (W ↦ W x .fst) (gset_paths G y) p)
        (inverse (Id B y x) (concat B y y x (inverse B y y (refl y)) p) p (inverse_refl_concat B y x p)))
      z q

def gset_paths_ap_eval (G : Group) (y z : BG G .carrier) (q : Id (BG G .carrier) y z)
  : Id (Id (BG G .carrier) z y)
      (gset_path_eval G (gset_paths G y) (gset_paths G z) y (refl y) (map_path (BG G .carrier) (GSet G) (gset_paths G) y z q))
      (inverse (BG G .carrier) y z q)
  ≔ let B ≔ BG G .carrier in
    concat (Id B z y)
      (gset_path_eval G (gset_paths G y) (gset_paths G z) y (refl y) (map_path B (GSet G) (gset_paths G) y z q))
      (concat B z y y (inverse B y z q) (refl y)) (inverse B y z q)
      (gset_paths_transport G y z y q (refl y))
      (concat_p1 B z y (inverse B y z q))

{` lem:pathsptransportiseq. ap of P_- : (y = z) → (P_y = P_z) is an
   equivalence, with inverse e ↦ (e_y(refl_y))⁻¹ (the book's footnote,
   via lem:weq-iso); the second round trip uses that ev_{refl_y} is
   injective on P_y = P_z since P_y is transitive. `}
def gset_paths_ap_inverse (G : Group) (y z : BG G .carrier) (e : Id (GSet G) (gset_paths G y) (gset_paths G z))
  : Id (BG G .carrier) y z
  ≔ inverse (BG G .carrier) z y (gset_path_eval G (gset_paths G y) (gset_paths G z) y (refl y) e)

def gset_paths_ap_retraction (G : Group) (y z : BG G .carrier) (q : Id (BG G .carrier) y z)
  : Id (Id (BG G .carrier) y z)
      (gset_paths_ap_inverse G y z (map_path (BG G .carrier) (GSet G) (gset_paths G) y z q)) q
  ≔ let B ≔ BG G .carrier in
    concat (Id B y z) (gset_paths_ap_inverse G y z (map_path B (GSet G) (gset_paths G) y z q))
      (inverse B z y (inverse B y z q)) q
      (map_path (Id B z y) (Id B y z) (inverse B z y)
        (gset_path_eval G (gset_paths G y) (gset_paths G z) y (refl y) (map_path B (GSet G) (gset_paths G) y z q))
        (inverse B y z q) (gset_paths_ap_eval G y z q))
      (inverse_inverse B y z q)

def gset_paths_ap_section (G : Group) (y z : BG G .carrier) (e : Id (GSet G) (gset_paths G y) (gset_paths G z))
  : Id (Id (GSet G) (gset_paths G y) (gset_paths G z))
      (map_path (BG G .carrier) (GSet G) (gset_paths G) y z (gset_paths_ap_inverse G y z e)) e
  ≔ let B ≔ BG G .carrier in
    let ev ≔ gset_path_eval G (gset_paths G y) (gset_paths G z) y (refl y) in
    let q ≔ gset_paths_ap_inverse G y z e in
    embedding_reflects_paths (Id (GSet G) (gset_paths G y) (gset_paths G z)) (Id B z y) ev
      (gset_path_eval_injective G (gset_paths G y) (gset_paths G z) y (refl y) (gset_paths_transitive G y))
      (map_path B (GSet G) (gset_paths G) y z q) e
      (concat (Id B z y) (ev (map_path B (GSet G) (gset_paths G) y z q)) (inverse B y z q) (ev e)
        (gset_paths_ap_eval G y z q)
        (inverse_inverse B z y (ev e)))

def gset_paths_ap_equiv (G : Group) (y z : BG G .carrier)
  : BookEquiv (Id (BG G .carrier) y z) (Id (GSet G) (gset_paths G y) (gset_paths G z))
  ≔ book_quasi_inverse_equiv (Id (BG G .carrier) y z) (Id (GSet G) (gset_paths G y) (gset_paths G z))
      (map_path (BG G .carrier) (GSet G) (gset_paths G) y z) (gset_paths_ap_inverse G y z)
      (gset_paths_ap_retraction G y z) (gset_paths_ap_section G y z)

def gset_paths_ap_is_equiv (G : Group) (y z : BG G .carrier)
  : BookIsEquiv (Id (BG G .carrier) y z) (Id (GSet G) (gset_paths G y) (gset_paths G z))
      (map_path (BG G .carrier) (GSet G) (gset_paths G) y z)
  ≔ gset_paths_ap_equiv G y z .equiv

{` rem (after def:Gtorsor): Torsor_G is connected. `}
def torsors_path_equiv (G : Group) (S T : Torsors G) : Equiv (Id (Torsors G) S T) (Id (GSet G) (S .fst) (T .fst))
  ≔ subtype_path_equiv (GSet G) (X ↦ Mere (Id (GSet G) (principal_gset G) X))
      (X ↦ mere_isprop (Id (GSet G) (principal_gset G) X)) S T

def torsors_connected (G : Group) : Connected (Torsors G)
  ≔ let Tor ≔ Torsors G in
    let P ≔ principal_gset G in
    let reach : (S : Tor) → Mere (Id Tor (principal_torsor G) S)
      ≔ S ↦ mere_rec (Id (GSet G) P (S .fst)) (Mere (Id Tor (principal_torsor G) S)) (mere_isprop (Id Tor (principal_torsor G) S))
          (p ↦ mere (Id Tor (principal_torsor G) S)
            (equiv_inverse_map (Id Tor (principal_torsor G) S) (Id (GSet G) P (S .fst))
              (torsors_path_equiv G (principal_torsor G) S) p))
          (S .snd) in
    (mere Tor (principal_torsor G),
     S T ↦ merely_paths_compose native_truncation Tor (principal_torsor G) S T (reach S) (reach T))

def torsors_groupoid (G : Group) : isGroupoid (Torsors G)
  ≔ hlevel_to_groupoid (Torsors G)
      (subtype_hlevel (suc. (suc. zero.)) (GSet G) (X ↦ Mere (Id (GSet G) (principal_gset G) X))
        (groupoid_to_hlevel (GSet G) (gset_groupoid G))
        (X ↦ mere_isprop (Id (GSet G) (principal_gset G) X)))

{` ap of BG → Torsor_G is an equivalence on loops at sh_G (through the
   subtype projection Torsor_G → GSet, whose ap is an equivalence). `}
def bg_to_torsors_ap_is_equiv (G : Group) (y z : BG G .carrier)
  : BookIsEquiv (Id (BG G .carrier) y z) (Id (Torsors G) (bg_to_torsors G y) (bg_to_torsors G z))
      (map_path (BG G .carrier) (Torsors G) (bg_to_torsors G) y z)
  ≔ let B ≔ BG G .carrier in
    let Tor ≔ Torsors G in
    let u ≔ bg_to_torsors G y in
    let v ≔ bg_to_torsors G z in
    let e ≔ torsors_path_equiv G u v in
    book_quasi_inverse_equiv (Id B y z) (Id Tor u v) (map_path B Tor (bg_to_torsors G) y z)
      (r ↦ gset_paths_ap_inverse G y z (r .fst))
      (gset_paths_ap_retraction G y z)
      (r ↦ equivalence_injective (Id Tor u v) (Id (GSet G) (gset_paths G y) (gset_paths G z)) e
        (map_path B Tor (bg_to_torsors G) y z (gset_paths_ap_inverse G y z (r .fst))) r
        (gset_paths_ap_section G y z (r .fst)))
    .equiv

{` lem:BGbytorsor. P_- : BG → Torsor_G is an equivalence (cor:fib-vs-path,
   conn-fib-vs-path-point, as in the book's proof). `}
def bg_torsors_equiv (G : Group) : BookEquiv (BG G .carrier) (Torsors G)
  ≔ connected_map_equiv_from_loops native_truncation (BG G .carrier) (Torsors G) (bg_to_torsors G)
      (bg_connected G) (torsors_connected G) (shape G) (bg_to_torsors_ap_is_equiv G (shape G) (shape G))

def bg_to_torsors_is_equiv (G : Group) : BookIsEquiv (BG G .carrier) (Torsors G) (bg_to_torsors G)
  ≔ bg_torsors_equiv G .equiv
