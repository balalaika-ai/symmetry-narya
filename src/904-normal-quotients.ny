export "903-normal-subgroups"
export "930-epi-surj-easy"

{` Chapter 9 (subgroups.tex), sec:normal, part 2: lem:evaliseqwhennormal and
   def:normalquotient (the quotient group G/N and the quotient homomorphism
   q_N, an epimorphism).

   Notation: for N : Nor(G) we write N(y) ≡ (X_y, pt_y, !) with
   X_y = normal_family G N y : GSet G and pt_y = normal_family_point G N y. `}

def normal_family (G : Group) (N : NormalSubgroups G) (y : BG G .carrier) : GSet G ≔ N y .gset

def normal_family_point (G : Group) (N : NormalSubgroups G) (y : BG G .carrier) : normal_family G N y y .fst
  ≔ N y .point

{` The map X : (y = z) → (X_y = X_z) of lem:evaliseqwhennormal (2): the
   action of y ↦ X_y on paths (X_refl ≡ refl). `}
def normal_family_map (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier) (p : Id (BG G .carrier) y z)
  : Id (GSet G) (normal_family G N y) (normal_family G N z)
  ≔ map_path (BG G .carrier) (GSet G) (normal_family G N) y z p

{` ev_yz : (X_y = X_z) → X_z(y), ev_yz(f) ≔ f_y(pt_y). `}
def normal_evaluation (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  (e : Id (GSet G) (normal_family G N y) (normal_family G N z)) : normal_family G N z y .fst
  ≔ gset_path_eval G (normal_family G N y) (normal_family G N z) y (normal_family_point G N y) e

{` The composite ev_yz ∘ X sends p : y = z to p⁻¹ ·_{X_z} pt_z (by path
   induction on p; this is where N being a section over all of BG is used). `}
def nsub_eval_family_map (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier) (p : Id (BG G .carrier) y z)
  : Id (normal_family G N z y .fst) (normal_evaluation G N y z (normal_family_map G N y z p))
      (gset_act G (normal_family G N z) z y (inverse (BG G .carrier) y z p) (normal_family_point G N z))
  ≔ let B ≔ BG G .carrier in
    let X ≔ normal_family G N in
    let pt ≔ normal_family_point G N in
    J B y
      (z p ↦ Id (X z y .fst) (normal_evaluation G N y z (normal_family_map G N y z p))
        (gset_act G (X z) z y (inverse B y z p) (pt z)))
      (concat (X y y .fst) (normal_evaluation G N y y (refl (X y))) (pt y)
        (gset_act G (X y) y y (inverse B y y (refl y)) (pt y))
        (transport_refl (GSet G) (W ↦ W y .fst) (X y) (pt y))
        (inverse (X y y .fst) (gset_act G (X y) y y (inverse B y y (refl y)) (pt y)) (pt y)
          (concat (X y y .fst) (gset_act G (X y) y y (inverse B y y (refl y)) (pt y))
            (gset_act G (X y) y y (refl y) (pt y)) (pt y)
            (refl ((q ↦ gset_act G (X y) y y q (pt y)) : Id B y y → X y y .fst) (inverse_refl B y))
            (gset_act_refl G (X y) y (pt y)))))
      z p

{` ev_yz ∘ X is surjective: X_z is transitive, so every x : X_z(y) is
   q ·_{X_z} pt_z for some q : z = y. `}
def nsub_eval_family_surjective (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : Surjective (Id (BG G .carrier) y z) (normal_family G N z y .fst)
      (p ↦ normal_evaluation G N y z (normal_family_map G N y z p))
  ≔ let B ≔ BG G .carrier in
    let X ≔ normal_family G N in
    let pt ≔ normal_family_point G N in
    let Ev ≔ (p ↦ normal_evaluation G N y z (normal_family_map G N y z p)) : Id B y z → X z y .fst in
    let T ≔ ActionType G (X z) in
    let conn : Connected T ≔ transitive_action_type_connected (group_at G z) (X z) (N z .transitive) in
    x ↦ mere_rec (Id T (z, pt z) (y, x)) (Mere (BookFiber (Id B y z) (X z y .fst) Ev x))
      (mere_isprop (BookFiber (Id B y z) (X z y .fst) Ev x))
      (r ↦ let qe ≔ action_type_path_equiv G (X z) (z, pt z) (y, x) .map r in
        let q : Id B z y ≔ qe .fst in
        mere (BookFiber (Id B y z) (X z y .fst) Ev x)
          (inverse B z y q,
           calc
             x
             = gset_act G (X z) z y q (pt z)
               by inverse (X z y .fst) (gset_act G (X z) z y q (pt z)) x (qe .snd)
             = gset_act G (X z) z y (inverse B y z (inverse B z y q)) (pt z)
               by refl ((s ↦ gset_act G (X z) z y s (pt z)) : Id B z y → X z y .fst)
                    (inverse (Id B z y) (inverse B y z (inverse B z y q)) q (inverse_inverse B z y q))
             = Ev (inverse B z y q)
               by inverse (X z y .fst) (Ev (inverse B z y q))
                    (gset_act G (X z) z y (inverse B y z (inverse B z y q)) (pt z))
                    (nsub_eval_family_map G N y z (inverse B z y q)) ∎))
      (conn .snd (z, pt z) (y, x))

def nsub_evaluation_surjective (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : Surjective (Id (GSet G) (normal_family G N y) (normal_family G N z)) (normal_family G N z y .fst)
      (normal_evaluation G N y z)
  ≔ let B ≔ BG G .carrier in
    let P ≔ Id (GSet G) (normal_family G N y) (normal_family G N z) in
    let Y ≔ normal_family G N z y .fst in
    x ↦ mere_rec (BookFiber (Id B y z) Y (p ↦ normal_evaluation G N y z (normal_family_map G N y z p)) x)
      (Mere (BookFiber P Y (normal_evaluation G N y z) x)) (mere_isprop (BookFiber P Y (normal_evaluation G N y z) x))
      (pe ↦ mere (BookFiber P Y (normal_evaluation G N y z) x) (normal_family_map G N y z (pe .fst), pe .snd))
      (nsub_eval_family_surjective G N y z x)

def nsub_evaluation_injective (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : IsEmbedding (Id (GSet G) (normal_family G N y) (normal_family G N z)) (normal_family G N z y .fst)
      (normal_evaluation G N y z)
  ≔ gset_path_eval_injective (group_at G y) (normal_family G N y) (normal_family G N z) y (normal_family_point G N y)
      (N y .transitive)

{` lem:evaliseqwhennormal (1): ev_yz : (X_y = X_z) → X_z(y) is an
   equivalence, for all y, z : BG. `}
def normal_evaluation_equiv (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : BookEquiv (Id (GSet G) (normal_family G N y) (normal_family G N z)) (normal_family G N z y .fst)
  ≔ embedding_surjection_equiv native_truncation
      (Id (GSet G) (normal_family G N y) (normal_family G N z)) (normal_family G N z y .fst)
      (normal_evaluation G N y z) (nsub_evaluation_injective G N y z) (nsub_evaluation_surjective G N y z)

def normal_evaluation_is_equiv (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : BookIsEquiv (Id (GSet G) (normal_family G N y) (normal_family G N z)) (normal_family G N z y .fst)
      (normal_evaluation G N y z)
  ≔ normal_evaluation_equiv G N y z .equiv

{` lem:evaliseqwhennormal (2): X : (y = z) → (X_y = X_z) is surjective. `}
def normal_family_map_surjective (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : Surjective (Id (BG G .carrier) y z) (Id (GSet G) (normal_family G N y) (normal_family G N z))
      (normal_family_map G N y z)
  ≔ let B ≔ BG G .carrier in
    let P ≔ Id (GSet G) (normal_family G N y) (normal_family G N z) in
    let Y ≔ normal_family G N z y .fst in
    let ev ≔ normal_evaluation G N y z in
    e ↦ mere_rec (BookFiber (Id B y z) Y (p ↦ ev (normal_family_map G N y z p)) (ev e))
      (Mere (BookFiber (Id B y z) P (normal_family_map G N y z) e))
      (mere_isprop (BookFiber (Id B y z) P (normal_family_map G N y z) e))
      (pe ↦ mere (BookFiber (Id B y z) P (normal_family_map G N y z) e)
        (pe .fst,
         refl ((u ↦ u .fst) : BookFiber P Y ev (ev e) → P)
           (nsub_evaluation_injective G N y z (ev e) (e, refl (ev e)) (normal_family_map G N y z (pe .fst), pe .snd))))
      (nsub_eval_family_surjective G N y z (ev e))

{` def:normalquotient. G/N ≔ Aut_{G-Set}(X_{sh_G}), the component of the
   groupoid of G-sets at X_{sh_G}. `}
def normal_quotient_group (G : Group) (N : NormalSubgroups G) : Group
  ≔ automorphism_group (GSet G) (gset_groupoid G) (normal_family G N (shape G))

{` Bq_N(z) ≔ X_z (in the component, since BG is connected). `}
def normal_quotient_map (G : Group) (N : NormalSubgroups G)
  : BG G .carrier → BG (normal_quotient_group G N) .carrier
  ≔ z ↦ (normal_family G N z,
         mere_rec (Id (BG G .carrier) (shape G) z)
           (Mere (Id (GSet G) (normal_family G N (shape G)) (normal_family G N z)))
           (mere_isprop (Id (GSet G) (normal_family G N (shape G)) (normal_family G N z)))
           (p ↦ mere (Id (GSet G) (normal_family G N (shape G)) (normal_family G N z))
             (normal_family_map G N (shape G) z p))
           (bg_connected G .snd (shape G) z))

{` The book's q_N is strictly pointed; here the pointing path is the
   identification of points of the component whose first component is
   refl (the second components are proofs of a proposition). `}
def normal_quotient_point (G : Group) (N : NormalSubgroups G)
  : Id (BG (normal_quotient_group G N) .carrier) (shape (normal_quotient_group G N))
      (normal_quotient_map G N (shape G))
  ≔ component_path (GSet G) (normal_family G N (shape G)) (shape (normal_quotient_group G N))
      (normal_quotient_map G N (shape G)) (refl (normal_family G N (shape G)))

def normal_quotient_hom (G : Group) (N : NormalSubgroups G) : GroupHom G (normal_quotient_group G N)
  ≔ mkhom G (normal_quotient_group G N) (normal_quotient_map G N, normal_quotient_point G N)

{` USym(q_N) is surjective (by lem:evaliseqwhennormal (2) at y ≡ z ≡ sh_G). `}
def normal_quotient_usym_surjective (G : Group) (N : NormalSubgroups G)
  : Surjective (USym G) (USym (normal_quotient_group G N)) (usym_hom G (normal_quotient_group G N) (normal_quotient_hom G N))
  ≔ let Q ≔ normal_quotient_group G N in
    let B ≔ BG G .carrier in
    let C ≔ BG Q .carrier in
    let X ≔ normal_family G N in
    let Xs ≔ X (shape G) in
    let Bq ≔ normal_quotient_map G N in
    let s ≔ shape G in
    let c0 ≔ shape Q in
    let pt ≔ normal_quotient_point G N in
    let u ≔ Bq s in
    let qh ≔ normal_quotient_hom G N in
    h ↦
      let l : Id C u u ≔ concat C u c0 u (inverse C c0 u pt) (concat C c0 c0 u h pt) in
      mere_rec (BookFiber (Id B s s) (Id (GSet G) Xs Xs) (normal_family_map G N s s) (l .fst))
        (Mere (BookFiber (USym G) (USym Q) (usym_hom G Q qh) h))
        (mere_isprop (BookFiber (USym G) (USym Q) (usym_hom G Q qh) h))
        (ge ↦
          let g : USym G ≔ ge .fst in
          let lg : Id (Id C u u) l (refl Bq g)
            ≔ equivalence_injective (Id C u u) (Id (GSet G) Xs Xs) (component_path_equiv (GSet G) Xs u u)
                l (refl Bq g) (ge .snd) in
          mere (BookFiber (USym G) (USym Q) (usym_hom G Q qh) h)
            (g,
             calc
               h
               = pointed_loop_conjugate C c0 u pt l
                 by inverse (Id C c0 c0) (pointed_loop_conjugate C c0 u pt l) h (gepi_conjugate_cancel C c0 u pt h)
               = pointed_loop_conjugate C c0 u pt (refl Bq g)
                 by refl (pointed_loop_conjugate C c0 u pt) lg
               = usym_hom G Q qh g by refl (usym_hom G Q qh g) ∎))
        (normal_family_map_surjective G N s s (l .fst))

{` "q_N is an epimorphism" (via lem:epi-surj (2') ⇒ (1')), and its
   classifying map has connected fibers ((2') ⇒ (3')). `}
def normal_quotient_epi (G : Group) (N : NormalSubgroups G)
  : IsGroupEpi G (normal_quotient_group G N) (normal_quotient_hom G N)
  ≔ gepi_usym_surjective_epi G (normal_quotient_group G N) (normal_quotient_hom G N)
      (normal_quotient_usym_surjective G N)

def normal_quotient_connected (G : Group) (N : NormalSubgroups G)
  : IsConnectedHom G (normal_quotient_group G N) (normal_quotient_hom G N)
  ≔ gepi_usym_surjective_connected_fibers G (normal_quotient_group G N) (normal_quotient_hom G N)
      (normal_quotient_usym_surjective G N)

{` q : Nor(G) → Epi(G), q(N) ≔ (G/N, q_N, !), and the same into the
   homomorphisms with connected fibers. `}
def normal_quotient_epis (G : Group) (N : NormalSubgroups G) : GroupEpis G
  ≔ (normal_quotient_group G N, (normal_quotient_hom G N, normal_quotient_epi G N))

def normal_quotient_connected_epis (G : Group) (N : NormalSubgroups G) : ConnectedEpis G
  ≔ (normal_quotient_group G N, (normal_quotient_hom G N, normal_quotient_connected G N))
