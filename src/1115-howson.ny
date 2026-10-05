export "1111-nielsen-schreier"
export "1155-fgauto-reachability"

{` thm:howson-neumann (fggroups.tex:855): if H1, H2 are subgroups of F = F_S with
   finite indices h1, h2, then H1 ∩ H2 has finite index at most h1·h2.

   S is a finite set with decidable equality (the chapter's standing assumption,
   lines 116-118; it is needed: the index must be a natural number, i.e. the orbit
   below must be a decidable subset).  H1 ∩ H2 is the subgroup of the orbit of
   (x1, x2) in the product F_S-set X1 × X2 (subgroup_intersection; its classifying
   type is the component of (sh, x1, x2) in Σ_z X1(z) × X2(z) = BH1 ×_{BF} BH2, i.e.
   the book's def:intersectionofgroups).  Its index is the size of that orbit, a
   subset of X1(base) × X2(base) of size h1·h2.

   Decidability of the orbit (orbit_decidable): for a finite F_S-set Y, y lies in the
   orbit of y0 iff y is reachable from y0 in the finite Schreier graph with edges
   v -s-> s·v and s·v -S-> v (forward: transport the runs into paths of Σ_z Y(z);
   backward: an encode family on the graph quotient Σ_z Y(z) of the flattening,
   module 1111), and reachability is decided by the breadth-first search of module
   1155 (fgauto_reached). `}

{` ---------- The Schreier graph of a finite F_S-set ---------- `}

def SchreierGood (S V : Type) (tr : S → V → V) (p : V) (x : SignedLetter S) (q : V) : Type
  ≔ match x [ inl. s ↦ Id V q (tr s p) | inr. s ↦ Id V p (tr s q) ]

def SchreierAllGood (S V : Type) (tr : S → V → V) (E : List (FgautoEdge S V)) : Type
  ≔ match E [ nil. ↦ Unit | cons. e E' ↦ Product (SchreierGood S V tr (e .src) (e .lab) (e .tgt)) (SchreierAllGood S V tr E') ]

def schreier_all_good_append (S V : Type) (tr : S → V → V) (E E' : List (FgautoEdge S V))
  (h : SchreierAllGood S V tr E) (h' : SchreierAllGood S V tr E') : SchreierAllGood S V tr (append (FgautoEdge S V) E E')
  ≔ match E [ nil. ↦ h' | cons. e E0 ↦ (h .fst, schreier_all_good_append S V tr E0 E' (h .snd) h') ]

def schreier_edges_at (S V : Type) (tr : S → V → V) (v : V) (ls : List S) : List (FgautoEdge S V)
  ≔ match ls [
  | nil. ↦ nil.
  | cons. s ls' ↦ cons. (v, inl. s, tr s v) (cons. (tr s v, inr. s, v) (schreier_edges_at S V tr v ls')) ]

def schreier_edges (S V : Type) (tr : S → V → V) (vs : List V) (ls : List S) : List (FgautoEdge S V)
  ≔ match vs [ nil. ↦ nil. | cons. v vs' ↦ append (FgautoEdge S V) (schreier_edges_at S V tr v ls) (schreier_edges S V tr vs' ls) ]

def schreier_edges_at_good (S V : Type) (tr : S → V → V) (v : V) (ls : List S)
  : SchreierAllGood S V tr (schreier_edges_at S V tr v ls)
  ≔ match ls [
  | nil. ↦ star.
  | cons. s ls' ↦ (refl (tr s v), (refl (tr s v), schreier_edges_at_good S V tr v ls')) ]

def schreier_edges_good (S V : Type) (tr : S → V → V) (vs : List V) (ls : List S)
  : SchreierAllGood S V tr (schreier_edges S V tr vs ls)
  ≔ match vs [
  | nil. ↦ star.
  | cons. v vs' ↦ schreier_all_good_append S V tr (schreier_edges_at S V tr v ls) (schreier_edges S V tr vs' ls)
      (schreier_edges_at_good S V tr v ls) (schreier_edges_good S V tr vs' ls) ]

def schreier_good_transport (S V : Type) (tr : S → V → V) (p p' : V) (x x' : SignedLetter S) (q q' : V)
  (ep : Id V p p') (ex : Id (SignedLetter S) x x') (eq : Id V q q') (g : SchreierGood S V tr p' x' q')
  : SchreierGood S V tr p x q
  ≔ transport V (a ↦ SchreierGood S V tr a x q) p' p (inverse V p p' ep)
      (transport (SignedLetter S) (y ↦ SchreierGood S V tr p' y q) x' x (inverse (SignedLetter S) x x' ex)
        (transport V (b ↦ SchreierGood S V tr p' x' b) q' q (inverse V q q' eq) g))

def schreier_step_good (S V : Type) (tr : S → V → V) (E : List (FgautoEdge S V)) (h : SchreierAllGood S V tr E)
  (p : V) (x : SignedLetter S) (q : V) (st : FgautoStep S V E p x q) : SchreierGood S V tr p x q
  ≔ match E [
  | nil. ↦ match st []
  | cons. e E' ↦ match st [
    | inl. t ↦ schreier_good_transport S V tr p (e .src) x (e .lab) q (e .tgt) (t .fst) (t .snd .fst) (t .snd .snd) (h .fst)
    | inr. st' ↦ schreier_step_good S V tr E' (h .snd) p x q st' ] ]

{` The edges at v for s ∈ ls are present. `}
def schreier_step_fwd_at (S V : Type) (tr : S → V → V) (v : V) (ls : List S) (s : S) (m : FgautoMem S s ls)
  : FgautoStep S V (schreier_edges_at S V tr v ls) v (inl. s) (tr s v)
  ≔ match ls [
  | nil. ↦ match m []
  | cons. s0 ls' ↦ match m [
    | inl. e ↦ inl. (refl v, (refl ((z : S) ↦ (inl. z : SignedLetter S)) e, refl ((z : S) ↦ tr z v) e))
    | inr. m' ↦ inr. (inr. (schreier_step_fwd_at S V tr v ls' s m')) ] ]

def schreier_step_back_at (S V : Type) (tr : S → V → V) (v : V) (ls : List S) (s : S) (m : FgautoMem S s ls)
  : FgautoStep S V (schreier_edges_at S V tr v ls) (tr s v) (inr. s) v
  ≔ match ls [
  | nil. ↦ match m []
  | cons. s0 ls' ↦ match m [
    | inl. e ↦ inr. (inl. (refl ((z : S) ↦ tr z v) e, (refl ((z : S) ↦ (inr. z : SignedLetter S)) e, refl v)))
    | inr. m' ↦ inr. (inr. (schreier_step_back_at S V tr v ls' s m')) ] ]

def schreier_step_fwd (S V : Type) (tr : S → V → V) (vs : List V) (ls : List S) (v : V) (mv : FgautoMem V v vs)
  (s : S) (ms : FgautoMem S s ls) : FgautoStep S V (schreier_edges S V tr vs ls) v (inl. s) (tr s v)
  ≔ match vs [
  | nil. ↦ match mv []
  | cons. v0 vs' ↦ match mv [
    | inl. e ↦ fgauto_step_append_left S V (schreier_edges_at S V tr v0 ls) (schreier_edges S V tr vs' ls) v (inl. s) (tr s v)
        (transport V (a ↦ FgautoStep S V (schreier_edges_at S V tr a ls) v (inl. s) (tr s v)) v v0 e
          (schreier_step_fwd_at S V tr v ls s ms))
    | inr. m' ↦ fgauto_step_append_right S V (schreier_edges_at S V tr v0 ls) (schreier_edges S V tr vs' ls) v (inl. s) (tr s v)
        (schreier_step_fwd S V tr vs' ls v m' s ms) ] ]

def schreier_step_back (S V : Type) (tr : S → V → V) (vs : List V) (ls : List S) (v : V) (mv : FgautoMem V v vs)
  (s : S) (ms : FgautoMem S s ls) : FgautoStep S V (schreier_edges S V tr vs ls) (tr s v) (inr. s) v
  ≔ match vs [
  | nil. ↦ match mv []
  | cons. v0 vs' ↦ match mv [
    | inl. e ↦ fgauto_step_append_left S V (schreier_edges_at S V tr v0 ls) (schreier_edges S V tr vs' ls) (tr s v) (inr. s) v
        (transport V (a ↦ FgautoStep S V (schreier_edges_at S V tr a ls) (tr s v) (inr. s) v) v v0 e
          (schreier_step_back_at S V tr v ls s ms))
    | inr. m' ↦ fgauto_step_append_right S V (schreier_edges_at S V tr v0 ls) (schreier_edges S V tr vs' ls) (tr s v) (inr. s) v
        (schreier_step_back S V tr vs' ls v m' s ms) ] ]

{` ---------- Runs and paths in Σ_z Y(z) ---------- `}

def schreier_tr (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type) (s : S) (v : Y (F .base)) : Y (F .base)
  ≔ transport (F .carrier) Y (F .base) (F .base) (F .loop s) v

def schreier_pair (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type) (v : Y (F .base)) : Σ (F .carrier) Y
  ≔ (F .base, v)

def schreier_edge_path (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type) (v : Y (F .base)) (s : S)
  : Id (Σ (F .carrier) Y) (F .base, v) (F .base, schreier_tr S F Y s v)
  ≔ (F .loop s, pathover_of_eq (F .carrier) Y (F .base) (F .base) (F .loop s) v (schreier_tr S F Y s v)
       (refl (schreier_tr S F Y s v)))

def schreier_good_path (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type) (p : Y (F .base))
  (x : SignedLetter S) (q : Y (F .base)) (g : SchreierGood S (Y (F .base)) (schreier_tr S F Y) p x q)
  : Id (Σ (F .carrier) Y) (F .base, p) (F .base, q)
  ≔ let T ≔ Σ (F .carrier) Y in
    let pr ≔ schreier_pair S F Y in
    match x [
    | inl. s ↦ concat T (F .base, p) (F .base, schreier_tr S F Y s p) (F .base, q) (schreier_edge_path S F Y p s)
        (refl pr (inverse (Y (F .base)) q (schreier_tr S F Y s p) g))
    | inr. s ↦ concat T (F .base, p) (F .base, schreier_tr S F Y s q) (F .base, q) (refl pr g)
        (inverse T (F .base, q) (F .base, schreier_tr S F Y s q) (schreier_edge_path S F Y q s)) ]

def schreier_run_path (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type)
  (E : List (FgautoEdge S (Y (F .base)))) (h : SchreierAllGood S (Y (F .base)) (schreier_tr S F Y) E)
  (p : Y (F .base)) (w : SignedWord S) (q : Y (F .base)) (r : FgautoRun S (Y (F .base)) E p w q)
  : Id (Σ (F .carrier) Y) (F .base, p) (F .base, q)
  ≔ match w [
  | nil. ↦ refl (schreier_pair S F Y) r
  | cons. x w' ↦ concat (Σ (F .carrier) Y) (F .base, p) (F .base, r .fst) (F .base, q)
      (schreier_good_path S F Y p x (r .fst) (schreier_step_good S (Y (F .base)) (schreier_tr S F Y) E h p x (r .fst) (r .snd .fst)))
      (schreier_run_path S F Y E h (r .fst) w' q (r .snd .snd)) ]

{` ---------- Encoding paths as runs ---------- `}

def SchreierReach (S V : Type) (E : List (FgautoEdge S V)) (y0 v : V) : Type
  ≔ Mere (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w v))

def schreier_reach_prop (S V : Type) (E : List (FgautoEdge S V)) (y0 v : V) : PropTypes
  ≔ (SchreierReach S V E y0 v, mere_isprop (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w v)))

def schreier_reach_extend (S V : Type) (E : List (FgautoEdge S V)) (y0 v : V) (x : SignedLetter S) (v' : V)
  (st : FgautoStep S V E v x v') (h : SchreierReach S V E y0 v) : SchreierReach S V E y0 v'
  ≔ mere_rec (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w v)) (SchreierReach S V E y0 v')
      (mere_isprop (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w v')))
      (u ↦ mere (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w v'))
        (append (SignedLetter S) (u .fst) (cons. x nil.),
         fgauto_run_append S V E y0 (u .fst) v (cons. x nil.) v' (u .snd) (v', (st, refl v'))))
      h

def schreier_encode_edge (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type)
  (vs : List (Y (F .base))) (hvs : (v : Y (F .base)) → FgautoMem (Y (F .base)) v vs)
  (ls : List S) (hls : (s : S) → FgautoMem S s ls) (y0 : Y (F .base))
  (v v' : Y (F .base)) (e : FreeFlatEdges S F Y v v')
  : Id PropTypes (schreier_reach_prop S (Y (F .base)) (schreier_edges S (Y (F .base)) (schreier_tr S F Y) vs ls) y0 v)
      (schreier_reach_prop S (Y (F .base)) (schreier_edges S (Y (F .base)) (schreier_tr S F Y) vs ls) y0 v')
  ≔ let V ≔ Y (F .base) in
    let tr ≔ schreier_tr S F Y in
    let E ≔ schreier_edges S V tr vs ls in
    let s ≔ e .fst in
    let q : Id V (tr s v) v' ≔ pathover_transport_equiv (F .carrier) Y (F .base) (F .base) (F .loop s) v v' .map (e .snd) in
    proposition_extensionality (schreier_reach_prop S V E y0 v) (schreier_reach_prop S V E y0 v')
      (schreier_reach_extend S V E y0 v (inl. s) v'
        (transport V (b ↦ FgautoStep S V E v (inl. s) b) (tr s v) v' q (schreier_step_fwd S V tr vs ls v (hvs v) s (hls s))))
      (schreier_reach_extend S V E y0 v' (inr. s) v
        (transport V (a ↦ FgautoStep S V E a (inr. s) v) (tr s v) v' q (schreier_step_back S V tr vs ls v (hvs v) s (hls s))))

def schreier_orbit_reach (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type)
  (vs : List (Y (F .base))) (hvs : (v : Y (F .base)) → FgautoMem (Y (F .base)) v vs)
  (ls : List S) (hls : (s : S) → FgautoMem S s ls) (y0 y : Y (F .base))
  (o : Mere (Id (Σ (F .carrier) Y) (F .base, y0) (F .base, y)))
  : SchreierReach S (Y (F .base)) (schreier_edges S (Y (F .base)) (schreier_tr S F Y) vs ls) y0 y
  ≔ let V ≔ Y (F .base) in
    let E ≔ schreier_edges S V (schreier_tr S F Y) vs ls in
    let R ≔ free_flattening_signature S F Y in
    let d : GraphCocone V (FreeFlatEdges S F Y) PropTypes
      ≔ (v ↦ schreier_reach_prop S V E y0 v, v v' e ↦ schreier_encode_edge S F Y vs hvs ls hls y0 v v' e) in
    let P ≔ gq_rec V (FreeFlatEdges S F Y) R PropTypes d in
    let start : P (F .base, y0) .fst
      ≔ transport PropTypes (X ↦ X .fst) (schreier_reach_prop S V E y0 y0) (P (F .base, y0))
          (inverse PropTypes (P (F .base, y0)) (schreier_reach_prop S V E y0 y0) (gq_rec_vertex V (FreeFlatEdges S F Y) R PropTypes d y0))
          (mere (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w y0)) (nil., refl y0)) in
    transport PropTypes (X ↦ X .fst) (P (F .base, y)) (schreier_reach_prop S V E y0 y)
      (gq_rec_vertex V (FreeFlatEdges S F Y) R PropTypes d y)
      (mere_rec (Id (Σ (F .carrier) Y) (F .base, y0) (F .base, y)) (P (F .base, y) .fst) (P (F .base, y) .snd)
        (p ↦ transport (Σ (F .carrier) Y) (u ↦ P u .fst) (F .base, y0) (F .base, y) p start) o)

{` The orbit of y0 in a finite F_S-set is decidable. `}
def schreier_orbit_decidable (S : Type) (F : FreeGroupSignature S) (Y : F .carrier → Type)
  (dV : DecidableEquality (Y (F .base)))
  (vs : List (Y (F .base))) (hvs : (v : Y (F .base)) → FgautoMem (Y (F .base)) v vs)
  (ls : List S) (hls : (s : S) → FgautoMem S s ls) (y0 y : Y (F .base))
  : Decidable (Mere (Id (Σ (F .carrier) Y) (F .base, y0) (F .base, y)))
  ≔ let V ≔ Y (F .base) in
    let tr ≔ schreier_tr S F Y in
    let E ≔ schreier_edges S V tr vs ls in
    let T ≔ Σ (F .carrier) Y in
    match fgauto_mem_decide V dV y (fgauto_reached S V dV E y0) [
    | inl. m ↦ inl. (mere (Id T (F .base, y0) (F .base, y))
        (schreier_run_path S F Y E (schreier_edges_good S V tr vs ls) y0 (fgauto_tree_word S V dV E y0 y) y
          (fgauto_tree_word_run S V dV E y0 y m)))
    | inr. n ↦ inr. (o ↦ mere_rec (Σ (SignedWord S) (w ↦ FgautoRun S V E y0 w y)) Empty empty_prop
        (u ↦ n (fgauto_reach_complete S V dV E y0 (u .fst) y (u .snd)))
        (schreier_orbit_reach S F Y vs hvs ls hls y0 y o)) ]
