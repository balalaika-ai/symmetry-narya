export "750-abstract-concrete-gsets"
export "740-abstract-restriction-induction"
export "542-restriction-induction"
export "521-orbits-set-truncation"

{` Chapter 7 (absgroup.tex), sec:Gsetsabstrconcr, xca:f_!-abs(f)_!: for a
   homomorphism f : G → H the square
     ev_{sh_H} ∘ f_! = abstr(f)_! ∘ ev_{sh_G} : GSet(G) → absGSet(abstr H)
   commutes.

   For a G-set X, ev_{sh_H}(f_! X) has underlying set
   f_!X(sh_H) = ‖Σ_{z:BG} (Bf(z) = sh_H) × X(z)‖₀, the set truncation of the
   action type of the G-set Y = induced_sum_gset (ft:f_!X(w)-orbitset), and
   abstr(f)_!(ev_{sh_G} X) has underlying set (USym H × X(sh_G))/∼ with
   (t, x) ∼ (u, y) ≔ ∃_g (t · f(g) = u) × (x = g ·_X y) (def:phi_!, module 740;
   t · f(g) = concat f(g) t, the book's p USym f(g) = q; no flip is needed).
   Following the equivalences before def:phi_! (lem:X/G=setTruncX_hG,
   cor:orbit-equiv), the map (t, x) ↦ |(sh_G, (Bf_pt⁻¹ · t, x))|₀ (using Bf_pt,
   as in induced_sum_underlying_equiv) is surjective (BG is connected), respects
   ∼ and reflects it (set_trunc_paths and rem:path-in-action-type), so it
   induces an equivalence from the quotient (surjection_quotient_equiv); it
   commutes with the H-actions ((t, x) ↦ (h t, x) versus transport along h). `}

{` Path algebra: with f(g) = p · c · p⁻¹ (concatenation order),
   c⁻¹ · (p⁻¹ · (f(g) · t)) = p⁻¹ · t. `}
def induce_compare_conj_cancel (A : Type) (s b w : A) (p : Id A s b) (c : Id A b b) (t : Id A s w)
  : Id (Id A b w)
      (concat A b b w (inverse A b b c)
        (concat A b s w (inverse A s b p) (concat A s s w (concat A s b s p (concat A b b s c (inverse A s b p))) t)))
      (concat A b s w (inverse A s b p) t)
  ≔ let ip ≔ inverse A s b p in let ic ≔ inverse A b b c in
    let cp ≔ concat A b b s c ip in
    calc
      concat A b b w ic (concat A b s w ip (concat A s s w (concat A s b s p cp) t))
      = concat A b b w ic (concat A b s w ip (concat A s b w p (concat A b s w cp t)))
        by refl ((r ↦ concat A b b w ic (concat A b s w ip r)) : Id A s w → Id A b w) (concat_assoc A s b s w p cp t)
      = concat A b b w ic (concat A b s w cp t)
        by refl (concat A b b w ic) (concat_left_inverse_cancel A s b w p (concat A b s w cp t))
      = concat A b b w ic (concat A b b w c (concat A b s w ip t))
        by refl (concat A b b w ic) (concat_assoc A b b s w c ip t)
      = concat A b s w ip t by concat_left_inverse_cancel A b b w c (concat A b s w ip t) ∎

{` Conversely, c⁻¹ · (p⁻¹ · t) = p⁻¹ · t' implies (p · c · p⁻¹) · t' = t. `}
def induce_compare_conj_solve (A : Type) (s b w : A) (p : Id A s b) (c : Id A b b) (t t' : Id A s w)
  (d : Id (Id A b w) (concat A b b w (inverse A b b c) (concat A b s w (inverse A s b p) t)) (concat A b s w (inverse A s b p) t'))
  : Id (Id A s w) (concat A s s w (concat A s b s p (concat A b b s c (inverse A s b p))) t') t
  ≔ let ip ≔ inverse A s b p in let ic ≔ inverse A b b c in
    let cp ≔ concat A b b s c ip in
    let r ≔ concat A b s w ip t in
    let k ≔ concat A s s w (concat A s b s p cp) in
    calc
      k t' = k (concat A s b w p (concat A b s w ip t'))
        by refl k (inverse (Id A s w) (concat A s b w p (concat A b s w ip t')) t' (ch5_concat_inverse_cancel A s b w p t'))
      = k (concat A s b w p (concat A b b w ic r))
        by refl ((v ↦ k (concat A s b w p v)) : Id A b w → Id A s w)
          (inverse (Id A b w) (concat A b b w ic r) (concat A b s w ip t') d)
      = concat A s b w p (concat A b s w cp (concat A s b w p (concat A b b w ic r)))
        by concat_assoc A s b s w p cp (concat A s b w p (concat A b b w ic r))
      = concat A s b w p (concat A b b w c (concat A b s w ip (concat A s b w p (concat A b b w ic r))))
        by refl (concat A s b w p) (concat_assoc A b b s w c ip (concat A s b w p (concat A b b w ic r)))
      = concat A s b w p (concat A b b w c (concat A b b w ic r))
        by refl ((v ↦ concat A s b w p (concat A b b w c v)) : Id A b w → Id A s w)
          (concat_left_inverse_cancel A s b w p (concat A b b w ic r))
      = concat A s b w p r by refl (concat A s b w p) (ch5_concat_inverse_cancel A b b w c r)
      = t by ch5_concat_inverse_cancel A s b w p t ∎

{` The action of the G-set z ↦ (Bf(z) = w) × X(z): g · (q, x) = (ap_Bf(g)⁻¹ · q, g · x). `}
def induce_compare_sum_act (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier)
  (z z' : BG G .carrier) (g : Id (BG G .carrier) z z')
  (q : Id (BG H .carrier) (hom_function G H f z) w) (x : X z .fst)
  : Id (induced_sum_gset G H f X w z' .fst)
      (gset_act G (induced_sum_gset G H f X w) z z' g (q, x))
      (concat (BG H .carrier) (hom_function G H f z') (hom_function G H f z) w
         (inverse (BG H .carrier) (hom_function G H f z) (hom_function G H f z') (refl (hom_function G H f) g)) q,
       gset_act G X z z' g x)
  ≔ let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in let Y ≔ induced_sum_gset G H f X w in
    J (BG G .carrier) z
      (z' g ↦ Id (Y z' .fst) (gset_act G Y z z' g (q, x))
        (concat B (Bf z') (Bf z) w (inverse B (Bf z) (Bf z') (refl Bf g)) q, gset_act G X z z' g x))
      (concat (Y z .fst) (gset_act G Y z z (refl z) (q, x)) (q, x)
        (concat B (Bf z) (Bf z) w (inverse B (Bf z) (Bf z) (refl (Bf z))) q, gset_act G X z z (refl z) x)
        (gset_act_refl G Y z (q, x))
        (inverse (Y z .fst)
          (concat B (Bf z) (Bf z) w (inverse B (Bf z) (Bf z) (refl (Bf z))) q, gset_act G X z z (refl z) x) (q, x)
          (inverse_refl_concat B (Bf z) w q, gset_act_refl G X z x)))
      z' g

{` The action of f_!X: transport along h : w = w' sends |(z, (q, x))|₀ to |(z, (q · h, x))|₀. `}
def induce_compare_trunc_act (G H : Group) (f : GroupHom G H) (X : GSet G) (w w' : BG H .carrier)
  (h : Id (BG H .carrier) w w') (z : BG G .carrier) (q : Id (BG H .carrier) (hom_function G H f z) w) (x : X z .fst)
  : Id (gset_induce G H f X w' .fst)
      (gset_act H (gset_induce G H f X) w w' h (set_trunc (GSetInducedSum G H f X w) (z, (q, x))))
      (set_trunc (GSetInducedSum G H f X w') (z, (concat (BG H .carrier) (hom_function G H f z) w w' q h, x)))
  ≔ let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in
    J B w
      (w' h ↦ Id (gset_induce G H f X w' .fst)
        (gset_act H (gset_induce G H f X) w w' h (set_trunc (GSetInducedSum G H f X w) (z, (q, x))))
        (set_trunc (GSetInducedSum G H f X w') (z, (concat B (Bf z) w w' q h, x))))
      (concat (gset_induce G H f X w .fst)
        (gset_act H (gset_induce G H f X) w w (refl w) (set_trunc (GSetInducedSum G H f X w) (z, (q, x))))
        (set_trunc (GSetInducedSum G H f X w) (z, (q, x)))
        (set_trunc (GSetInducedSum G H f X w) (z, (concat B (Bf z) w w q (refl w), x)))
        (gset_act_refl H (gset_induce G H f X) w (set_trunc (GSetInducedSum G H f X w) (z, (q, x))))
        (refl ((r ↦ set_trunc (GSetInducedSum G H f X w) (z, (r, x))) : Id B (Bf z) w → gset_induce G H f X w .fst)
          (inverse (Id B (Bf z) w) (concat B (Bf z) w w q (refl w)) q (concat_p1 B (Bf z) w q))))
      w' h

{` The representative map (t, x) ↦ |(sh_G, (Bf_pt⁻¹ · t, x))|₀. `}
def induce_compare_rep (G H : Group) (f : GroupHom G H) (X : GSet G) (u : Product (USym H) (gset_underlying G X))
  : gset_induce G H f X (shape H) .fst
  ≔ set_trunc (GSetInducedSum G H f X (shape H))
      (shape G, (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (shape H)
                   (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (u .fst), u .snd))

{` The representative map respects ∼. `}
def induce_compare_respects_witness (G H : Group) (f : GroupHom G H) (X : GSet G)
  (u v : Product (USym H) (gset_underlying G X))
  (wt : AgsetInduceWitness (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) u v)
  : Id (gset_induce G H f X (shape H) .fst) (induce_compare_rep G H f X u) (induce_compare_rep G H f X v)
  ≔ let B ≔ BG H .carrier in let a0 ≔ shape G in let s ≔ shape H in
    let Bf ≔ hom_function G H f in let b ≔ Bf a0 in let p ≔ hom_point G H f in
    let ip ≔ inverse B s b p in
    let Y ≔ induced_sum_gset G H f X s in
    let S ≔ gset_underlying G X in
    let g ≔ wt .fst in
    let c : Id B b b ≔ refl Bf g in
    let ic ≔ inverse B b b c in
    let fg ≔ usym_hom G H f g in
    let qu ≔ concat B b s s ip (u .fst) in
    let qv ≔ concat B b s s ip (v .fst) in
    let e1 : Id (USym H) (concat B s s s fg (u .fst)) (v .fst) ≔ wt .snd .fst in
    let e2 : Id S (u .snd) (agset_act (abstr G) (ev_gset G X) g (v .snd)) ≔ wt .snd .snd in
    let efst : Id (Id B b s) (concat B b b s ic qv) qu
      ≔ concat (Id B b s) (concat B b b s ic qv) (concat B b b s ic (concat B b s s ip (concat B s s s fg (u .fst)))) qu
          (refl ((t ↦ concat B b b s ic (concat B b s s ip t)) : Id B s s → Id B b s)
            (inverse (USym H) (concat B s s s fg (u .fst)) (v .fst) e1))
          (induce_compare_conj_cancel B s b s p c (u .fst)) in
    let esnd : Id S (gset_act G X a0 a0 g (v .snd)) (u .snd)
      ≔ inverse S (u .snd) (gset_act G X a0 a0 g (v .snd))
          (concat S (u .snd) (agset_act (abstr G) (ev_gset G X) g (v .snd)) (gset_act G X a0 a0 g (v .snd))
            e2 (ev_gset_act G X g (v .snd))) in
    let e : Id (Y a0 .fst) (gset_act G Y a0 a0 g (qv, v .snd)) (qu, u .snd)
      ≔ concat (Y a0 .fst) (gset_act G Y a0 a0 g (qv, v .snd)) (concat B b b s ic qv, gset_act G X a0 a0 g (v .snd))
          (qu, u .snd)
          (induce_compare_sum_act G H f X s a0 a0 g qv (v .snd)) (efst, esnd) in
    inverse (gset_induce G H f X s .fst) (induce_compare_rep G H f X v) (induce_compare_rep G H f X u)
      (refl (set_trunc (ActionType G Y)) (action_type_path G Y a0 a0 (qv, v .snd) (qu, u .snd) g e))

def induce_compare_respects (G H : Group) (f : GroupHom G H) (X : GSet G)
  : Respects (Product (USym H) (gset_underlying G X)) (gset_induce G H f X (shape H) .fst)
      (agset_induce_relation (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X)) (induce_compare_rep G H f X)
  ≔ let W ≔ AgsetInduceWitness (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) in
    let T ≔ gset_induce G H f X (shape H) .fst in
    u v r ↦ mere_rec (W u v) (Id T (induce_compare_rep G H f X u) (induce_compare_rep G H f X v))
      (set_trunc_set (GSetInducedSum G H f X (shape H)) (induce_compare_rep G H f X u) (induce_compare_rep G H f X v))
      (wt ↦ induce_compare_respects_witness G H f X u v wt) r

{` The representative map reflects ∼: a witness from an identification in the action type. `}
def induce_compare_reflect_witness (G H : Group) (f : GroupHom G H) (X : GSet G)
  (u v : Product (USym H) (gset_underlying G X)) (k : USym G)
  (ek : Id (induced_sum_gset G H f X (shape H) (shape G) .fst)
    (gset_act G (induced_sum_gset G H f X (shape H)) (shape G) (shape G) k
      (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (shape H)
         (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (u .fst), u .snd))
    (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (shape H)
       (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (v .fst), v .snd))
  : AgsetInduceWitness (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) v u
  ≔ let B ≔ BG H .carrier in let a0 ≔ shape G in let s ≔ shape H in
    let Bf ≔ hom_function G H f in let b ≔ Bf a0 in let p ≔ hom_point G H f in
    let ip ≔ inverse B s b p in
    let Y ≔ induced_sum_gset G H f X s in
    let S ≔ gset_underlying G X in
    let c : Id B b b ≔ refl Bf k in
    let ic ≔ inverse B b b c in
    let qu ≔ concat B b s s ip (u .fst) in
    let qv ≔ concat B b s s ip (v .fst) in
    let ek' : Id (Y a0 .fst) (concat B b b s ic qu, gset_act G X a0 a0 k (u .snd)) (qv, v .snd)
      ≔ concat (Y a0 .fst) (concat B b b s ic qu, gset_act G X a0 a0 k (u .snd)) (gset_act G Y a0 a0 k (qu, u .snd))
          (qv, v .snd)
          (inverse (Y a0 .fst) (gset_act G Y a0 a0 k (qu, u .snd)) (concat B b b s ic qu, gset_act G X a0 a0 k (u .snd))
            (induce_compare_sum_act G H f X s a0 a0 k qu (u .snd)))
          ek in
    let d1 : Id (Id B b s) (concat B b b s ic qu) qv ≔ refl ((y ↦ y .fst) : Y a0 .fst → Id B b s) ek' in
    let d2 : Id S (gset_act G X a0 a0 k (u .snd)) (v .snd) ≔ refl ((y ↦ y .snd) : Y a0 .fst → S) ek' in
    (k, (induce_compare_conj_solve B s b s p c (u .fst) (v .fst) d1,
         concat S (v .snd) (gset_act G X a0 a0 k (u .snd)) (agset_act (abstr G) (ev_gset G X) k (u .snd))
           (inverse S (gset_act G X a0 a0 k (u .snd)) (v .snd) d2)
           (inverse S (agset_act (abstr G) (ev_gset G X) k (u .snd)) (gset_act G X a0 a0 k (u .snd))
             (ev_gset_act G X k (u .snd)))))

def induce_compare_reflects (G H : Group) (f : GroupHom G H) (X : GSet G)
  (u v : Product (USym H) (gset_underlying G X))
  (e : Id (gset_induce G H f X (shape H) .fst) (induce_compare_rep G H f X u) (induce_compare_rep G H f X v))
  : Rel (Product (USym H) (gset_underlying G X)) (agset_induce_relation (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X)) u v
  ≔ let B ≔ BG H .carrier in let a0 ≔ shape G in let s ≔ shape H in
    let b ≔ hom_function G H f a0 in
    let ip ≔ inverse B s b (hom_point G H f) in
    let Y ≔ induced_sum_gset G H f X s in
    let R ≔ agset_induce_relation (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) in
    let W ≔ AgsetInduceWitness (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) in
    let yu : Y a0 .fst ≔ (concat B b s s ip (u .fst), u .snd) in
    let yv : Y a0 .fst ≔ (concat B b s s ip (v .fst), v .snd) in
    let K ≔ Σ (USym G) (k ↦ Id (Y a0 .fst) (gset_act G Y a0 a0 k yu) yv) in
    let m : Mere K
      ≔ action_type_mere_path_exists G Y a0 a0 yu yv .map
          (set_trunc_paths (ActionType G Y) (a0, yu) (a0, yv) .map e) in
    R .symmetric v u
      (mere_rec K (Mere (W v u)) (mere_isprop (W v u))
        (kw ↦ mere (W v u) (induce_compare_reflect_witness G H f X u v (kw .fst) (kw .snd))) m)

{` The representative map is surjective (BG is connected). `}
def induce_compare_surjective (G H : Group) (f : GroupHom G H) (X : GSet G)
  : Surjective (Product (USym H) (gset_underlying G X)) (gset_induce G H f X (shape H) .fst) (induce_compare_rep G H f X)
  ≔ let B ≔ BG H .carrier in let a0 ≔ shape G in let s ≔ shape H in
    let b ≔ hom_function G H f a0 in let p ≔ hom_point G H f in
    let ip ≔ inverse B s b p in
    let Y ≔ induced_sum_gset G H f X s in
    let T ≔ ActionType G Y in
    let ST ≔ SetTrunc T in
    let P ≔ Product (USym H) (gset_underlying G X) in
    let rep ≔ induce_compare_rep G H f X in
    zz ↦ mere_rec (BookFiber T ST (set_trunc T) zz) (Mere (BookFiber P ST rep zz)) (mere_isprop (BookFiber P ST rep zz))
      (a ↦ mere_rec (BookFiber (Y a0 .fst) T (action_type_base_point G Y) (a .fst)) (Mere (BookFiber P ST rep zz))
         (mere_isprop (BookFiber P ST rep zz))
         (bpt ↦ let y ≔ bpt .fst in
           mere (BookFiber P ST rep zz)
             ((concat B s b s p (y .fst), y .snd),
              concat ST zz (set_trunc T (a .fst)) (rep (concat B s b s p (y .fst), y .snd)) (a .snd)
                (concat ST (set_trunc T (a .fst)) (set_trunc T (a0, y)) (rep (concat B s b s p (y .fst), y .snd))
                  (refl (set_trunc T) (bpt .snd))
                  (refl ((r ↦ set_trunc T (a0, (r, y .snd))) : Id B b s → ST)
                    (inverse (Id B b s) (concat B b s s ip (concat B s b s p (y .fst))) (y .fst)
                      (concat_left_inverse_cancel B s b s p (y .fst)))))))
         (action_type_base_point_surjective G Y (a .fst)))
      (set_trunc_surjective T zz)

{` The comparison map abstr(f)_!(ev_{sh_G} X) → f_!X(sh_H), [t, x] ↦ |(sh_G, (Bf_pt⁻¹ · t, x))|₀. `}
def induce_compare_map (G H : Group) (f : GroupHom G H) (X : GSet G)
  (z : AgsetInduceCarrier (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X)) : gset_induce G H f X (shape H) .fst
  ≔ quotient_rec (Product (USym H) (gset_underlying G X)) (gset_induce G H f X (shape H) .fst)
      (agset_induce_relation (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
      (set_trunc_set (GSetInducedSum G H f X (shape H))) (induce_compare_rep G H f X) (induce_compare_respects G H f X) z

{` Litmus: the comparison map on a class computes. `}
def induce_compare_class (G H : Group) (f : GroupHom G H) (X : GSet G) (t : USym H) (x : gset_underlying G X)
  : Id (gset_induce G H f X (shape H) .fst)
      (induce_compare_map G H f X (agset_induce_class (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X) t x))
      (set_trunc (GSetInducedSum G H f X (shape H))
        (shape G, (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (shape H)
                     (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) t, x)))
  ≔ refl (induce_compare_rep G H f X (t, x))

{` The equivalence (USym H × X(sh_G))/∼ ≃ f_!X(sh_H). `}
def induce_compare_book_equiv (G H : Group) (f : GroupHom G H) (X : GSet G)
  : BookEquiv (AgsetInduceCarrier (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X)) (gset_induce G H f X (shape H) .fst)
  ≔ surjection_quotient_equiv (Product (USym H) (gset_underlying G X)) (gset_induce G H f X (shape H) .fst)
      (set_trunc_set (GSetInducedSum G H f X (shape H)))
      (agset_induce_relation (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X)) (induce_compare_rep G H f X)
      (induce_compare_surjective G H f X) (induce_compare_respects G H f X) (induce_compare_reflects G H f X)

{` The comparison map commutes with the H-actions. `}
def induce_compare_equivariant (G H : Group) (f : GroupHom G H) (X : GSet G)
  : AgsetEquivariant (abstr H) (agset_induce (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
      (ev_gset H (gset_induce G H f X)) (induce_compare_map G H f X)
  ≔ let AG ≔ abstr G in let AH ≔ abstr H in let φ ≔ abstr_hom G H f in let EX ≔ ev_gset G X in
    let B ≔ BG H .carrier in let a0 ≔ shape G in let s ≔ shape H in
    let b ≔ hom_function G H f a0 in
    let ip ≔ inverse B s b (hom_point G H f) in
    let P ≔ Product (USym H) (gset_underlying G X) in
    let R ≔ agset_induce_relation AG AH φ EX in
    let ST ≔ gset_induce G H f X s .fst in
    let L ≔ ev_gset H (gset_induce G H f X) in
    let Φ ≔ induce_compare_map G H f X in
    h zq ↦ quotient_prop_induction P R
      (zq ↦ Id ST (Φ (agset_act AH (agset_induce AG AH φ EX) h zq)) (agset_act AH L h (Φ zq)))
      (zq ↦ set_trunc_set (GSetInducedSum G H f X s) (Φ (agset_act AH (agset_induce AG AH φ EX) h zq))
        (agset_act AH L h (Φ zq)))
      (u ↦ calc
         induce_compare_rep G H f X (concat B s s s (u .fst) h, u .snd)
         = set_trunc (GSetInducedSum G H f X s) (a0, (concat B b s s (concat B b s s ip (u .fst)) h, u .snd))
           by refl ((r ↦ set_trunc (GSetInducedSum G H f X s) (a0, (r, u .snd))) : Id B b s → ST)
             (inverse (Id B b s) (concat B b s s (concat B b s s ip (u .fst)) h) (concat B b s s ip (concat B s s s (u .fst) h))
               (concat_assoc B b s s s ip (u .fst) h))
         = gset_usym_act H (gset_induce G H f X) h (induce_compare_rep G H f X u)
           by inverse ST (gset_usym_act H (gset_induce G H f X) h (induce_compare_rep G H f X u))
             (set_trunc (GSetInducedSum G H f X s) (a0, (concat B b s s (concat B b s s ip (u .fst)) h, u .snd)))
             (induce_compare_trunc_act G H f X s s h a0 (concat B b s s ip (u .fst)) (u .snd))
         = agset_act AH L h (induce_compare_rep G H f X u)
           by inverse ST (agset_act AH L h (induce_compare_rep G H f X u))
             (gset_usym_act H (gset_induce G H f X) h (induce_compare_rep G H f X u))
             (ev_gset_act H (gset_induce G H f X) h (induce_compare_rep G H f X u)) ∎)
      zq

{` The isomorphism abstr(f)_!(ev_{sh_G} X) ≅ ev_{sh_H}(f_! X) of abstr(H)-sets. `}
def induce_compare_iso (G H : Group) (f : GroupHom G H) (X : GSet G)
  : AbstractGSetIso (abstr H) (agset_induce (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
      (ev_gset H (gset_induce G H f X))
  ≔ (native_equivalence (AgsetInduceCarrier (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
       (gset_induce G H f X (shape H) .fst) (induce_compare_book_equiv G H f X),
     h zq ↦ induce_compare_equivariant G H f X h zq)

def induce_ev_path (G H : Group) (f : GroupHom G H) (X : GSet G)
  : Id (AbstractGSet (abstr H)) (ev_gset H (gset_induce G H f X)) (agset_induce (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
  ≔ inverse (AbstractGSet (abstr H)) (agset_induce (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
      (ev_gset H (gset_induce G H f X))
      (agset_path_from_iso (abstr H) (agset_induce (abstr G) (abstr H) (abstr_hom G H f) (ev_gset G X))
        (ev_gset H (gset_induce G H f X)) (induce_compare_iso G H f X))

{` xca:f_!-abs(f)_!: the filled square ev_{sh_H} ∘ f_! = abstr(f)_! ∘ ev_{sh_G}. `}
def induce_ev_square (G H : Group) (f : GroupHom G H)
  : Id (GSet G → AbstractGSet (abstr H))
      (X ↦ gset_abstract_gset_equiv H .map (gset_induce G H f X))
      (X ↦ agset_induce (abstr G) (abstr H) (abstr_hom G H f) (gset_abstract_gset_equiv G .map X))
  ≔ funext (GSet G) (_ ↦ AbstractGSet (abstr H))
      (X ↦ gset_abstract_gset_equiv H .map (gset_induce G H f X))
      (X ↦ agset_induce (abstr G) (abstr H) (abstr_hom G H f) (gset_abstract_gset_equiv G .map X))
      (induce_ev_path G H f)
