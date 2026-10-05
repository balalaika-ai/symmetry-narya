export "878-wedge-induction-from-recursion"

{` Free groups on a sum are wedges: if X ≃ S + T (by e), then for free
   group signatures F on X, F1 on S and F2 on T, the type B F_X with
   i1 = rec(base, s ↦ loop_{e(inl s)}) : B F_S → B F_X,
   i2 = rec(base, t ↦ loop_{e(inr t)}) : B F_T → B F_X and the glue
   g = r1 · r2⁻¹ (r_k : i_k(base_k) = base the base computation rules) is a
   WedgeSignature of (B F_S, base) and (B F_T, base).  Proof: maps out of B F_X
   are bouquets indexed by X ≃ S + T, and wedge cocones are equivalent to
   such bouquets by Ψ(f1, f2, p) = (f1 base, inl s ↦ ap_{f1}(loop s),
   inr t ↦ p · ap_{f2}(loop t) · p⁻¹) (the universal properties of F_S, F_T);
   the cocone of h is sent by Ψ to the bouquet of h up to a path, so cocone
   evaluation is an equivalence and module 878 gives wedge induction.
   Instances: the wedge of two circles from a free group on Bool, and
   F_{n⊔1} as F_n ∨ Z (module 880). `}

def fsc_sum_loops (S T Z : Type) (z : Z) (l1 : S → Id Z z z) (l2 : T → Id Z z z) (y : Sum S T) : Id Z z z
  ≔ match y [ inl. s ↦ l1 s | inr. t ↦ l2 t ]

def wedge_bouquet_map (S T : Type) (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type)
  (c : WedgeCocone (free_pointed S F1) (free_pointed T F2) Z) : BouquetData (Sum S T) Z
  ≔ (c .fst (F1 .base),
     fsc_sum_loops S T Z (c .fst (F1 .base)) (s ↦ refl (c .fst) (F1 .loop s))
       (t ↦ pointed_loop_conjugate Z (c .fst (F1 .base)) (c .snd .fst (F2 .base)) (c .snd .snd)
         (refl (c .snd .fst) (F2 .loop t))))

{` Ψ is an equivalence (universal properties of F_S and F_T). `}
def fsc_conjugate_loops_equiv (T Z : Type) (z1 : Z)
  : Equiv (Σ (BouquetData T Z) (u ↦ Id Z z1 (u .fst))) (T → Id Z z1 z1)
  ≔ quasi_inverse_equiv (Σ (BouquetData T Z) (u ↦ Id Z z1 (u .fst))) (T → Id Z z1 z1)
      (v t ↦ pointed_loop_conjugate Z z1 (v .fst .fst) (v .snd) (v .fst .snd t))
      (l ↦ ((z1, l), refl z1))
      (v ↦ J Z z1
        (z2 p ↦ (l2 : T → Id Z z2 z2)
          → Id (Σ (BouquetData T Z) (u ↦ Id Z z1 (u .fst)))
              ((z1, t ↦ pointed_loop_conjugate Z z1 z2 p (l2 t)), refl z1) ((z2, l2), p))
        (l2 ↦ refl ((l ↦ ((z1, l), refl z1)) : (T → Id Z z1 z1) → Σ (BouquetData T Z) (u ↦ Id Z z1 (u .fst)))
          (funext T (_ ↦ Id Z z1 z1) (t ↦ pointed_loop_conjugate Z z1 z1 (refl z1) (l2 t)) l2
            (t ↦ loop_conjugate_at_refl Z z1 (l2 t))))
        (v .fst .fst) (v .snd) (v .fst .snd))
      (l ↦ funext T (_ ↦ Id Z z1 z1) (t ↦ pointed_loop_conjugate Z z1 z1 (refl z1) (l t)) l
        (t ↦ loop_conjugate_at_refl Z z1 (l t)))

def fsc_sum_bouquet_equiv (S T Z : Type)
  : Equiv (Σ (BouquetData S Z) (u ↦ T → Id Z (u .fst) (u .fst))) (BouquetData (Sum S T) Z)
  ≔ quasi_inverse_equiv (Σ (BouquetData S Z) (u ↦ T → Id Z (u .fst) (u .fst))) (BouquetData (Sum S T) Z)
      (v ↦ (v .fst .fst, fsc_sum_loops S T Z (v .fst .fst) (v .fst .snd) (v .snd)))
      (w ↦ ((w .fst, s ↦ w .snd (inl. s)), t ↦ w .snd (inr. t)))
      (v ↦ refl v)
      (w ↦ (refl (w .fst), funext (Sum S T) (_ ↦ Id Z (w .fst) (w .fst))
        (fsc_sum_loops S T Z (w .fst) (s ↦ w .snd (inl. s)) (t ↦ w .snd (inr. t))) (w .snd)
        (y ↦ match y [ inl. s ↦ refl (w .snd (inl. s)) | inr. t ↦ refl (w .snd (inr. t)) ])))

def wedge_bouquet_equiv (S T : Type) (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type)
  : Equiv (WedgeCocone (free_pointed S F1) (free_pointed T F2) Z) (BouquetData (Sum S T) Z)
  ≔ let A ≔ WedgeCocone (free_pointed S F1) (free_pointed T F2) Z in
    let B1 ≔ F1 .carrier in let B2 ≔ F2 .carrier in
    let A1 ≔ Σ (B1 → Z) (f1 ↦ Σ (BouquetData T Z) (u ↦ Id Z (f1 (F1 .base)) (u .fst))) in
    let A2 ≔ Σ (B1 → Z) (f1 ↦ T → Id Z (f1 (F1 .base)) (f1 (F1 .base))) in
    let A3 ≔ Σ (BouquetData S Z) (u ↦ T → Id Z (u .fst) (u .fst)) in
    let e ≔ compose_equiv A A2 (BouquetData (Sum S T) Z)
      (compose_equiv A A1 A2
        (family_equiv (B1 → Z) (f1 ↦ Σ (B2 → Z) (f2 ↦ Id Z (f1 (F1 .base)) (f2 (F2 .base))))
          (f1 ↦ Σ (BouquetData T Z) (u ↦ Id Z (f1 (F1 .base)) (u .fst)))
          (f1 ↦ sigma_reindex_equiv (B2 → Z) (BouquetData T Z) (free_universal_property T F2 Z)
            (u ↦ Id Z (f1 (F1 .base)) (u .fst))))
        (family_equiv (B1 → Z) (f1 ↦ Σ (BouquetData T Z) (u ↦ Id Z (f1 (F1 .base)) (u .fst)))
          (f1 ↦ T → Id Z (f1 (F1 .base)) (f1 (F1 .base)))
          (f1 ↦ fsc_conjugate_loops_equiv T Z (f1 (F1 .base)))))
      (compose_equiv A2 A3 (BouquetData (Sum S T) Z)
        (sigma_reindex_equiv (B1 → Z) (BouquetData S Z) (free_universal_property S F1 Z)
          (u ↦ T → Id Z (u .fst) (u .fst)))
        (fsc_sum_bouquet_equiv S T Z)) in
    equiv_change_map A (BouquetData (Sum S T) Z) e (wedge_bouquet_map S T F1 F2 Z) (c ↦ refl (e .map c))

{` A path in bouquet data gives the commutation of the loops with its
   first component. `}
def bouquet_path_coherence (S A : Type) (u v : BouquetData S A) (w : Id (BouquetData S A) u v) (s : S)
  : Id (Id A (u .fst) (v .fst)) (concat A (u .fst) (u .fst) (v .fst) (u .snd s) (w .fst))
      (concat A (u .fst) (v .fst) (v .fst) (w .fst) (v .snd s))
  ≔ J (BouquetData S A) u
      (v w ↦ Id (Id A (u .fst) (v .fst)) (concat A (u .fst) (u .fst) (v .fst) (u .snd s) (w .fst))
        (concat A (u .fst) (v .fst) (v .fst) (w .fst) (v .snd s)))
      (concat (Id A (u .fst) (u .fst)) (concat A (u .fst) (u .fst) (u .fst) (u .snd s) (refl (u .fst))) (u .snd s)
        (concat A (u .fst) (u .fst) (u .fst) (refl (u .fst)) (u .snd s))
        (concat_p1 A (u .fst) (u .fst) (u .snd s))
        (inverse (Id A (u .fst) (u .fst)) (concat A (u .fst) (u .fst) (u .fst) (refl (u .fst)) (u .snd s)) (u .snd s)
          (concat_1p A (u .fst) (u .fst) (u .snd s))))
      v w

{` Path algebra for the glue g = r1 · r2⁻¹. `}
def fsc_refl_inverse_refl (B : Type) (x : B)
  : Id (Id B x x) (concat B x x x (refl x) (inverse B x x (refl x))) (refl x)
  ≔ concat (Id B x x) (concat B x x x (refl x) (inverse B x x (refl x))) (inverse B x x (refl x)) (refl x)
      (concat_1p B x x (inverse B x x (refl x))) (inverse_refl B x)

def fsc_glue_base (B : Type) (x : B) (M L : Id B x x)
  (c : Id (Id B x x) (concat B x x x M (refl x)) (concat B x x x (refl x) L))
  : Id (Id B x x) (concat B x x x (refl x) L)
      (concat B x x x (pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M) (refl x))
  ≔ calc
      concat B x x x (refl x) L
      = concat B x x x M (refl x) by inverse (Id B x x) (concat B x x x M (refl x)) (concat B x x x (refl x) L) c
      = M by concat_p1 B x x M
      = pointed_loop_conjugate B x x (refl x) M
        by inverse (Id B x x) (pointed_loop_conjugate B x x (refl x) M) M (loop_conjugate_at_refl B x M)
      = pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M
        by refl ((q ↦ pointed_loop_conjugate B x x q M) : Id B x x → Id B x x)
          (inverse (Id B x x) (concat B x x x (refl x) (inverse B x x (refl x))) (refl x) (fsc_refl_inverse_refl B x))
      = concat B x x x (pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M) (refl x)
        by inverse (Id B x x)
          (concat B x x x (pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M) (refl x))
          (pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M)
          (concat_p1 B x x (pointed_loop_conjugate B x x (concat B x x x (refl x) (inverse B x x (refl x))) M)) ∎

def fsc_glue_coherence_at (B : Type) (x1 x2 : B) (r1 : Id B x1 x2) (M L : Id B x2 x2)
  (c : Id (Id B x2 x2) (concat B x2 x2 x2 M (refl x2)) (concat B x2 x2 x2 (refl x2) L))
  : Id (Id B x1 x2) (concat B x1 x2 x2 r1 L)
      (concat B x1 x1 x2 (pointed_loop_conjugate B x1 x2 (concat B x1 x2 x2 r1 (inverse B x2 x2 (refl x2))) M) r1)
  ≔ J B x1
      (x2 r1 ↦ (M L : Id B x2 x2) → Id (Id B x2 x2) (concat B x2 x2 x2 M (refl x2)) (concat B x2 x2 x2 (refl x2) L)
        → Id (Id B x1 x2) (concat B x1 x2 x2 r1 L)
            (concat B x1 x1 x2 (pointed_loop_conjugate B x1 x2 (concat B x1 x2 x2 r1 (inverse B x2 x2 (refl x2))) M) r1))
      (M L c ↦ fsc_glue_base B x1 M L c) x2 r1 M L c

def fsc_glue_coherence (B : Type) (x1 x2 b : B) (r1 : Id B x1 b) (r2 : Id B x2 b) (M : Id B x2 x2) (L : Id B b b)
  (c : Id (Id B x2 b) (concat B x2 x2 b M r2) (concat B x2 b b r2 L))
  : Id (Id B x1 b) (concat B x1 b b r1 L)
      (concat B x1 x1 b (pointed_loop_conjugate B x1 x2 (concat B x1 b x2 r1 (inverse B x2 b r2)) M) r1)
  ≔ J B x2
      (b r2 ↦ (r1 : Id B x1 b) (L : Id B b b) → Id (Id B x2 b) (concat B x2 x2 b M r2) (concat B x2 b b r2 L)
        → Id (Id B x1 b) (concat B x1 b b r1 L)
            (concat B x1 x1 b (pointed_loop_conjugate B x1 x2 (concat B x1 b x2 r1 (inverse B x2 b r2)) M) r1))
      (r1 L c ↦ fsc_glue_coherence_at B x1 x2 r1 M L c) b r2 r1 L c

def fsc_map_path_conjugate (A Z : Type) (h : A → Z) (a x : A) (p : Id A a x) (l : Id A x x)
  : Id (Id Z (h a) (h a)) (refl h (pointed_loop_conjugate A a x p l))
      (pointed_loop_conjugate Z (h a) (h x) (refl h p) (refl h l))
  ≔ calc
      refl h (pointed_loop_conjugate A a x p l)
      = concat Z (h a) (h x) (h a) (refl h p) (refl h (concat A x x a l (inverse A a x p)))
        by map_path_concat A Z h a x a p (concat A x x a l (inverse A a x p))
      = concat Z (h a) (h x) (h a) (refl h p) (concat Z (h x) (h x) (h a) (refl h l) (refl h (inverse A a x p)))
        by refl (concat Z (h a) (h x) (h a) (refl h p)) (map_path_concat A Z h x x a l (inverse A a x p))
      = pointed_loop_conjugate Z (h a) (h x) (refl h p) (refl h l)
        by refl ((q ↦ concat Z (h a) (h x) (h a) (refl h p) (concat Z (h x) (h x) (h a) (refl h l) q))
            : Id Z (h x) (h a) → Id Z (h a) (h a))
          (map_path_inverse A Z h a x p) ∎

{` The constructed wedge structure on B F_X. `}
def free_sum_incl1 (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) : F1 .carrier → F .carrier
  ≔ free_rec S F1 (F .carrier) (F .base, s ↦ F .loop (e .map (inl. s)))

def free_sum_incl2 (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F2 : FreeGroupSignature T) : F2 .carrier → F .carrier
  ≔ free_rec T F2 (F .carrier) (F .base, t ↦ F .loop (e .map (inr. t)))

def free_sum_base1 (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X) (F1 : FreeGroupSignature S)
  : Id (F .carrier) (free_sum_incl1 S T X e F F1 (F1 .base)) (F .base)
  ≔ free_rec_beta S F1 (F .carrier) (F .base, s ↦ F .loop (e .map (inl. s))) .fst

def free_sum_base2 (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X) (F2 : FreeGroupSignature T)
  : Id (F .carrier) (free_sum_incl2 S T X e F F2 (F2 .base)) (F .base)
  ≔ free_rec_beta T F2 (F .carrier) (F .base, t ↦ F .loop (e .map (inr. t))) .fst

def free_sum_glue (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T)
  : Id (F .carrier) (free_sum_incl1 S T X e F F1 (F1 .base)) (free_sum_incl2 S T X e F F2 (F2 .base))
  ≔ concat (F .carrier) (free_sum_incl1 S T X e F F1 (F1 .base)) (F .base) (free_sum_incl2 S T X e F F2 (F2 .base))
      (free_sum_base1 S T X e F F1)
      (inverse (F .carrier) (free_sum_incl2 S T X e F F2 (F2 .base)) (F .base) (free_sum_base2 S T X e F F2))

def free_sum_cocone (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type) (h : F .carrier → Z)
  : WedgeCocone (free_pointed S F1) (free_pointed T F2) Z
  ≔ fsc_wedge_cocone_eval (free_pointed S F1) (free_pointed T F2) (F .carrier)
      (free_sum_incl1 S T X e F F1) (free_sum_incl2 S T X e F F2) (free_sum_glue S T X e F F1 F2) Z h

def free_sum_bouquet (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X) (Z : Type)
  (h : F .carrier → Z) : BouquetData (Sum S T) Z
  ≔ (h (F .base), y ↦ refl h (F .loop (e .map y)))

def free_sum_coherence_left (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type) (h : F .carrier → Z) (s : S)
  : Id (Id Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)) (h (F .base))
        (refl h (free_sum_base1 S T X e F F1)) (refl h (F .loop (e .map (inl. s)))))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base))
        (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h) .snd (inl. s))
        (refl h (free_sum_base1 S T X e F F1)))
  ≔ let B ≔ F .carrier in let b ≔ F .base in
    let i1 ≔ free_sum_incl1 S T X e F F1 in
    let x1 ≔ i1 (F1 .base) in
    let r1 ≔ free_sum_base1 S T X e F F1 in
    let L ≔ F .loop (e .map (inl. s)) in
    calc
      concat Z (h x1) (h b) (h b) (refl h r1) (refl h L)
      = refl h (concat B x1 b b r1 L)
        by inverse (Id Z (h x1) (h b)) (refl h (concat B x1 b b r1 L))
          (concat Z (h x1) (h b) (h b) (refl h r1) (refl h L))
          (map_path_concat B Z h x1 b b r1 L)
      = refl h (concat B x1 x1 b (refl i1 (F1 .loop s)) r1)
        by refl (map_path B Z h x1 b) (inverse (Id B x1 b) (concat B x1 x1 b (refl i1 (F1 .loop s)) r1)
          (concat B x1 b b r1 L)
          (bouquet_path_coherence S B (free_bouquet S F1 B i1) (b, a ↦ F .loop (e .map (inl. a)))
            (free_rec_beta S F1 B (b, a ↦ F .loop (e .map (inl. a)))) s))
      = concat Z (h x1) (h x1) (h b) (refl h (refl i1 (F1 .loop s))) (refl h r1)
        by map_path_concat B Z h x1 x1 b (refl i1 (F1 .loop s)) r1 ∎

def free_sum_coherence_right (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type) (h : F .carrier → Z) (t : T)
  : Id (Id Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)) (h (F .base))
        (refl h (free_sum_base1 S T X e F F1)) (refl h (F .loop (e .map (inr. t)))))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base))
        (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h) .snd (inr. t))
        (refl h (free_sum_base1 S T X e F F1)))
  ≔ let B ≔ F .carrier in let b ≔ F .base in
    let i1 ≔ free_sum_incl1 S T X e F F1 in let i2 ≔ free_sum_incl2 S T X e F F2 in
    let x1 ≔ i1 (F1 .base) in let x2 ≔ i2 (F2 .base) in
    let r1 ≔ free_sum_base1 S T X e F F1 in let r2 ≔ free_sum_base2 S T X e F F2 in
    let g ≔ free_sum_glue S T X e F F1 F2 in
    let L ≔ F .loop (e .map (inr. t)) in
    let M ≔ refl i2 (F2 .loop t) in
    calc
      concat Z (h x1) (h b) (h b) (refl h r1) (refl h L)
      = refl h (concat B x1 b b r1 L)
        by inverse (Id Z (h x1) (h b)) (refl h (concat B x1 b b r1 L))
          (concat Z (h x1) (h b) (h b) (refl h r1) (refl h L))
          (map_path_concat B Z h x1 b b r1 L)
      = refl h (concat B x1 x1 b (pointed_loop_conjugate B x1 x2 g M) r1)
        by refl (map_path B Z h x1 b) (fsc_glue_coherence B x1 x2 b r1 r2 M L
          (bouquet_path_coherence T B (free_bouquet T F2 B i2) (b, a ↦ F .loop (e .map (inr. a)))
            (free_rec_beta T F2 B (b, a ↦ F .loop (e .map (inr. a)))) t))
      = concat Z (h x1) (h x1) (h b) (refl h (pointed_loop_conjugate B x1 x2 g M)) (refl h r1)
        by map_path_concat B Z h x1 x1 b (pointed_loop_conjugate B x1 x2 g M) r1
      = concat Z (h x1) (h x1) (h b) (pointed_loop_conjugate Z (h x1) (h x2) (refl h g) (refl h M)) (refl h r1)
        by refl ((q ↦ concat Z (h x1) (h x1) (h b) q (refl h r1)) : Id Z (h x1) (h x1) → Id Z (h x1) (h b))
          (fsc_map_path_conjugate B Z h x1 x2 g M) ∎

def free_sum_coherence (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type) (h : F .carrier → Z) (y : Sum S T)
  : Id (Id Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base)) (h (F .base))
        (refl h (free_sum_base1 S T X e F F1)) (refl h (F .loop (e .map y))))
      (concat Z (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (free_sum_incl1 S T X e F F1 (F1 .base))) (h (F .base))
        (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h) .snd y)
        (refl h (free_sum_base1 S T X e F F1)))
  ≔ match y [
  | inl. s ↦ free_sum_coherence_left S T X e F F1 F2 Z h s
  | inr. t ↦ free_sum_coherence_right S T X e F F1 F2 Z h t ]

def free_sum_comparison (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) (Z : Type) (h : F .carrier → Z)
  : Id (BouquetData (Sum S T) Z) (free_sum_bouquet S T X e F Z h)
      (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h))
  ≔ bouquet_path_from_coherence (Sum S T) Z (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h))
      (h (F .base)) (refl h (free_sum_base1 S T X e F F1)) (y ↦ refl h (F .loop (e .map y)))
      (free_sum_coherence S T X e F F1 F2 Z h)

{` Maps out of B F_X are bouquets indexed by S + T. `}
def free_sum_bouquet_equiv (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X) (Z : Type)
  : Equiv (F .carrier → Z) (BouquetData (Sum S T) Z)
  ≔ compose_equiv (F .carrier → Z) (BouquetData X Z) (BouquetData (Sum S T) Z)
      (free_universal_property X F Z)
      (family_equiv Z (z ↦ X → Id Z z z) (z ↦ Sum S T → Id Z z z)
        (z ↦ precompose_equiv (Sum S T) X (Id Z z z) e))

def free_sum_wedge_property (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T)
  : NondependentWedgeProperty (free_pointed S F1) (free_pointed T F2) (F .carrier)
      (free_sum_incl1 S T X e F F1) (free_sum_incl2 S T X e F F2) (free_sum_glue S T X e F F1 F2)
  ≔ Z ↦
    let A ≔ WedgeCocone (free_pointed S F1) (free_pointed T F2) Z in
    let Psi ≔ wedge_bouquet_equiv S T F1 F2 Z in
    equiv_change_map (F .carrier → Z) A
      (compose_equiv (F .carrier → Z) (BouquetData (Sum S T) Z) A (free_sum_bouquet_equiv S T X e F Z)
        (canonical_inverse_equiv A (BouquetData (Sum S T) Z) Psi))
      (free_sum_cocone S T X e F F1 F2 Z)
      (h ↦ inverse_at_known_point A (BouquetData (Sum S T) Z) Psi (free_sum_cocone S T X e F F1 F2 Z h)
        (free_sum_bouquet S T X e F Z h)
        (inverse (BouquetData (Sum S T) Z) (free_sum_bouquet S T X e F Z h)
          (wedge_bouquet_map S T F1 F2 Z (free_sum_cocone S T X e F F1 F2 Z h))
          (free_sum_comparison S T X e F F1 F2 Z h)))
      .equiv

{` F_X with X ≃ S + T is the wedge F_S ∨ F_T. `}
def free_sum_wedge_signature (S T X : Type) (e : Equiv (Sum S T) X) (F : FreeGroupSignature X)
  (F1 : FreeGroupSignature S) (F2 : FreeGroupSignature T) : WedgeSignature (free_pointed S F1) (free_pointed T F2)
  ≔ wedge_signature_from_recursion (free_pointed S F1) (free_pointed T F2) (F .carrier)
      (free_sum_incl1 S T X e F F1) (free_sum_incl2 S T X e F F2) (free_sum_glue S T X e F F1 F2)
      (free_sum_wedge_property S T X e F F1 F2)

{` The wedge of two circles, from a free group on Bool (true ↦ first
   summand, false ↦ second). `}
def fsc_unit_sum_bool (y : Sum Unit Unit) : Bool ≔ match y [ inl. _ ↦ true. | inr. _ ↦ false. ]

def fsc_bool_unit_sum (b : Bool) : Sum Unit Unit ≔ match b [ true. ↦ inl. star. | false. ↦ inr. star. ]

def fsc_unit_sum_bool_equiv : Equiv (Sum Unit Unit) Bool
  ≔ quasi_inverse_equiv (Sum Unit Unit) Bool fsc_unit_sum_bool fsc_bool_unit_sum
      (y ↦ match y [ inl. u ↦ match u [ star. ↦ refl (inl. star. : Sum Unit Unit) ]
                   | inr. u ↦ match u [ star. ↦ refl (inr. star. : Sum Unit Unit) ] ])
      (b ↦ match b [ true. ↦ refl (true. : Bool) | false. ↦ refl (false. : Bool) ])

def circle_wedge_from_free_bool (F : FreeGroupSignature Bool) (C : CircleSignature)
  : WedgeSignature (circle_pointed C) (circle_pointed C)
  ≔ free_sum_wedge_signature Unit Unit Bool fsc_unit_sum_bool_equiv F (circle_free_signature C) (circle_free_signature C)

{` S¹ ∨ S¹ without HITs: the constructed circle wedged with itself, carried
   by the classifying type of the constructed free group on Bool. `}
def constructed_circle_wedge : WedgeSignature (circle_pointed constructed_circle) (circle_pointed constructed_circle)
  ≔ circle_wedge_from_free_bool (constructed_free_group_signature Bool fw_bool_decidable_equality) constructed_circle

def constructed_circle_wedge_carrier
  : Id Type (constructed_circle_wedge .carrier) (BG free_bool_group .carrier)
  ≔ refl (BG free_bool_group .carrier)

def constructed_circle_wedge_groupoid : isGroupoid (constructed_circle_wedge .carrier)
  ≔ bg_groupoid free_bool_group
