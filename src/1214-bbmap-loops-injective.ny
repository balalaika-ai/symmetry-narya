export "1213-bbmap-central-loops"

{` Chapter 12, helper for the lemma at abelian.tex 928: for a simply
   connected pointed type X and a pointed type Y whose identity types are
   groupoids (e.g. Y = BB L), Ω is injective on pointed maps X →* Y:
   if Ω F and Ω F' agree pointwise then F = F'.

   Proof: for u : X put S(u) ≔ Σ(h : F u = F' u) Π(ℓ : pt = u)
   F_pt · (ap_F ℓ · h) = F'_pt · ap_F' ℓ (concatenation order). At u = pt,
   using Ω F ℓ = Ω F' ℓ, each factor is equivalent to F_pt · h = F'_pt (a set),
   Loop X is connected, so S(pt) ≃ Σ h (F_pt · h = F'_pt), a fiber of the
   equivalence F_pt · -, hence contractible; X is connected, so every S(u) is
   contractible, and the centers form a pointed homotopy F ~ F'. `}

{` Moving a conjugated loop across a path (two J-lemmas). `}
def bbmap_conjugate_shift (B : Type) (b c d : B) (q : Id B b c) (l : Id B c c) (h : Id B c d)
  : Id (Id B b d) (concat B b b d (pointed_loop_conjugate B b c q l) (concat B b c d q h))
      (concat B b c d q (concat B c c d l h))
  ≔ J B b (c q ↦ (l : Id B c c) (h : Id B c d) → Id (Id B b d)
        (concat B b b d (pointed_loop_conjugate B b c q l) (concat B b c d q h))
        (concat B b c d q (concat B c c d l h)))
      (l h ↦ calc
        concat B b b d (pointed_loop_conjugate B b b (refl b) l) (concat B b b d (refl b) h)
          = concat B b b d l (concat B b b d (refl b) h)
          by refl ((t ↦ concat B b b d t (concat B b b d (refl b) h)) : Id B b b → Id B b d)
            (loop_conjugate_at_refl B b l)
        = concat B b b d l h by refl (concat B b b d l) (concat_1p B b d h)
        = concat B b b d (refl b) (concat B b b d l h)
          by inverse (Id B b d) (concat B b b d (refl b) (concat B b b d l h)) (concat B b b d l h)
            (concat_1p B b d (concat B b b d l h)) ∎)
      c q l h

def bbmap_conjugate_shift_end (B : Type) (b c : B) (q : Id B b c) (l : Id B c c)
  : Id (Id B b c) (concat B b c c q l) (concat B b b c (pointed_loop_conjugate B b c q l) q)
  ≔ J B b (c q ↦ (l : Id B c c) → Id (Id B b c) (concat B b c c q l)
        (concat B b b c (pointed_loop_conjugate B b c q l) q))
      (l ↦ calc
        concat B b b b (refl b) l = l by concat_1p B b b l
        = pointed_loop_conjugate B b b (refl b) l
          by inverse (Id B b b) (pointed_loop_conjugate B b b (refl b) l) l (loop_conjugate_at_refl B b l)
        = concat B b b b (pointed_loop_conjugate B b b (refl b) l) (refl b)
          by inverse (Id B b b) (concat B b b b (pointed_loop_conjugate B b b (refl b) l) (refl b))
            (pointed_loop_conjugate B b b (refl b) l) (concat_p1 B b b (pointed_loop_conjugate B b b (refl b) l)) ∎)
      c q l

{` Maps from a connected type into a set are their value at a point. `}
def bbmap_connected_constant_equiv (C S : Type) (hC : Connected C) (hS : isSet S) (c0 : C) : Equiv (C → S) S
  ≔ quasi_inverse_equiv (C → S) S (g ↦ g c0) (s _ ↦ s)
      (g ↦ funext C (_ ↦ S) (_ ↦ g c0) g (c ↦ connected_set_map_constant C S hC hS g c0 c))
      (s ↦ refl s)

def BBMapHomotopyData (X Y : Pointed) (F F' : BookPointedMap X Y) (u : X .carrier) : Type
  ≔ Σ (Id (Y .carrier) (F .fst u) (F' .fst u))
      (h ↦ (l : Id (X .carrier) (X .point) u) → Id (Id (Y .carrier) (Y .point) (F' .fst u))
        (concat (Y .carrier) (Y .point) (F .fst (X .point)) (F' .fst u) (F .snd)
          (concat (Y .carrier) (F .fst (X .point)) (F .fst u) (F' .fst u) (refl (F .fst) l) h))
        (concat (Y .carrier) (Y .point) (F' .fst (X .point)) (F' .fst u) (F' .snd) (refl (F' .fst) l)))

{` At a loop ℓ with Ω F ℓ = Ω F' ℓ, the condition on h is F_pt · h = F'_pt. `}
def bbmap_homotopy_condition_equiv (X Y : Pointed) (F F' : BookPointedMap X Y)
  (l : Loop X) (e : Id (Loop Y) (loops_map X Y F l) (loops_map X Y F' l))
  (h : Id (Y .carrier) (F .fst (X .point)) (F' .fst (X .point)))
  : Equiv (Id (Id (Y .carrier) (Y .point) (F' .fst (X .point)))
        (concat (Y .carrier) (Y .point) (F .fst (X .point)) (F' .fst (X .point)) (F .snd)
          (concat (Y .carrier) (F .fst (X .point)) (F .fst (X .point)) (F' .fst (X .point)) (refl (F .fst) l) h))
        (concat (Y .carrier) (Y .point) (F' .fst (X .point)) (F' .fst (X .point)) (F' .snd) (refl (F' .fst) l)))
      (Id (Id (Y .carrier) (Y .point) (F' .fst (X .point)))
        (concat (Y .carrier) (Y .point) (F .fst (X .point)) (F' .fst (X .point)) (F .snd) h) (F' .snd))
  ≔ let B ≔ Y .carrier in let b ≔ Y .point in let c ≔ F .fst (X .point) in let c' ≔ F' .fst (X .point) in
    let m ≔ loops_map X Y F l in let m' ≔ loops_map X Y F' l in
    let P ≔ Id B b c' in
    compose_equiv
      (Id P (concat B b c c' (F .snd) (concat B c c c' (refl (F .fst) l) h)) (concat B b c' c' (F' .snd) (refl (F' .fst) l)))
      (Id P (concat B b b c' m (concat B b c c' (F .snd) h)) (concat B b b c' m (F' .snd)))
      (Id P (concat B b c c' (F .snd) h) (F' .snd))
      (path_endpoints_equiv P (concat B b c c' (F .snd) (concat B c c c' (refl (F .fst) l) h))
        (concat B b b c' m (concat B b c c' (F .snd) h))
        (concat B b c' c' (F' .snd) (refl (F' .fst) l)) (concat B b b c' m (F' .snd))
        (bbmap_conjugate_shift B b c c' (F .snd) (refl (F .fst) l) h)
        (concat P (concat B b c' c' (F' .snd) (refl (F' .fst) l)) (concat B b b c' m' (F' .snd))
          (concat B b b c' m (F' .snd))
          (bbmap_conjugate_shift_end B b c' (F' .snd) (refl (F' .fst) l))
          (refl ((t ↦ concat B b b c' t (F' .snd)) : Id B b b → P) (inverse (Id B b b) m m' e))))
      (canonical_inverse_equiv (Id P (concat B b c c' (F .snd) h) (F' .snd))
        (Id P (concat B b b c' m (concat B b c c' (F .snd) h)) (concat B b b c' m (F' .snd)))
        (equivalence_on_paths P P (concat_left_equiv B b b c' m) (concat B b c c' (F .snd) h) (F' .snd)))

def bbmap_homotopy_data_base_contractible (X Y : Pointed) (hX : SimplyConnected X)
  (hY : (y y' : Y .carrier) → isGroupoid (Id (Y .carrier) y y')) (F F' : BookPointedMap X Y)
  (e : (l : Loop X) → Id (Loop Y) (loops_map X Y F l) (loops_map X Y F' l))
  : isContr (BBMapHomotopyData X Y F F' (X .point))
  ≔ let B ≔ Y .carrier in let b ≔ Y .point in let c ≔ F .fst (X .point) in let c' ≔ F' .fst (X .point) in
    let T ≔ (h ↦ Id (Id B b c') (concat B b c c' (F .snd) h) (F' .snd)) : Id B c c' → Type in
    let R ≔ (h l ↦ Id (Id B b c') (concat B b c c' (F .snd) (concat B c c c' (refl (F .fst) l) h))
        (concat B b c' c' (F' .snd) (refl (F' .fst) l))) : Id B c c' → Loop X → Type in
    let Fib ≔ Fiber (Id B c c') (Id B b c') (concat B b c c' (F .snd)) (F' .snd) in
    let E : Equiv (BBMapHomotopyData X Y F F' (X .point)) Fib
      ≔ compose_equiv (BBMapHomotopyData X Y F F' (X .point)) (Σ (Id B c c') (h ↦ Loop X → T h)) Fib
          (family_equiv (Id B c c') (h ↦ (l : Loop X) → R h l) (h ↦ Loop X → T h)
            (h ↦ pi_family_equiv (Loop X) (l ↦ R h l) (_ ↦ T h)
              (l ↦ bbmap_homotopy_condition_equiv X Y F F' l (e l) h)))
          (family_equiv (Id B c c') (h ↦ Loop X → T h) T
            (h ↦ bbmap_connected_constant_equiv (Loop X) (T h) (hX .snd)
              (hY b c' (concat B b c c' (F .snd) h) (F' .snd)) (refl (X .point)))) in
    contractible_retract Fib (BBMapHomotopyData X Y F F' (X .point))
      (concat_left_equiv B b c c' (F .snd) .equiv (F' .snd))
      (equiv_inverse_map (BBMapHomotopyData X Y F F' (X .point)) Fib E) (E .map)
      (equiv_retraction (BBMapHomotopyData X Y F F' (X .point)) Fib E)

def bbmap_homotopy_data_contractible (X Y : Pointed) (hX : SimplyConnected X)
  (hY : (y y' : Y .carrier) → isGroupoid (Id (Y .carrier) y y')) (F F' : BookPointedMap X Y)
  (e : (l : Loop X) → Id (Loop Y) (loops_map X Y F l) (loops_map X Y F' l))
  : (u : X .carrier) → isContr (BBMapHomotopyData X Y F F' u)
  ≔ connected_based_elim native_truncation (X .carrier) (hX .fst) (X .point)
      (u ↦ isContr (BBMapHomotopyData X Y F F' u)) (u ↦ iscontr_isprop (BBMapHomotopyData X Y F F' u))
      (bbmap_homotopy_data_base_contractible X Y hX hY F F' e)

{` Ω is injective on pointed maps from a simply connected type into a
   type with groupoid identity types. `}
def bbmap_loops_injective (X Y : Pointed) (hX : SimplyConnected X)
  (hY : (y y' : Y .carrier) → isGroupoid (Id (Y .carrier) y y')) (F F' : BookPointedMap X Y)
  (e : (l : Loop X) → Id (Loop Y) (loops_map X Y F l) (loops_map X Y F' l))
  : Id (BookPointedMap X Y) F F'
  ≔ let B ≔ Y .carrier in let b ≔ Y .point in let a ≔ X .point in
    let c ≔ F .fst a in let c' ≔ F' .fst a in
    let K ≔ bbmap_homotopy_data_contractible X Y hX hY F F' e in
    let H ≔ (u ↦ K u .center .fst) : (u : X .carrier) → Id B (F .fst u) (F' .fst u) in
    equiv_inverse_map (Id (BookPointedMap X Y) F F') (PointedHomotopy X Y F F') (pointed_map_path_equiv X Y F F')
      (H, calc
        concat B b c c' (F .snd) (H a)
          = concat B b c c' (F .snd) (concat B c c c' (refl c) (H a))
          by refl (concat B b c c' (F .snd))
            (inverse (Id B c c') (concat B c c c' (refl c) (H a)) (H a) (concat_1p B c c' (H a)))
        = concat B b c' c' (F' .snd) (refl c') by K a .center .snd (refl a)
        = F' .snd by concat_p1 B b c' (F' .snd) ∎)
