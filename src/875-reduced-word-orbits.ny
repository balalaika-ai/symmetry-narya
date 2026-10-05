export "861-free-words"
export "870-free-s-sets"

{` Maps out of the tree of reduced words (the combinatorial core of the
   freeness of reduced words, generalizing ForwardSteps/forward_steps_equiv
   of module 220 from N to the tree of reduced words).

   The nonempty reduced words are the edges x·w (x a signed letter, w a
   word, x·w reduced).  For a type Y with F : S → (Y ≃ Y), let x act by
   F_a if x = a and by F_a⁻¹ if x = ā, and words act by composition
   (fsc_word_act, ⟦x w⟧ y = x(⟦w⟧ y)).  A map φ on reduced words with
   φ(x·w) = x(φ w) for every edge (ReducedEdgeSteps) is the same as a point
   y = φ(ε) together with paths φ(x·w) = ⟦x·w⟧ y, and the type of maps of
   the latter kind with a fixed y is contractible.  Hence maps with edge
   steps are equivalent to Y, by evaluation at ε, for EVERY type Y. `}

def ReducedEdgeAt (S : Type) (x : SignedLetter S) : Type
  ≔ Σ (SignedWord S) (w ↦ IsReducedWord S (cons. x w))

def ReducedEdge (S : Type) : Type ≔ Σ (SignedLetter S) (ReducedEdgeAt S)

def reduced_edge_word (S : Type) (e : ReducedEdge S) : ReducedWord S ≔ (cons. (e .fst) (e .snd .fst), e .snd .snd)

def reduced_edge_tail (S : Type) (e : ReducedEdge S) : ReducedWord S ≔ (e .snd .fst, e .snd .snd .snd)

{` Signed letters act on Y: a by F_a, ā by F_a⁻¹; words by composition. `}
def fsc_signed_map (S Y : Type) (F : S → Equiv Y Y) (x : SignedLetter S) : Y → Y
  ≔ match x [ inl. a ↦ F a .map | inr. a ↦ equiv_inverse_map Y Y (F a) ]

def fsc_word_act (S Y : Type) (F : S → Equiv Y Y) (w : SignedWord S) (y : Y) : Y
  ≔ match w [ nil. ↦ y | cons. x v ↦ fsc_signed_map S Y F x (fsc_word_act S Y F v y) ]

{` Functions on reduced words = a value at ε and a function on edges. `}
def fsc_rw_cases (S Y : Type) (y : Y) (g : ReducedEdge S → Y) (w : SignedWord S) (h : IsReducedWord S w) : Y
  ≔ match w [ nil. ↦ y | cons. x v ↦ g (x, (v, h)) ]

def fsc_rw_fun (S Y : Type) (y : Y) (g : ReducedEdge S → Y) (r : ReducedWord S) : Y
  ≔ fsc_rw_cases S Y y g (r .fst) (r .snd)

def fsc_rw_restrict (S Y : Type) (phi : ReducedWord S → Y) : Product Y (ReducedEdge S → Y)
  ≔ (phi (reduced_word_empty S), e ↦ phi (reduced_edge_word S e))

def fsc_rw_restrict_cases (S Y : Type) (phi : ReducedWord S → Y) (w : SignedWord S) (h : IsReducedWord S w)
  : Id Y (fsc_rw_cases S Y (phi (reduced_word_empty S)) (e ↦ phi (reduced_edge_word S e)) w h) (phi (w, h))
  ≔ match w [
  | nil. ↦ match h [ star. ↦ refl (phi (nil., star.)) ]
  | cons. x v ↦ refl (phi (cons. x v, h)) ]

def fsc_rw_split_equiv (S Y : Type) : Equiv (Product Y (ReducedEdge S → Y)) (ReducedWord S → Y)
  ≔ quasi_inverse_equiv (Product Y (ReducedEdge S → Y)) (ReducedWord S → Y)
      (u ↦ fsc_rw_fun S Y (u .fst) (u .snd)) (fsc_rw_restrict S Y)
      (u ↦ refl u)
      (phi ↦ funext (ReducedWord S) (_ ↦ Y)
        (fsc_rw_fun S Y (phi (reduced_word_empty S)) (e ↦ phi (reduced_edge_word S e))) phi
        (r ↦ fsc_rw_restrict_cases S Y phi (r .fst) (r .snd)))

{` Edge steps φ(x·w) = x(φ w) and orbit paths g(x·w) = ⟦x·w⟧ y. `}
def ReducedEdgeSteps (S Y : Type) (F : S → Equiv Y Y) (phi : ReducedWord S → Y) : Type
  ≔ (e : ReducedEdge S) → Id Y (phi (reduced_edge_word S e)) (fsc_signed_map S Y F (e .fst) (phi (reduced_edge_tail S e)))

def fsc_edge_value (S Y : Type) (F : S → Equiv Y Y) (y : Y) (e : ReducedEdge S) : Y
  ≔ fsc_word_act S Y F (cons. (e .fst) (e .snd .fst)) y

def ReducedEdgeOrbits (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y) : Type
  ≔ (e : ReducedEdge S) → Id Y (g e) (fsc_edge_value S Y F y e)

def fsc_steps_aux (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (st : ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) (w : SignedWord S) (h : IsReducedWord S w)
  : Id Y (fsc_rw_cases S Y y g w h) (fsc_word_act S Y F w y)
  ≔ match w [
  | nil. ↦ refl y
  | cons. x v ↦ concat Y (g (x, (v, h))) (fsc_signed_map S Y F x (fsc_rw_cases S Y y g v (h .snd)))
      (fsc_signed_map S Y F x (fsc_word_act S Y F v y))
      (st (x, (v, h))) (refl (fsc_signed_map S Y F x) (fsc_steps_aux S Y F y g st v (h .snd))) ]

def fsc_steps_orbits (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (st : ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) : ReducedEdgeOrbits S Y F y g
  ≔ e ↦ fsc_steps_aux S Y F y g st (cons. (e .fst) (e .snd .fst)) (e .snd .snd)

def fsc_orbits_aux (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (H : ReducedEdgeOrbits S Y F y g) (w : SignedWord S) (h : IsReducedWord S w)
  : Id Y (fsc_rw_cases S Y y g w h) (fsc_word_act S Y F w y)
  ≔ match w [ nil. ↦ refl y | cons. x v ↦ H (x, (v, h)) ]

def fsc_orbits_steps (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (H : ReducedEdgeOrbits S Y F y g) : ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)
  ≔ e ↦ concat Y (g e) (fsc_edge_value S Y F y e)
      (fsc_signed_map S Y F (e .fst) (fsc_rw_cases S Y y g (e .snd .fst) (e .snd .snd .snd)))
      (H e)
      (inverse Y (fsc_signed_map S Y F (e .fst) (fsc_rw_cases S Y y g (e .snd .fst) (e .snd .snd .snd)))
        (fsc_signed_map S Y F (e .fst) (fsc_word_act S Y F (e .snd .fst) y))
        (refl (fsc_signed_map S Y F (e .fst)) (fsc_orbits_aux S Y F y g H (e .snd .fst) (e .snd .snd .snd))))

def fsc_aux_agree (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (st : ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) (w : SignedWord S) (h : IsReducedWord S w)
  : Id (Id Y (fsc_rw_cases S Y y g w h) (fsc_word_act S Y F w y))
      (fsc_orbits_aux S Y F y g (fsc_steps_orbits S Y F y g st) w h) (fsc_steps_aux S Y F y g st w h)
  ≔ match w [
  | nil. ↦ refl (refl y)
  | cons. x v ↦ refl (fsc_steps_aux S Y F y g st (cons. x v) h) ]

def fsc_steps_roundtrip (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (st : ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) (e : ReducedEdge S)
  : Id (Id Y (g e) (fsc_signed_map S Y F (e .fst) (fsc_rw_cases S Y y g (e .snd .fst) (e .snd .snd .snd))))
      (fsc_orbits_steps S Y F y g (fsc_steps_orbits S Y F y g st) e) (st e)
  ≔ let x ≔ e .fst in let w ≔ e .snd .fst in let h ≔ e .snd .snd .snd in
    let G ≔ fsc_signed_map S Y F x in
    let A ≔ fsc_steps_aux S Y F y g st w h in
    calc
      fsc_orbits_steps S Y F y g (fsc_steps_orbits S Y F y g st) e
      = concat Y (g e) (G (fsc_word_act S Y F w y)) (G (fsc_rw_cases S Y y g w h))
          (concat Y (g e) (G (fsc_rw_cases S Y y g w h)) (G (fsc_word_act S Y F w y)) (st e) (refl G A))
          (inverse Y (G (fsc_rw_cases S Y y g w h)) (G (fsc_word_act S Y F w y)) (refl G A))
        by refl ((q ↦ concat Y (g e) (G (fsc_word_act S Y F w y)) (G (fsc_rw_cases S Y y g w h))
            (concat Y (g e) (G (fsc_rw_cases S Y y g w h)) (G (fsc_word_act S Y F w y)) (st e) (refl G A))
            (inverse Y (G (fsc_rw_cases S Y y g w h)) (G (fsc_word_act S Y F w y)) (refl G q)))
          : Id Y (fsc_rw_cases S Y y g w h) (fsc_word_act S Y F w y) → Id Y (g e) (G (fsc_rw_cases S Y y g w h)))
          (fsc_aux_agree S Y F y g st w h)
      = st e
        by concat_cancel_inverse_right Y (g e) (G (fsc_rw_cases S Y y g w h)) (G (fsc_word_act S Y F w y)) (st e) (refl G A) ∎

def fsc_orbits_aux_roundtrip (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  (H : ReducedEdgeOrbits S Y F y g) (w : SignedWord S) (h : IsReducedWord S w)
  : Id (Id Y (fsc_rw_cases S Y y g w h) (fsc_word_act S Y F w y))
      (fsc_steps_aux S Y F y g (fsc_orbits_steps S Y F y g H) w h) (fsc_orbits_aux S Y F y g H w h)
  ≔ match w [
  | nil. ↦ refl (refl y)
  | cons. x v ↦
      let G ≔ fsc_signed_map S Y F x in
      let O ≔ fsc_orbits_aux S Y F y g H v (h .snd) in
      calc
        fsc_steps_aux S Y F y g (fsc_orbits_steps S Y F y g H) (cons. x v) h
        = concat Y (g (x, (v, h))) (G (fsc_rw_cases S Y y g v (h .snd))) (G (fsc_word_act S Y F v y))
            (fsc_orbits_steps S Y F y g H (x, (v, h))) (refl G O)
          by refl ((q ↦ concat Y (g (x, (v, h))) (G (fsc_rw_cases S Y y g v (h .snd))) (G (fsc_word_act S Y F v y))
              (fsc_orbits_steps S Y F y g H (x, (v, h))) (refl G q))
            : Id Y (fsc_rw_cases S Y y g v (h .snd)) (fsc_word_act S Y F v y) → Id Y (g (x, (v, h))) (G (fsc_word_act S Y F v y)))
            (fsc_orbits_aux_roundtrip S Y F y g H v (h .snd))
        = H (x, (v, h))
          by concat_inverse_cancel_right Y (g (x, (v, h))) (G (fsc_word_act S Y F v y)) (G (fsc_rw_cases S Y y g v (h .snd)))
            (H (x, (v, h))) (refl G O) ∎ ]

def fsc_steps_orbits_equiv (S Y : Type) (F : S → Equiv Y Y) (y : Y) (g : ReducedEdge S → Y)
  : Equiv (ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) (ReducedEdgeOrbits S Y F y g)
  ≔ quasi_inverse_equiv (ReducedEdgeSteps S Y F (fsc_rw_fun S Y y g)) (ReducedEdgeOrbits S Y F y g)
      (fsc_steps_orbits S Y F y g) (fsc_orbits_steps S Y F y g)
      (st ↦ funext (ReducedEdge S)
        (e ↦ Id Y (g e) (fsc_signed_map S Y F (e .fst) (fsc_rw_cases S Y y g (e .snd .fst) (e .snd .snd .snd))))
        (fsc_orbits_steps S Y F y g (fsc_steps_orbits S Y F y g st)) st (fsc_steps_roundtrip S Y F y g st))
      (H ↦ funext (ReducedEdge S) (e ↦ Id Y (g e) (fsc_edge_value S Y F y e))
        (fsc_steps_orbits S Y F y g (fsc_orbits_steps S Y F y g H)) H
        (e ↦ fsc_orbits_aux_roundtrip S Y F y g H (cons. (e .fst) (e .snd .fst)) (e .snd .snd)))

{` For a fixed y the functions on edges with orbit paths form a singleton. `}
def fsc_edge_orbit_functions_contractible (S Y : Type) (F : S → Equiv Y Y) (y : Y)
  : isContr (Σ (ReducedEdge S → Y) (g ↦ ReducedEdgeOrbits S Y F y g))
  ≔ let c ≔ fsc_edge_value S Y F y in
    hlevel_equiv zero. (Σ (ReducedEdge S → Y) (g ↦ Id (ReducedEdge S → Y) g c))
      (Σ (ReducedEdge S → Y) (g ↦ ReducedEdgeOrbits S Y F y g))
      (family_equiv (ReducedEdge S → Y) (g ↦ Id (ReducedEdge S → Y) g c) (g ↦ ReducedEdgeOrbits S Y F y g)
        (g ↦ canonical_inverse_equiv (Homotopy (ReducedEdge S) (_ ↦ Y) g c) (Id (ReducedEdge S → Y) g c)
          (funext_equiv (ReducedEdge S) (_ ↦ Y) g c)))
      (path_to_contractible (ReducedEdge S → Y) c)

{` Maps on reduced words with edge steps ≃ Y, by evaluation at ε. `}
def ReducedStepMaps (S Y : Type) (F : S → Equiv Y Y) : Type
  ≔ Σ (ReducedWord S → Y) (ReducedEdgeSteps S Y F)

def ReducedSplitOrbits (S Y : Type) (F : S → Equiv Y Y) : Type
  ≔ Σ (Product Y (ReducedEdge S → Y)) (u ↦ ReducedEdgeOrbits S Y F (u .fst) (u .snd))

def ReducedSplitOrbitFibers (S Y : Type) (F : S → Equiv Y Y) : Type
  ≔ Σ Y (y ↦ Σ (ReducedEdge S → Y) (g ↦ ReducedEdgeOrbits S Y F y g))

def fsc_split_orbit_fibers_equiv (S Y : Type) (F : S → Equiv Y Y)
  : Equiv (ReducedSplitOrbits S Y F) (ReducedSplitOrbitFibers S Y F)
  ≔ quasi_inverse_equiv (ReducedSplitOrbits S Y F) (ReducedSplitOrbitFibers S Y F)
      (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (v ↦ ((v .fst, v .snd .fst), v .snd .snd))
      (u ↦ refl u) (v ↦ refl v)

def fsc_step_maps_equiv (S Y : Type) (F : S → Equiv Y Y) : Equiv (ReducedStepMaps S Y F) Y
  ≔ let A0 ≔ ReducedStepMaps S Y F in
    let A1 ≔ Σ (Product Y (ReducedEdge S → Y)) (u ↦ ReducedEdgeSteps S Y F (fsc_rw_fun S Y (u .fst) (u .snd))) in
    let A2 ≔ ReducedSplitOrbits S Y F in
    let A3 ≔ ReducedSplitOrbitFibers S Y F in
    compose_equiv A0 A3 Y
      (compose_equiv A0 A2 A3
        (compose_equiv A0 A1 A2
          (canonical_inverse_equiv A1 A0
            (sigma_reindex_equiv (Product Y (ReducedEdge S → Y)) (ReducedWord S → Y) (fsc_rw_split_equiv S Y)
              (ReducedEdgeSteps S Y F)))
          (family_equiv (Product Y (ReducedEdge S → Y))
            (u ↦ ReducedEdgeSteps S Y F (fsc_rw_fun S Y (u .fst) (u .snd)))
            (u ↦ ReducedEdgeOrbits S Y F (u .fst) (u .snd))
            (u ↦ fsc_steps_orbits_equiv S Y F (u .fst) (u .snd))))
        (fsc_split_orbit_fibers_equiv S Y F))
      (contractible_fiber_projection Y (y ↦ Σ (ReducedEdge S → Y) (g ↦ ReducedEdgeOrbits S Y F y g))
        (fsc_edge_orbit_functions_contractible S Y F))

{` Litmus: the equivalence is evaluation at the empty word. `}
def fsc_step_maps_equiv_evaluation (S Y : Type) (F : S → Equiv Y Y) (m : ReducedStepMaps S Y F)
  : Id Y (fsc_step_maps_equiv S Y F .map m) (m .fst (reduced_word_empty S))
  ≔ refl (m .fst (reduced_word_empty S))
