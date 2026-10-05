export "482-six-element-bicycles"

{` rem:F2-first-look (group.tex 1896–1953): bicycles are the connected
   coverings over S¹ ∨ S¹, "constructed in analogy with S¹ as a higher
   inductive type with three constructors: a base point and two loops".
   As for the circle in chapter 3 (CircleSignature, thm:cycset-connS1cover),
   the pinned Narya has no higher inductive types, so the figure eight is a
   parameter: a signature with base, loop₁, loop₂ and the dependent
   induction principle with its computation law (an identification of the
   boundary data). For every such signature we prove
   - the universal property (S¹∨S¹ → A) ≃ Σ_{a:A} (a = a) × (a = a),
   - set families over it ≃ sets with two permutations,
   - connected coverings over it ≃ Bicyc (figure_eight_connected_coverings_bicycles),
   with the bicycle given by the fiber over base and transport along the
   two loops. The S-fold generalization and the free groups are forward
   references (sec:freegroups) and are not formalized here. `}

def FigureEightBoundary (W : Type) (base : W) (l1 l2 : Id W base base) (P : W → Type) : Type
  ≔ Σ (P base) (b ↦ Product (Id P l1 b b) (Id P l2 b b))

def figure_eight_evaluate (W : Type) (base : W) (l1 l2 : Id W base base) (P : W → Type) (f : (x : W) → P x)
  : FigureEightBoundary W base l1 l2 P
  ≔ (f base, (refl f l1, refl f l2))

def FigureEightSignature : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop1 : Id carrier base base,
  loop2 : Id carrier base base,
  induction : (P : carrier → Type) (d : FigureEightBoundary carrier base loop1 loop2 P)
    → Σ ((x : carrier) → P x)
        (f ↦ Id (FigureEightBoundary carrier base loop1 loop2 P) (figure_eight_evaluate carrier base loop1 loop2 P f) d))

def FigureEightLoops (A : Type) : Type ≔ Σ A (a ↦ Product (Id A a a) (Id A a a))

def figure_eight_eval (W : FigureEightSignature) (A : Type) (f : W .carrier → A) : FigureEightLoops A
  ≔ (f (W .base), (refl f (W .loop1), refl f (W .loop2)))

def figure_eight_rec (W : FigureEightSignature) (A : Type) (d : FigureEightLoops A) : W .carrier → A
  ≔ W .induction (_ ↦ A) d .fst

def figure_eight_rec_beta (W : FigureEightSignature) (A : Type) (d : FigureEightLoops A)
  : Id (FigureEightLoops A) (figure_eight_eval W A (figure_eight_rec W A d)) d
  ≔ W .induction (_ ↦ A) d .snd

def figure_eight_maps_equal (W : FigureEightSignature) (A : Type) (f g : W .carrier → A)
  (d : Id (FigureEightLoops A) (figure_eight_eval W A f) (figure_eight_eval W A g))
  : Id (W .carrier → A) f g
  ≔ funext (W .carrier) (_ ↦ A) f g
      (W .induction (x ↦ Id A (f x) (g x)) (d .fst, (sym (d .snd .fst), sym (d .snd .snd))) .fst)

{` The universal property of S¹ ∨ S¹ (analogue of lem:freeloopspace). `}
def figure_eight_universal_property (W : FigureEightSignature) (A : Type)
  : Equiv (W .carrier → A) (FigureEightLoops A)
  ≔ quasi_inverse_equiv (W .carrier → A) (FigureEightLoops A) (figure_eight_eval W A) (figure_eight_rec W A)
      (f ↦ figure_eight_maps_equal W A (figure_eight_rec W A (figure_eight_eval W A f)) f
        (figure_eight_rec_beta W A (figure_eight_eval W A f)))
      (figure_eight_rec_beta W A)

def figure_eight_ind_prop (W : FigureEightSignature) (P : W .carrier → Type)
  (hP : (x : W .carrier) → isProp (P x)) (b : P (W .base)) : (x : W .carrier) → P x
  ≔ W .induction P
      (b, (pathover_of_eq (W .carrier) P (W .base) (W .base) (W .loop1) b b
             (hP (W .base) (transport (W .carrier) P (W .base) (W .base) (W .loop1) b) b),
           pathover_of_eq (W .carrier) P (W .base) (W .base) (W .loop2) b b
             (hP (W .base) (transport (W .carrier) P (W .base) (W .base) (W .loop2) b) b))) .fst

def figure_eight_connected_to_base (W : FigureEightSignature) (x : W .carrier) : Mere (Id (W .carrier) x (W .base))
  ≔ figure_eight_ind_prop W (y ↦ Mere (Id (W .carrier) y (W .base))) (y ↦ mere_isprop (Id (W .carrier) y (W .base)))
      (mere (Id (W .carrier) (W .base) (W .base)) (refl (W .base))) x

{` Set families over S¹ ∨ S¹ are sets with two permutations. `}
def figure_eight_setfamilies_triples (W : FigureEightSignature) : Equiv (W .carrier → SetTypes) BicycleDataTriples
  ≔ compose_equiv (W .carrier → SetTypes) (FigureEightLoops SetTypes) BicycleDataTriples
      (figure_eight_universal_property W SetTypes)
      (family_equiv SetTypes (S ↦ Product (Id SetTypes S S) (Id SetTypes S S)) (S ↦ Σ (SetAutomorphisms S) (_ ↦ SetAutomorphisms S))
        (S ↦ product_equiv (Id SetTypes S S) (Id SetTypes S S) (SetAutomorphisms S) (SetAutomorphisms S)
          (set_paths_transport_equiv S S) (set_paths_transport_equiv S S)))

def figure_eight_coverings_triples (W : FigureEightSignature) : Equiv (Coverings (W .carrier)) BicycleDataTriples
  ≔ compose_equiv (Coverings (W .carrier)) (W .carrier → SetTypes) BicycleDataTriples
      (coverings_setfamilies_equiv (W .carrier)) (figure_eight_setfamilies_triples W)

{` The two monodromies of a family over S¹ ∨ S¹. `}
def figure_eight_monodromy1 (W : FigureEightSignature) (R : W .carrier → Type) : Equiv (R (W .base)) (R (W .base))
  ≔ transport_equiv (R (W .base)) (R (W .base)) (refl R (W .loop1))

def figure_eight_monodromy2 (W : FigureEightSignature) (R : W .carrier → Type) : Equiv (R (W .base)) (R (W .base))
  ≔ transport_equiv (R (W .base)) (R (W .base)) (refl R (W .loop2))

{` Words give paths in the total space: (base, x) = (base, ⟦ℓ⟧x). `}
def figure_eight_loop_power_transport (W : FigureEightSignature) (R : W .carrier → Type) (l : Id (W .carrier) (W .base) (W .base))
  (x : R (W .base)) (n : Int)
  : Id (R (W .base)) (transport (W .carrier) R (W .base) (W .base) (loop_power (W .carrier) (W .base) l n) x)
      (permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) n x)
  ≔ transport_loop_power (W .carrier) R (W .base) l
      (m ↦ permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) m x)
      (m ↦ inverse (R (W .base))
        (permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) (int_succ m) x)
        (transport_equiv (R (W .base)) (R (W .base)) (refl R l) .map
          (permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) m x))
        (permutation_power_succ (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) m x)) n

def figure_eight_power_path (W : FigureEightSignature) (R : W .carrier → Type) (l : Id (W .carrier) (W .base) (W .base))
  (x : R (W .base)) (n : Int)
  : Id (Σ (W .carrier) R) (W .base, x)
      (W .base, permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) n x)
  ≔ let p ≔ loop_power (W .carrier) (W .base) l n in
    (p, pathover_of_eq (W .carrier) R (W .base) (W .base) p x
      (permutation_power (R (W .base)) (transport_equiv (R (W .base)) (R (W .base)) (refl R l)) n x)
      (figure_eight_loop_power_transport W R l x n))

def figure_eight_word_path (W : FigureEightSignature) (R : W .carrier → Type) (l : List (Sum Int Int)) (x : R (W .base))
  : Id (Σ (W .carrier) R) (W .base, x)
      (W .base, bicycle_meaning_map (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) l x)
  ≔ let T ≔ Σ (W .carrier) R in
    let M ≔ bicycle_meaning_map (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) in
    match l [
    | nil. ↦ refl ((W .base, x) : T)
    | cons. (inl. n) k ↦ concat T (W .base, x) (W .base, M k x)
        (W .base, permutation_power (R (W .base)) (figure_eight_monodromy1 W R) n (M k x))
        (figure_eight_word_path W R k x) (figure_eight_power_path W R (W .loop1) (M k x) n)
    | cons. (inr. n) k ↦ concat T (W .base, x) (W .base, M k x)
        (W .base, permutation_power (R (W .base)) (figure_eight_monodromy2 W R) n (M k x))
        (figure_eight_word_path W R k x) (figure_eight_power_path W R (W .loop2) (M k x) n) ]

{` Paths in the total space give words ("encode"): the predicate "word-
   connected to r" on the fibers is invariant under both monodromies, so it
   extends to a family over the total space by induction. `}
def figure_eight_word_predicate_base (W : FigureEightSignature) (R : W .carrier → Type) (r : R (W .base))
  (s : R (W .base)) : PropTypes
  ≔ (Mere (BicycleWordFrom (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) r s),
      mere_isprop (BicycleWordFrom (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) r s))

def figure_eight_word_step (X : Type) (a b : Equiv X X) (r s : X) (letter : Sum Int Int)
  (w : BicycleWordFrom X a b r s) : BicycleWordFrom X a b r (bicycle_meaning_map X a b (cons. letter nil.) s)
  ≔ (cons. letter (w .fst),
      concat X (bicycle_meaning_map X a b (cons. letter nil.) s)
        (bicycle_meaning_map X a b (cons. letter nil.) (bicycle_meaning_map X a b (w .fst) r))
        (bicycle_meaning_map X a b (cons. letter (w .fst)) r)
        (refl (bicycle_meaning_map X a b (cons. letter nil.)) (w .snd))
        (inverse X (bicycle_meaning_map X a b (cons. letter (w .fst)) r)
          (bicycle_meaning_map X a b (cons. letter nil.) (bicycle_meaning_map X a b (w .fst) r))
          (bicycle_meaning_append X a b (cons. letter nil.) (w .fst) r)))

def figure_eight_word_unstep (X : Type) (a b : Equiv X X) (r s : X) (e : Equiv X X)
  (letter : Sum Int Int) (back : Sum Int Int)
  (h1 : (y : X) → Id X (bicycle_meaning_map X a b (cons. back nil.) (e .map y)) y)
  (w : BicycleWordFrom X a b r (e .map s)) : BicycleWordFrom X a b r s
  ≔ (cons. back (w .fst), calc
      s = bicycle_meaning_map X a b (cons. back nil.) (e .map s)
        by inverse X (bicycle_meaning_map X a b (cons. back nil.) (e .map s)) s (h1 s)
      = bicycle_meaning_map X a b (cons. back nil.) (bicycle_meaning_map X a b (w .fst) r)
        by refl (bicycle_meaning_map X a b (cons. back nil.)) (w .snd)
      = bicycle_meaning_map X a b (cons. back (w .fst)) r
        by inverse X (bicycle_meaning_map X a b (cons. back (w .fst)) r)
          (bicycle_meaning_map X a b (cons. back nil.) (bicycle_meaning_map X a b (w .fst) r))
          (bicycle_meaning_append X a b (cons. back nil.) (w .fst) r) ∎)

def figure_eight_predicate_invariant (X : Type) (a b : Equiv X X) (r : X) (e : Equiv X X) (letter back : Sum Int Int)
  (h0 : (y : X) → Id X (bicycle_meaning_map X a b (cons. letter nil.) y) (e .map y))
  (h1 : (y : X) → Id X (bicycle_meaning_map X a b (cons. back nil.) (e .map y)) y)
  (s0 s1 : X) (q : Id X (e .map s0) s1)
  : Id PropTypes (Mere (BicycleWordFrom X a b r s0), mere_isprop (BicycleWordFrom X a b r s0))
      (Mere (BicycleWordFrom X a b r s1), mere_isprop (BicycleWordFrom X a b r s1))
  ≔ concat PropTypes (Mere (BicycleWordFrom X a b r s0), mere_isprop (BicycleWordFrom X a b r s0))
      (Mere (BicycleWordFrom X a b r (e .map s0)), mere_isprop (BicycleWordFrom X a b r (e .map s0)))
      (Mere (BicycleWordFrom X a b r s1), mere_isprop (BicycleWordFrom X a b r s1))
      (proposition_extensionality
        (Mere (BicycleWordFrom X a b r s0), mere_isprop (BicycleWordFrom X a b r s0))
        (Mere (BicycleWordFrom X a b r (e .map s0)), mere_isprop (BicycleWordFrom X a b r (e .map s0)))
        (mere_rec (BicycleWordFrom X a b r s0) (Mere (BicycleWordFrom X a b r (e .map s0))) (mere_isprop (BicycleWordFrom X a b r (e .map s0)))
          (w ↦ mere (BicycleWordFrom X a b r (e .map s0))
            (let w' ≔ figure_eight_word_step X a b r s0 letter w in
             (w' .fst, concat X (e .map s0) (bicycle_meaning_map X a b (cons. letter nil.) s0) (bicycle_meaning_map X a b (w' .fst) r)
               (inverse X (bicycle_meaning_map X a b (cons. letter nil.) s0) (e .map s0) (h0 s0)) (w' .snd)))))
        (mere_rec (BicycleWordFrom X a b r (e .map s0)) (Mere (BicycleWordFrom X a b r s0)) (mere_isprop (BicycleWordFrom X a b r s0))
          (w ↦ mere (BicycleWordFrom X a b r s0) (figure_eight_word_unstep X a b r s0 e letter back h1 w))))
      (refl ((s ↦ (Mere (BicycleWordFrom X a b r s), mere_isprop (BicycleWordFrom X a b r s))) : X → PropTypes) q)

def figure_eight_word_predicate_data (W : FigureEightSignature) (R : W .carrier → Type) (r : R (W .base))
  : FigureEightBoundary (W .carrier) (W .base) (W .loop1) (W .loop2) (x ↦ R x → PropTypes)
  ≔ let X ≔ R (W .base) in
    let a ≔ figure_eight_monodromy1 W R in let b ≔ figure_eight_monodromy2 W R in
    (figure_eight_word_predicate_base W R r,
     (s ⤇ figure_eight_predicate_invariant X a b r a (inl. (pos. (suc. zero.))) (inl. (neg. zero.))
            (y ↦ refl (a .map y)) (y ↦ equiv_retraction X X a y) s.0 s.1
            (pathover_transport_equiv (W .carrier) R (W .base) (W .base) (W .loop1) s.0 s.1 .map s.2),
      s ⤇ figure_eight_predicate_invariant X a b r b (inr. (pos. (suc. zero.))) (inr. (neg. zero.))
            (y ↦ refl (b .map y)) (y ↦ equiv_retraction X X b y) s.0 s.1
            (pathover_transport_equiv (W .carrier) R (W .base) (W .base) (W .loop2) s.0 s.1 .map s.2)))

def figure_eight_word_predicate (W : FigureEightSignature) (R : W .carrier → Type) (r : R (W .base))
  : (x : W .carrier) → R x → PropTypes
  ≔ W .induction (x ↦ R x → PropTypes) (figure_eight_word_predicate_data W R r) .fst

def figure_eight_word_predicate_beta (W : FigureEightSignature) (R : W .carrier → Type) (r : R (W .base))
  : Id (R (W .base) → PropTypes) (figure_eight_word_predicate W R r (W .base)) (figure_eight_word_predicate_base W R r)
  ≔ W .induction (x ↦ R x → PropTypes) (figure_eight_word_predicate_data W R r) .snd .fst

def figure_eight_total_path_word (W : FigureEightSignature) (R : W .carrier → Type) (r s : R (W .base))
  (p : Id (Σ (W .carrier) R) (W .base, r) (W .base, s))
  : Mere (BicycleWordFrom (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) r s)
  ≔ let Q ≔ figure_eight_word_predicate W R r in
    let beta ≔ figure_eight_word_predicate_beta W R r in
    let Pt ≔ (u ↦ Q (u .fst) (u .snd) .fst) : Σ (W .carrier) R → Type in
    let at_r : Q (W .base) r .fst
      ≔ transport PropTypes (P ↦ P .fst) (figure_eight_word_predicate_base W R r r) (Q (W .base) r)
          (inverse PropTypes (Q (W .base) r) (figure_eight_word_predicate_base W R r r) (beta (refl r)))
          (mere (BicycleWordFrom (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R) r r) (nil., refl r)) in
    transport PropTypes (P ↦ P .fst) (Q (W .base) s) (figure_eight_word_predicate_base W R r s) (beta (refl s))
      (transport (Σ (W .carrier) R) Pt (W .base, r) (W .base, s) p at_r)

{` The total space of a family R over S¹ ∨ S¹ is connected iff (R(base), the
   two monodromies) satisfies the connectivity condition of def:bicycle. `}
def figure_eight_total_connected (W : FigureEightSignature) (R : W .carrier → Type)
  : Equiv (Connected (Σ (W .carrier) R))
      (BicycleConnected (R (W .base)) (figure_eight_monodromy1 W R) (figure_eight_monodromy2 W R))
  ≔ let X ≔ R (W .base) in
    let a ≔ figure_eight_monodromy1 W R in let b ≔ figure_eight_monodromy2 W R in
    let T ≔ Σ (W .carrier) R in
    let to_base : (u : T) → Mere (Σ X (x ↦ Id T u (W .base, x)))
      ≔ u ↦ mere_rec (Id (W .carrier) (u .fst) (W .base)) (Mere (Σ X (x ↦ Id T u (W .base, x))))
          (mere_isprop (Σ X (x ↦ Id T u (W .base, x))))
          (q ↦ mere (Σ X (x ↦ Id T u (W .base, x)))
            (transport (W .carrier) R (u .fst) (W .base) q (u .snd), (q, refl R q .liftr (u .snd))))
          (figure_eight_connected_to_base W (u .fst)) in
    iff_equiv (Connected T) (BicycleConnected X a b) (connected_isprop T) (bicycle_connected_prop X a b)
      (h ↦ (mere_rec T (Mere X) (mere_isprop X)
              (u ↦ mere_rec (Σ X (x ↦ Id T u (W .base, x))) (Mere X) (mere_isprop X) (v ↦ mere X (v .fst)) (to_base u)) (h .fst),
            x x' ↦ mere_rec (Id T (W .base, x) (W .base, x')) (Mere (BicycleWordFrom X a b x x'))
              (mere_isprop (BicycleWordFrom X a b x x'))
              (figure_eight_total_path_word W R x x') (h .snd (W .base, x) (W .base, x'))))
      (c ↦ (mere_rec X (Mere T) (mere_isprop T) (x ↦ mere T (W .base, x)) (c .fst),
            u v ↦ mere_rec (Σ X (x ↦ Id T u (W .base, x))) (Mere (Id T u v)) (mere_isprop (Id T u v))
              (su ↦ mere_rec (Σ X (x ↦ Id T v (W .base, x))) (Mere (Id T u v)) (mere_isprop (Id T u v))
                (sv ↦ mere_rec (BicycleWordFrom X a b (su .fst) (sv .fst)) (Mere (Id T u v)) (mere_isprop (Id T u v))
                  (w ↦ mere (Id T u v)
                    (calc u = (W .base, su .fst) by su .snd
                      = (W .base, bicycle_meaning_map X a b (w .fst) (su .fst)) by figure_eight_word_path W R (w .fst) (su .fst)
                      = (W .base, sv .fst)
                        by (refl (W .base), inverse X (sv .fst) (bicycle_meaning_map X a b (w .fst) (su .fst)) (w .snd))
                      = v by inverse T v (W .base, sv .fst) (sv .snd) ∎))
                  (c .snd (su .fst) (sv .fst)))
                (to_base v))
              (to_base u)))

{` Connected coverings over S¹ ∨ S¹ are bicycles. `}
def figure_eight_covering_connected (W : FigureEightSignature) (c : Coverings (W .carrier))
  : Equiv (Connected (c .fst)) (bicycle_triple_connected (figure_eight_coverings_triples W .map c))
  ≔ compose_equiv (Connected (c .fst))
      (Connected (Σ (W .carrier) (x ↦ BookFiber (c .fst) (W .carrier) (c .snd .fst) x)))
      (bicycle_triple_connected (figure_eight_coverings_triples W .map c))
      (connected_equiv (c .fst) (Σ (W .carrier) (x ↦ BookFiber (c .fst) (W .carrier) (c .snd .fst) x))
        (canonical_inverse_equiv (Σ (W .carrier) (x ↦ BookFiber (c .fst) (W .carrier) (c .snd .fst) x))
          (c .fst) (sum_of_fibers_equiv (c .fst) (W .carrier) (c .snd .fst))))
      (figure_eight_total_connected W (x ↦ BookFiber (c .fst) (W .carrier) (c .snd .fst) x))

def bicycles_triples_equiv : Equiv (Σ BicycleDataTriples bicycle_triple_connected) Bicycles
  ≔ quasi_inverse_equiv (Σ BicycleDataTriples bicycle_triple_connected) Bicycles
      (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd, t .snd))))
      (B ↦ ((B .fst, (B .snd .fst, B .snd .snd .fst)), B .snd .snd .snd))
      (t ↦ refl t) (B ↦ refl B)

def figure_eight_connected_coverings_bicycles (W : FigureEightSignature)
  : BookEquiv (ConnectedCoverings (W .carrier)) Bicycles
  ≔ book_equivalence (ConnectedCoverings (W .carrier)) Bicycles
      (compose_equiv (ConnectedCoverings (W .carrier)) (Σ BicycleDataTriples bicycle_triple_connected) Bicycles
        (propositional_subtype_equiv (Coverings (W .carrier)) BicycleDataTriples
          (c ↦ Connected (c .fst)) bicycle_triple_connected (c ↦ connected_isprop (c .fst))
          (t ↦ bicycle_connected_prop (t .fst .fst) (t .snd .fst) (t .snd .snd))
          (figure_eight_coverings_triples W) (figure_eight_covering_connected W))
        bicycles_triples_equiv)
