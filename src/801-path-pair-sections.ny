export "150-paths-over-and-pairs"

{` Chapter 8 (congp.tex), sec:Semidirect-products, lines 199–289:
   identifications between pairs (x, f(x)) of Σ_{x:X} Y(x) for a section
   f : Π_{x:X} Y(x), for arbitrary X, Y and f as in the book (module 802
   specialises to G ⋉ H with f(t) ≔ sh_{H(t)}).

   Composition: the book's e' · e (first e, then e') is concat e e'; so
   the book's p' · p is concat p p' and (q'^p) · q is concat q (q'^p).
   The book defines its maps by induction on paths with definitional
   computation rules at refl; with Narya's J these rules are the proved
   identifications section_pathover_loop_refl and section_loop_action_refl
   (typal β-rule Jβ). `}

{` Proof of lem:pathpairsection, the fiberwise step: for p : x = x', the
   paths over p from f(x) to f(x') are equivalent to the loops f(x) = f(x),
   by induction on p with the identity equivalence at p ≡ refl x (where
   the two sides are equal by definition). `}
def section_pathover_loop_equiv (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : Equiv (Id Y p (f x) (f x')) (Id (Y x) (f x) (f x))
  ≔ J X x (x' p ↦ Equiv (Id Y p (f x) (f x')) (Id (Y x) (f x) (f x)))
      (identity_equiv (Id (Y x) (f x) (f x))) x' p

def section_pathover_loop (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  (r : Id Y p (f x) (f x')) : Id (Y x) (f x) (f x)
  ≔ section_pathover_loop_equiv X Y f x x' p .map r

{` At p ≡ refl x the fiberwise map is the identity (the book's definitional
   rule, here by Jβ). `}
def section_pathover_loop_refl (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (r : Id (Y x) (f x) (f x))
  : Id (Id (Y x) (f x) (f x)) (section_pathover_loop X Y f x x (refl x) r) r
  ≔ inverse (Id (Y x) (f x) (f x)) r (section_pathover_loop X Y f x x (refl x) r)
      (Jβ X x (x' p ↦ Equiv (Id Y p (f x) (f x')) (Id (Y x) (f x) (f x)))
        (identity_equiv (Id (Y x) (f x) (f x))) .map (refl r))

{` The dependent path apd_f(p) corresponds to the trivial loop. `}
def section_pathover_loop_apd (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : Id (Id (Y x) (f x) (f x)) (section_pathover_loop X Y f x x' p (refl f p)) (refl (f x))
  ≔ J X x (x' p ↦ Id (Id (Y x) (f x) (f x)) (section_pathover_loop X Y f x x' p (refl f p)) (refl (f x)))
      (section_pathover_loop_refl X Y f x (refl (f x))) x' p

{` lem:pathpairsection. ((x, f(x)) = (x', f(x'))) ≃ (x = x') × (f(x) = f(x)),
   as in the book's proof: lem:isEq-pair= (an identification of pairs is a
   pair (e .fst, e .snd) of a path and a path over it) followed by the
   fiberwise equivalence above (lem:fiberwise). The printed right-hand side
   (loops at f(x)) is correct as stated. `}
def path_pair_section_map (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (e : Id (Σ X Y) (x, f x) (x', f x')) : Product (Id X x x') (Id (Y x) (f x) (f x))
  ≔ (e .fst, section_pathover_loop X Y f x x' (e .fst) (e .snd))

def path_pair_section_inverse (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (pq : Product (Id X x x') (Id (Y x) (f x) (f x))) : Id (Σ X Y) (x, f x) (x', f x')
  ≔ (pq .fst, equiv_inverse_map (Id Y (pq .fst) (f x) (f x')) (Id (Y x) (f x) (f x))
       (section_pathover_loop_equiv X Y f x x' (pq .fst)) (pq .snd))

def path_pair_section_equiv (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  : Equiv (Id (Σ X Y) (x, f x) (x', f x')) (Product (Id X x x') (Id (Y x) (f x) (f x)))
  ≔ quasi_inverse_equiv (Id (Σ X Y) (x, f x) (x', f x')) (Product (Id X x x') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x') (path_pair_section_inverse X Y f x x')
      (e ↦ (refl (e .fst),
        equiv_retraction (Id Y (e .fst) (f x) (f x')) (Id (Y x) (f x) (f x))
          (section_pathover_loop_equiv X Y f x x' (e .fst)) (e .snd)))
      (pq ↦ (refl (pq .fst),
        equiv_counit (Id Y (pq .fst) (f x) (f x')) (Id (Y x) (f x) (f x))
          (section_pathover_loop_equiv X Y f x x' (pq .fst)) (pq .snd)))

def path_pair_section_book_equiv (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  : BookEquiv (Id (Σ X Y) (x, f x) (x', f x')) (Product (Id X x x') (Id (Y x) (f x) (f x)))
  ≔ book_equivalence (Id (Σ X Y) (x, f x) (x', f x')) (Product (Id X x x') (Id (Y x) (f x) (f x)))
      (path_pair_section_equiv X Y f x x')

{` def:pathsectionaction. For p : x = x', q' ↦ q'^p : (f(x') = f(x')) →
   (f(x) = f(x)), by induction on p with q'^{refl x} ≔ q' (here Jβ). `}
def section_loop_action (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  (q' : Id (Y x') (f x') (f x')) : Id (Y x) (f x) (f x)
  ≔ J X x (x' p ↦ Id (Y x') (f x') (f x') → Id (Y x) (f x) (f x)) (q ↦ q) x' p q'

def section_loop_action_refl (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (q' : Id (Y x) (f x) (f x))
  : Id (Id (Y x) (f x) (f x)) (section_loop_action X Y f x x (refl x) q') q'
  ≔ inverse (Id (Y x) (f x) (f x)) q' (section_loop_action X Y f x x (refl x) q')
      (Jβ X x (x' p ↦ Id (Y x') (f x') (f x') → Id (Y x) (f x) (f x)) (q ↦ q) (refl q'))

{` Lines 232–234: q'^p is "the transport of loops in Y(x) along paths in
   X": it is the transport of q' back along p in the family of loops
   z ↦ (f(z) = f(z)). `}
def section_loop_action_transport_base (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (q' : Id (Y x) (f x) (f x))
  : Id (Id (Y x) (f x) (f x)) (section_loop_action X Y f x x (refl x) q')
      (transport X (z ↦ Id (Y z) (f z) (f z)) x x (inverse X x x (refl x)) q')
  ≔ calc
      section_loop_action X Y f x x (refl x) q' = q' by section_loop_action_refl X Y f x q'
      = transport X (z ↦ Id (Y z) (f z) (f z)) x x (refl x) q'
        by inverse (Id (Y x) (f x) (f x)) (transport X (z ↦ Id (Y z) (f z) (f z)) x x (refl x) q') q'
             (transport_refl X (z ↦ Id (Y z) (f z) (f z)) x q')
      = transport X (z ↦ Id (Y z) (f z) (f z)) x x (inverse X x x (refl x)) q'
        by refl ((r ↦ transport X (z ↦ Id (Y z) (f z) (f z)) x x r q') : Id X x x → Id (Y x) (f x) (f x))
             (inverse (Id X x x) (inverse X x x (refl x)) (refl x) (inverse_refl X x)) ∎

def section_loop_action_transport (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  (q' : Id (Y x') (f x') (f x'))
  : Id (Id (Y x) (f x) (f x)) (section_loop_action X Y f x x' p q')
      (transport X (z ↦ Id (Y z) (f z) (f z)) x' x (inverse X x x' p) q')
  ≔ J X x (x' p ↦ (q' : Id (Y x') (f x') (f x')) → Id (Id (Y x) (f x) (f x)) (section_loop_action X Y f x x' p q')
        (transport X (z ↦ Id (Y z) (f z) (f z)) x' x (inverse X x x' p) q'))
      (q' ↦ section_loop_action_transport_base X Y f x q') x' p q'

{` def:pathsectionactionassoc. (q^{p'})^p = q^{p'·p} for p : x = x',
   p' : x' = x'', q : f(x'') = f(x''), where p' · p = concat p p'. By
   induction on p' (the book also inducts on p, which is not needed). `}
def section_loop_action_assoc_base (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (p : Id X x x') (q : Id (Y x') (f x') (f x'))
  : Id (Id (Y x) (f x) (f x))
      (section_loop_action X Y f x x' p (section_loop_action X Y f x' x' (refl x') q))
      (section_loop_action X Y f x x' (concat X x x' x' p (refl x')) q)
  ≔ concat (Id (Y x) (f x) (f x))
      (section_loop_action X Y f x x' p (section_loop_action X Y f x' x' (refl x') q))
      (section_loop_action X Y f x x' p q)
      (section_loop_action X Y f x x' (concat X x x' x' p (refl x')) q)
      (refl (section_loop_action X Y f x x' p) (section_loop_action_refl X Y f x' q))
      (refl ((r ↦ section_loop_action X Y f x x' r q) : Id X x x' → Id (Y x) (f x) (f x))
        (inverse (Id X x x') (concat X x x' x' p (refl x')) p (concat_p1 X x x' p)))

def section_loop_action_assoc (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (p : Id X x x') (x'' : X) (p' : Id X x' x'') (q : Id (Y x'') (f x'') (f x''))
  : Id (Id (Y x) (f x) (f x))
      (section_loop_action X Y f x x' p (section_loop_action X Y f x' x'' p' q))
      (section_loop_action X Y f x x'' (concat X x x' x'' p p') q)
  ≔ J X x' (x'' p' ↦ (q : Id (Y x'') (f x'') (f x'')) → Id (Id (Y x) (f x) (f x))
        (section_loop_action X Y f x x' p (section_loop_action X Y f x' x'' p' q))
        (section_loop_action X Y f x x'' (concat X x x' x'' p p') q))
      (q ↦ section_loop_action_assoc_base X Y f x x' p q) x'' p' q

{` For a constant family and a constant section the action is trivial. `}
def section_loop_action_constant (X B : Type) (b : B) (x x' : X) (p : Id X x x') (q' : Id B b b)
  : Id (Id B b b) (section_loop_action X (_ ↦ B) (_ ↦ b) x x' p q') q'
  ≔ J X x (x' p ↦ (q' : Id B b b) → Id (Id B b b) (section_loop_action X (_ ↦ B) (_ ↦ b) x x' p q') q')
      (q' ↦ section_loop_action_refl X (_ ↦ B) (_ ↦ b) x q') x' p q'

{` lem:pathpairsectionmult. The pair of a composite: (p, q) and (p', q')
   compose to (p' · p, (q'^p) · q), in concatenation order
   (concat p p', concat q (q'^p)). First the combination of pairs. `}
def path_pair_section_combine (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X)
  (a : Product (Id X x x') (Id (Y x) (f x) (f x))) (a' : Product (Id X x' x'') (Id (Y x') (f x') (f x')))
  : Product (Id X x x'') (Id (Y x) (f x) (f x))
  ≔ (concat X x x' x'' (a .fst) (a' .fst),
     concat (Y x) (f x) (f x) (f x) (a .snd) (section_loop_action X Y f x x' (a .fst) (a' .snd)))

def path_pair_section_concat_type (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X)
  (p : Id X x x') (r : Id Y p (f x) (f x')) (p' : Id X x' x'') (r' : Id Y p' (f x') (f x'')) : Type
  ≔ Id (Product (Id X x x'') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x'' (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') (p, r) (p', r')))
      (path_pair_section_combine X Y f x x' x''
        (p, section_pathover_loop X Y f x x' p r) (p', section_pathover_loop X Y f x' x'' p' r'))

{` The case p ≡ p' ≡ refl x (book: "apap g refl q' · apap g refl q =
   apap g refl (q' · q)", def:applfun2comp and lem:apcomp). `}
def path_pair_section_concat_snd (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (r r' : Id (Y x) (f x) (f x))
  : Id (Id (Y x) (f x) (f x))
      (section_pathover_loop X Y f x x (refl x) (concat (Y x) (f x) (f x) (f x) r r'))
      (concat (Y x) (f x) (f x) (f x) (section_pathover_loop X Y f x x (refl x) r)
        (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x (refl x) r')))
  ≔ concat (Id (Y x) (f x) (f x))
      (section_pathover_loop X Y f x x (refl x) (concat (Y x) (f x) (f x) (f x) r r'))
      (concat (Y x) (f x) (f x) (f x) r r')
      (concat (Y x) (f x) (f x) (f x) (section_pathover_loop X Y f x x (refl x) r)
        (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x (refl x) r')))
      (section_pathover_loop_refl X Y f x (concat (Y x) (f x) (f x) (f x) r r'))
      (refl (concat (Y x) (f x) (f x) (f x))
        (inverse (Id (Y x) (f x) (f x)) (section_pathover_loop X Y f x x (refl x) r) r
          (section_pathover_loop_refl X Y f x r))
        (inverse (Id (Y x) (f x) (f x))
          (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x (refl x) r')) r'
          (concat (Id (Y x) (f x) (f x))
            (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x (refl x) r'))
            (section_pathover_loop X Y f x x (refl x) r') r'
            (section_loop_action_refl X Y f x (section_pathover_loop X Y f x x (refl x) r'))
            (section_pathover_loop_refl X Y f x r'))))

def path_pair_section_concat_base (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (r r' : Id (Y x) (f x) (f x))
  : path_pair_section_concat_type X Y f x x x (refl x) r (refl x) r'
  ≔ concat (Product (Id X x x) (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x (concat (Σ X Y) (x, f x) (x, f x) (x, f x) (refl x, r) (refl x, r')))
      (path_pair_section_map X Y f x x (refl x, concat (Y x) (f x) (f x) (f x) r r'))
      (path_pair_section_combine X Y f x x x
        (refl x, section_pathover_loop X Y f x x (refl x) r) (refl x, section_pathover_loop X Y f x x (refl x) r'))
      (refl (path_pair_section_map X Y f x x)
        (inverse (Id (Σ X Y) (x, f x) (x, f x))
          (refl ((y ↦ (x, y)) : Y x → Σ X Y) (concat (Y x) (f x) (f x) (f x) r r'))
          (concat (Σ X Y) (x, f x) (x, f x) (x, f x) (refl x, r) (refl x, r'))
          (map_path_concat (Y x) (Σ X Y) (y ↦ (x, y)) (f x) (f x) (f x) r r')))
      (inverse (Id X x x) (concat X x x x (refl x) (refl x)) (refl x) (concat_p1 X x x (refl x)),
       path_pair_section_concat_snd X Y f x r r')

def path_pair_section_concat_left (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : (r : Id Y p (f x) (f x')) (r' : Id (Y x') (f x') (f x'))
      → path_pair_section_concat_type X Y f x x' x' p r (refl x') r'
  ≔ J X x (x' p ↦ (r : Id Y p (f x) (f x')) (r' : Id (Y x') (f x') (f x'))
        → path_pair_section_concat_type X Y f x x' x' p r (refl x') r')
      (r r' ↦ path_pair_section_concat_base X Y f x r r') x' p

def path_pair_section_concat_general (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (p : Id X x x') (r : Id Y p (f x) (f x')) (x'' : X) (p' : Id X x' x'') (r' : Id Y p' (f x') (f x''))
  : path_pair_section_concat_type X Y f x x' x'' p r p' r'
  ≔ J X x' (x'' p' ↦ (r' : Id Y p' (f x') (f x'')) → path_pair_section_concat_type X Y f x x' x'' p r p' r')
      (r' ↦ path_pair_section_concat_left X Y f x x' p r r') x'' p' r'

{` lem:pathpairsectionmult, unconditional form: the pair of e' · e is the
   combination of the pairs of e and e'. `}
def path_pair_section_concat (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X)
  (e : Id (Σ X Y) (x, f x) (x', f x')) (e' : Id (Σ X Y) (x', f x') (x'', f x''))
  : Id (Product (Id X x x'') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x'' (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') e e'))
      (path_pair_section_combine X Y f x x' x'' (path_pair_section_map X Y f x x' e)
        (path_pair_section_map X Y f x' x'' e'))
  ≔ path_pair_section_concat_general X Y f x x' (e .fst) (e .snd) x'' (e' .fst) (e' .snd)

{` lem:pathpairsectionmult as printed: if e corresponds to (p, q) and e' to
   (p', q'), then e' · e corresponds to (p' · p, (q'^p) · q). `}
def path_pair_section_mult (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X)
  (e : Id (Σ X Y) (x, f x) (x', f x')) (e' : Id (Σ X Y) (x', f x') (x'', f x''))
  (p : Id X x x') (q : Id (Y x) (f x) (f x)) (p' : Id X x' x'') (q' : Id (Y x') (f x') (f x'))
  (he : Id (Product (Id X x x') (Id (Y x) (f x) (f x))) (path_pair_section_map X Y f x x' e) (p, q))
  (he' : Id (Product (Id X x' x'') (Id (Y x') (f x') (f x'))) (path_pair_section_map X Y f x' x'' e') (p', q'))
  : Id (Product (Id X x x'') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x'' (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') e e'))
      (concat X x x' x'' p p', concat (Y x) (f x) (f x) (f x) q (section_loop_action X Y f x x' p q'))
  ≔ concat (Product (Id X x x'') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x'' (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') e e'))
      (path_pair_section_combine X Y f x x' x'' (path_pair_section_map X Y f x x' e)
        (path_pair_section_map X Y f x' x'' e'))
      (path_pair_section_combine X Y f x x' x'' (p, q) (p', q'))
      (path_pair_section_concat X Y f x x' x'' e e')
      (refl (path_pair_section_combine X Y f x x' x'') he he')

{` Every identification (x, f(x)) = (x', f(x')) splits: the pair (p, q)
   corresponds to (refl x, q) followed by (p, apd_f(p)). `}
def path_pair_section_split (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (p : Id X x x') (q : Id (Y x) (f x) (f x))
  : Id (Product (Id X x x') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x' (concat (Σ X Y) (x, f x) (x, f x) (x', f x') (refl x, q) (p, refl f p)))
      (p, q)
  ≔ concat (Product (Id X x x') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x' (concat (Σ X Y) (x, f x) (x, f x) (x', f x') (refl x, q) (p, refl f p)))
      (path_pair_section_combine X Y f x x x' (refl x, section_pathover_loop X Y f x x (refl x) q)
        (p, section_pathover_loop X Y f x x' p (refl f p)))
      (p, q)
      (path_pair_section_concat X Y f x x x' (refl x, q) (p, refl f p))
      (concat_1p X x x' p,
       concat (Id (Y x) (f x) (f x))
         (concat (Y x) (f x) (f x) (f x) (section_pathover_loop X Y f x x (refl x) q)
           (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x' p (refl f p))))
         (concat (Y x) (f x) (f x) (f x) q (refl (f x)))
         q
         (refl (concat (Y x) (f x) (f x) (f x)) (section_pathover_loop_refl X Y f x q)
           (concat (Id (Y x) (f x) (f x))
             (section_loop_action X Y f x x (refl x) (section_pathover_loop X Y f x x' p (refl f p)))
             (section_loop_action X Y f x x (refl x) (refl (f x)))
             (refl (f x))
             (refl (section_loop_action X Y f x x (refl x)) (section_pathover_loop_apd X Y f x x' p))
             (section_loop_action_refl X Y f x (refl (f x)))))
         (concat_p1 (Y x) (f x) (f x) q))
