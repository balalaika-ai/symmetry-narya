export "230-higher-images"

{` xca:trunc-sum-type+fam for every n >= -1:
   ||Σ_{x:X} Y(x)||_n ≃ ||Σ_{x:X} ||Y(x)||_n||_n, sending |(x,y)| to |(x,|y|)|. `}
def trunc_sum_to (k : Nat) (X : Type) (Y : X → Type)
  : Trunc k (Σ X Y) → Trunc k (Σ X (x ↦ Trunc k (Y x)))
  ≔ trunc_extend k (Σ X Y) (truncation k (Σ X Y)) (Trunc k (Σ X (x ↦ Trunc k (Y x))))
      (trunc_level k (Σ X (x ↦ Trunc k (Y x))))
      (w ↦ trunc_unit k (Σ X (x ↦ Trunc k (Y x))) (w .fst, trunc_unit k (Y (w .fst)) (w .snd)))

def trunc_sum_inner (k : Nat) (X : Type) (Y : X → Type) (x : X) : Trunc k (Y x) → Trunc k (Σ X Y)
  ≔ trunc_extend k (Y x) (truncation k (Y x)) (Trunc k (Σ X Y)) (trunc_level k (Σ X Y))
      (y ↦ trunc_unit k (Σ X Y) (x, y))

def trunc_sum_from (k : Nat) (X : Type) (Y : X → Type)
  : Trunc k (Σ X (x ↦ Trunc k (Y x))) → Trunc k (Σ X Y)
  ≔ trunc_extend k (Σ X (x ↦ Trunc k (Y x))) (truncation k (Σ X (x ↦ Trunc k (Y x)))) (Trunc k (Σ X Y))
      (trunc_level k (Σ X Y)) (w ↦ trunc_sum_inner k X Y (w .fst) (w .snd))

def trunc_sum_retraction (k : Nat) (X : Type) (Y : X → Type) (z : Trunc k (Σ X Y))
  : Id (Trunc k (Σ X Y)) (trunc_sum_from k X Y (trunc_sum_to k X Y z)) z
  ≔ let S ≔ Σ X Y in let T ≔ Σ X (x ↦ Trunc k (Y x)) in
    trunc_ind k S (truncation k S) (v ↦ Id (Trunc k S) (trunc_sum_from k X Y (trunc_sum_to k X Y v)) v)
      (v ↦ hlevel_raise k (Id (Trunc k S) (trunc_sum_from k X Y (trunc_sum_to k X Y v)) v)
        (trunc_level k S (trunc_sum_from k X Y (trunc_sum_to k X Y v)) v))
      (w ↦ calc
        trunc_sum_from k X Y (trunc_sum_to k X Y (trunc_unit k S w))
        = trunc_sum_from k X Y (trunc_unit k T (w .fst, trunc_unit k (Y (w .fst)) (w .snd)))
          by refl (trunc_sum_from k X Y) (inverse (Trunc k T)
            (trunc_unit k T (w .fst, trunc_unit k (Y (w .fst)) (w .snd))) (trunc_sum_to k X Y (trunc_unit k S w))
            (trunc_extend_beta k S (truncation k S) (Trunc k T) (trunc_level k T)
              (u ↦ trunc_unit k T (u .fst, trunc_unit k (Y (u .fst)) (u .snd))) w))
        = trunc_sum_inner k X Y (w .fst) (trunc_unit k (Y (w .fst)) (w .snd))
          by inverse (Trunc k S) (trunc_sum_inner k X Y (w .fst) (trunc_unit k (Y (w .fst)) (w .snd)))
            (trunc_sum_from k X Y (trunc_unit k T (w .fst, trunc_unit k (Y (w .fst)) (w .snd))))
            (trunc_extend_beta k T (truncation k T) (Trunc k S) (trunc_level k S)
              (u ↦ trunc_sum_inner k X Y (u .fst) (u .snd)) (w .fst, trunc_unit k (Y (w .fst)) (w .snd)))
        = trunc_unit k S w
          by inverse (Trunc k S) (trunc_unit k S w) (trunc_sum_inner k X Y (w .fst) (trunc_unit k (Y (w .fst)) (w .snd)))
            (trunc_extend_beta k (Y (w .fst)) (truncation k (Y (w .fst))) (Trunc k S) (trunc_level k S)
              (y ↦ trunc_unit k S (w .fst, y)) (w .snd)) ∎) z

def trunc_sum_section_inner (k : Nat) (X : Type) (Y : X → Type) (x : X) (t : Trunc k (Y x))
  : Id (Trunc k (Σ X (x ↦ Trunc k (Y x)))) (trunc_sum_to k X Y (trunc_sum_inner k X Y x t))
      (trunc_unit k (Σ X (x ↦ Trunc k (Y x))) (x, t))
  ≔ let S ≔ Σ X Y in let T ≔ Σ X (x ↦ Trunc k (Y x)) in
    trunc_ind k (Y x) (truncation k (Y x))
      (s ↦ Id (Trunc k T) (trunc_sum_to k X Y (trunc_sum_inner k X Y x s)) (trunc_unit k T (x, s)))
      (s ↦ hlevel_raise k (Id (Trunc k T) (trunc_sum_to k X Y (trunc_sum_inner k X Y x s)) (trunc_unit k T (x, s)))
        (trunc_level k T (trunc_sum_to k X Y (trunc_sum_inner k X Y x s)) (trunc_unit k T (x, s))))
      (y ↦ calc
        trunc_sum_to k X Y (trunc_sum_inner k X Y x (trunc_unit k (Y x) y))
        = trunc_sum_to k X Y (trunc_unit k S (x, y))
          by refl (trunc_sum_to k X Y) (inverse (Trunc k S) (trunc_unit k S (x, y))
            (trunc_sum_inner k X Y x (trunc_unit k (Y x) y))
            (trunc_extend_beta k (Y x) (truncation k (Y x)) (Trunc k S) (trunc_level k S) (u ↦ trunc_unit k S (x, u)) y))
        = trunc_unit k T (x, trunc_unit k (Y x) y)
          by inverse (Trunc k T) (trunc_unit k T (x, trunc_unit k (Y x) y)) (trunc_sum_to k X Y (trunc_unit k S (x, y)))
            (trunc_extend_beta k S (truncation k S) (Trunc k T) (trunc_level k T)
              (u ↦ trunc_unit k T (u .fst, trunc_unit k (Y (u .fst)) (u .snd))) (x, y)) ∎) t

def trunc_sum_section (k : Nat) (X : Type) (Y : X → Type) (z : Trunc k (Σ X (x ↦ Trunc k (Y x))))
  : Id (Trunc k (Σ X (x ↦ Trunc k (Y x)))) (trunc_sum_to k X Y (trunc_sum_from k X Y z)) z
  ≔ let S ≔ Σ X Y in let T ≔ Σ X (x ↦ Trunc k (Y x)) in
    trunc_ind k T (truncation k T) (v ↦ Id (Trunc k T) (trunc_sum_to k X Y (trunc_sum_from k X Y v)) v)
      (v ↦ hlevel_raise k (Id (Trunc k T) (trunc_sum_to k X Y (trunc_sum_from k X Y v)) v)
        (trunc_level k T (trunc_sum_to k X Y (trunc_sum_from k X Y v)) v))
      (w ↦ concat (Trunc k T) (trunc_sum_to k X Y (trunc_sum_from k X Y (trunc_unit k T w)))
        (trunc_sum_to k X Y (trunc_sum_inner k X Y (w .fst) (w .snd))) (trunc_unit k T w)
        (refl (trunc_sum_to k X Y) (inverse (Trunc k S) (trunc_sum_inner k X Y (w .fst) (w .snd))
          (trunc_sum_from k X Y (trunc_unit k T w))
          (trunc_extend_beta k T (truncation k T) (Trunc k S) (trunc_level k S)
            (u ↦ trunc_sum_inner k X Y (u .fst) (u .snd)) w)))
        (trunc_sum_section_inner k X Y (w .fst) (w .snd))) z

def trunc_sum_equiv (k : Nat) (X : Type) (Y : X → Type)
  : Equiv (Trunc k (Σ X Y)) (Trunc k (Σ X (x ↦ Trunc k (Y x))))
  ≔ quasi_inverse_equiv (Trunc k (Σ X Y)) (Trunc k (Σ X (x ↦ Trunc k (Y x))))
      (trunc_sum_to k X Y) (trunc_sum_from k X Y) (trunc_sum_retraction k X Y) (trunc_sum_section k X Y)

{` The n-truncation of an n-type is the type itself. `}
def trunc_of_level_equiv (k : Nat) (S : Type) (hS : HLevel (suc. k) S) : Equiv (Trunc k S) S
  ≔ quasi_inverse_equiv (Trunc k S) S (trunc_extend k S (truncation k S) S hS (identity S)) (trunc_unit k S)
      (z ↦ trunc_ind k S (truncation k S)
        (v ↦ Id (Trunc k S) (trunc_unit k S (trunc_extend k S (truncation k S) S hS (identity S) v)) v)
        (v ↦ hlevel_raise k (Id (Trunc k S) (trunc_unit k S (trunc_extend k S (truncation k S) S hS (identity S) v)) v)
          (trunc_level k S (trunc_unit k S (trunc_extend k S (truncation k S) S hS (identity S) v)) v))
        (s ↦ refl (trunc_unit k S) (inverse S s (trunc_extend k S (truncation k S) S hS (identity S) (trunc_unit k S s))
          (trunc_extend_beta k S (truncation k S) S hS (identity S) s))) z)
      (s ↦ inverse S s (trunc_extend k S (truncation k S) S hS (identity S) (trunc_unit k S s))
        (trunc_extend_beta k S (truncation k S) S hS (identity S) s))

{` The version used in the proof of thm:n-im-univ-prop: over an n-type
   base only the summands need truncating. `}
def trunc_sum_level_base_equiv (k : Nat) (X : Type) (hX : HLevel (suc. k) X) (Y : X → Type)
  : Equiv (Trunc k (Σ X Y)) (Σ X (x ↦ Trunc k (Y x)))
  ≔ compose_equiv (Trunc k (Σ X Y)) (Trunc k (Σ X (x ↦ Trunc k (Y x)))) (Σ X (x ↦ Trunc k (Y x)))
      (trunc_sum_equiv k X Y)
      (trunc_of_level_equiv k (Σ X (x ↦ Trunc k (Y x)))
        (hlevel_sigma (suc. k) X (x ↦ Trunc k (Y x)) hX (x ↦ trunc_level k (Y x))))

{` An n-connected map into an n-type presents it as the n-truncation of
   its domain; the map is the extension of g. `}
def connected_level_inverse (k : Nat) (A S : Type) (g : A → S) (hg : NConnectedMap k A S g) (s : S) : Trunc k A
  ≔ trunc_extend k (BookFiber A S g s) (truncation k (BookFiber A S g s)) (Trunc k A) (trunc_level k A)
      (w ↦ trunc_unit k A (w .fst)) (hg s .center)

def connected_level_section (k : Nat) (A S : Type) (hS : HLevel (suc. k) S) (g : A → S) (hg : NConnectedMap k A S g)
  (s : S) : Id S (trunc_extend k A (truncation k A) S hS g (connected_level_inverse k A S g hg s)) s
  ≔ let F ≔ BookFiber A S g s in
    let G ≔ trunc_extend k A (truncation k A) S hS g in
    let M ≔ trunc_extend k F (truncation k F) (Trunc k A) (trunc_level k A) (w ↦ trunc_unit k A (w .fst)) in
    trunc_ind k F (truncation k F) (t ↦ Id S (G (M t)) s)
      (t ↦ hlevel_raise k (Id S (G (M t)) s) (hS (G (M t)) s))
      (w ↦ calc
        G (M (trunc_unit k F w)) = G (trunc_unit k A (w .fst))
          by refl G (inverse (Trunc k A) (trunc_unit k A (w .fst)) (M (trunc_unit k F w))
            (trunc_extend_beta k F (truncation k F) (Trunc k A) (trunc_level k A) (v ↦ trunc_unit k A (v .fst)) w))
        = g (w .fst) by inverse S (g (w .fst)) (G (trunc_unit k A (w .fst)))
            (trunc_extend_beta k A (truncation k A) S hS g (w .fst))
        = s by inverse S s (g (w .fst)) (w .snd) ∎) (hg s .center)

def connected_level_retraction (k : Nat) (A S : Type) (hS : HLevel (suc. k) S) (g : A → S) (hg : NConnectedMap k A S g)
  (z : Trunc k A) : Id (Trunc k A) (connected_level_inverse k A S g hg (trunc_extend k A (truncation k A) S hS g z)) z
  ≔ let G ≔ trunc_extend k A (truncation k A) S hS g in
    let inv ≔ connected_level_inverse k A S g hg in
    trunc_ind k A (truncation k A) (v ↦ Id (Trunc k A) (inv (G v)) v)
      (v ↦ hlevel_raise k (Id (Trunc k A) (inv (G v)) v) (trunc_level k A (inv (G v)) v))
      (a ↦ let F ≔ BookFiber A S g (g a) in
        let M ≔ trunc_extend k F (truncation k F) (Trunc k A) (trunc_level k A) (w ↦ trunc_unit k A (w .fst)) in
        calc
          inv (G (trunc_unit k A a)) = inv (g a)
            by refl inv (inverse S (g a) (G (trunc_unit k A a)) (trunc_extend_beta k A (truncation k A) S hS g a))
          = M (trunc_unit k F (a, refl (g a)))
            by refl M (hg (g a) .contract (trunc_unit k F (a, refl (g a))))
          = trunc_unit k A a
            by inverse (Trunc k A) (trunc_unit k A a) (M (trunc_unit k F (a, refl (g a))))
              (trunc_extend_beta k F (truncation k F) (Trunc k A) (trunc_level k A) (w ↦ trunc_unit k A (w .fst))
                (a, refl (g a))) ∎) z

def connected_level_reflection (k : Nat) (A S : Type) (hS : HLevel (suc. k) S) (g : A → S) (hg : NConnectedMap k A S g)
  : Equiv (Trunc k A) S
  ≔ quasi_inverse_equiv (Trunc k A) S (trunc_extend k A (truncation k A) S hS g) (connected_level_inverse k A S g hg)
      (connected_level_retraction k A S hS g hg) (connected_level_section k A S hS g hg)

{` n-connectedness of maps is invariant under equivalences, and the
   induced map on fibers over a further map is n-connected. `}
def postequivalence_n_connected (k : Nat) (A X Y : Type) (e : Equiv X Y) (f : A → X) (hf : NConnectedMap k A X f)
  : NConnectedMap k A Y (compose A X Y (e .map) f)
  ≔ equivalence_induction X (Y e ↦ NConnectedMap k A Y (compose A X Y (e .map) f)) hf Y e

def cancel_preequivalence_n_connected (k : Nat) (A X B : Type) (e : Equiv A X) (f : X → B)
  (hf : NConnectedMap k A B (compose A X B f (e .map))) : NConnectedMap k X B f
  ≔ equivalence_induction A
      (X e ↦ (f : X → B) → NConnectedMap k A B (compose A X B f (e .map)) → NConnectedMap k X B f)
      (f hf ↦ hf) X e f hf

def total_n_connected_fiberwise (k : Nat) (B : Type) (P Q : B → Type) (f : (b : B) → P b → Q b)
  (hf : NConnectedMap k (Σ B P) (Σ B Q) (totalize B P Q f))
  : (b : B) → NConnectedMap k (P b) (Q b) (f b)
  ≔ b q ↦ n_connected_type_equiv k (BookFiber (Σ B P) (Σ B Q) (totalize B P Q f) (b, q)) (BookFiber (P b) (Q b) (f b) q)
      (total_fiber_equiv B P Q f b q) (hf (b, q))

def composite_fiber_map_n_connected (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g) (h : X → B)
  : (b : B) → NConnectedMap k (BookFiber A B (compose A X B h g) b) (BookFiber X B h b) (composite_fiber_map A X B g h b)
  ≔ total_n_connected_fiberwise k B (BookFiber A B (compose A X B h g)) (BookFiber X B h)
      (composite_fiber_map A X B g h)
      (cancel_preequivalence_n_connected k A (Σ B (BookFiber A B (compose A X B h g)))
        (Σ B (BookFiber X B h)) (fiber_decomposition_equiv A B (compose A X B h g))
        (totalize B (BookFiber A B (compose A X B h g)) (BookFiber X B h) (composite_fiber_map A X B g h))
        (postequivalence_n_connected k A X (Σ B (BookFiber X B h)) (fiber_decomposition_equiv X B h) g hg))

{` For g n-connected and h n-truncated, ||(hg)⁻¹(b)||_n ≃ h⁻¹(b). `}
def n_composite_truncated_fiber_equiv (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) (b : B)
  : Equiv (Trunc k (BookFiber A B (compose A X B h g) b)) (BookFiber X B h b)
  ≔ connected_level_reflection k (BookFiber A B (compose A X B h g) b) (BookFiber X B h b) (hh b)
      (composite_fiber_map A X B g h b) (composite_fiber_map_n_connected k A X B g hg h b)
