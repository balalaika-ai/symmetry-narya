export "501-transitive-gsets"

{` Chapter 5 (actions.tex), sec:gsets and sec:transitiveGsets:
   - def:finite-G-set, footnote: X(sh_G) is finite (an n-element set) iff
     X(z) is, for any z : BG;
   - the remark after def:transitiveGset: equivalent forms of transitivity
     (surjectivity of - · x, eq:Gset-trans-gen at every z, nonempty and
     pairwise), and the empty G-set is not transitive;
   - xca:normal-action-equiv: if ev_x : (X = X) → X(z) is an equivalence for
     one pair (z, x), then for all pairs (no transitivity needed). `}

{` A property of sets holds at X(sh_G) iff it holds at X(z), for each
   z : BG (BG is connected). `}
def gset_set_property_at_iff (G : Group) (X : GSet G) (Q : SetTypes → Type)
  (hQ : (S : SetTypes) → isProp (Q S)) (z : BG G .carrier)
  : Product (Q (X (shape G)) → Q (X z)) (Q (X z) → Q (X (shape G)))
  ≔ let B ≔ BG G .carrier in
    (q ↦ mere_rec (Id B (shape G) z) (Q (X z)) (hQ (X z))
        (p ↦ transport B (w ↦ Q (X w)) (shape G) z p q) (bg_connected G .snd (shape G) z),
     q ↦ mere_rec (Id B z (shape G)) (Q (X (shape G))) (hQ (X (shape G)))
        (p ↦ transport B (w ↦ Q (X w)) z (shape G) p q) (bg_connected G .snd z (shape G)))

{` def:finite-G-set, footnote: X(sh_G) is finite iff X(z) is finite, for
   any z : BG; equivalently, iff X(z) is finite for all z. `}
def gset_finite_at_iff (G : Group) (X : GSet G) (z : BG G .carrier)
  : Product (IsFiniteGSet G X → IsFinite (X z .fst)) (IsFinite (X z .fst) → IsFiniteGSet G X)
  ≔ gset_set_property_at_iff G X (S ↦ IsFinite (S .fst)) (S ↦ isfinite_prop (S .fst)) z

def gset_finite_everywhere_iff (G : Group) (X : GSet G)
  : Product (IsFiniteGSet G X → (z : BG G .carrier) → IsFinite (X z .fst))
      (((z : BG G .carrier) → IsFinite (X z .fst)) → IsFiniteGSet G X)
  ≔ (h z ↦ gset_finite_at_iff G X z .fst h, h ↦ h (shape G))

{` The same for n-element sets (‖(Fin n, !) = S‖ in Set, as in
   BookFiniteSetsAt). `}
def GSetNElementAt (G : Group) (X : GSet G) (n : Nat) (z : BG G .carrier) : Type
  ≔ Mere (Id SetTypes (Fin n, fin_set n) (X z))

def gset_n_element_at_iff (G : Group) (X : GSet G) (n : Nat) (z : BG G .carrier)
  : Product (GSetNElementAt G X n (shape G) → GSetNElementAt G X n z)
      (GSetNElementAt G X n z → GSetNElementAt G X n (shape G))
  ≔ gset_set_property_at_iff G X (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S))
      (S ↦ mere_isprop (Id SetTypes (Fin n, fin_set n) S)) z

def gset_n_element_everywhere_iff (G : Group) (X : GSet G) (n : Nat)
  : Product (GSetNElementAt G X n (shape G) → (z : BG G .carrier) → GSetNElementAt G X n z)
      (((z : BG G .carrier) → GSetNElementAt G X n z) → GSetNElementAt G X n (shape G))
  ≔ (h z ↦ gset_n_element_at_iff G X n z .fst h, h ↦ h (shape G))

{` Solving x = g · y for y: y = g⁻¹ · x. `}
def gset_act_solve (G : Group) (X : GSet G) (g : USym G) (x y : gset_underlying G X)
  (e : Id (gset_underlying G X) x (gset_usym_act G X g y))
  : Id (gset_underlying G X) y (gset_usym_act G X (usym_inv G g) x)
  ≔ let S ≔ gset_underlying G X in
    concat S y (gset_usym_act G X (usym_inv G g) (gset_usym_act G X g y)) (gset_usym_act G X (usym_inv G g) x)
      (inverse S (gset_usym_act G X (usym_inv G g) (gset_usym_act G X g y)) y (gset_act_inv_left G X g y))
      (refl (gset_usym_act G X (usym_inv G g)) (inverse S x (gset_usym_act G X g y) e))

{` Remark after def:transitiveGset, first form: X is transitive iff there is
   x : X(sh_G) such that - · x : USym G → X(sh_G) is surjective. `}
def GSetOrbitMapSurjective (G : Group) (X : GSet G) : Type
  ≔ Mere (Σ (gset_underlying G X) (x ↦ Surjective (USym G) (gset_underlying G X) (g ↦ gset_usym_act G X g x)))

def transitive_surjective_iff (G : Group) (X : GSet G)
  : Product (IsTransitive G X → GSetOrbitMapSurjective G X) (GSetOrbitMapSurjective G X → IsTransitive G X)
  ≔ let S ≔ gset_underlying G X in
    let Tr ≔ Σ S (x ↦ (y : S) → Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))) in
    let Su ≔ Σ S (x ↦ Surjective (USym G) S (g ↦ gset_usym_act G X g x)) in
    (t ↦ mere_rec Tr (GSetOrbitMapSurjective G X) (mere_isprop Su)
        (xh ↦ mere Su (xh .fst, y ↦ mere_rec (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g y)))
            (Mere (BookFiber (USym G) S (g ↦ gset_usym_act G X g (xh .fst)) y))
            (mere_isprop (BookFiber (USym G) S (g ↦ gset_usym_act G X g (xh .fst)) y))
            (ge ↦ mere (BookFiber (USym G) S (g ↦ gset_usym_act G X g (xh .fst)) y)
              (usym_inv G (ge .fst), gset_act_solve G X (ge .fst) (xh .fst) y (ge .snd)))
            (xh .snd y))) t,
     s ↦ mere_rec Su (IsTransitive G X) (is_transitive_prop G X)
        (xh ↦ mere Tr (xh .fst, y ↦ mere_rec (BookFiber (USym G) S (g ↦ gset_usym_act G X g (xh .fst)) y)
            (Mere (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g y))))
            (mere_isprop (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g y))))
            (ge ↦ mere (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g y)))
              (usym_inv G (ge .fst), gset_act_solve G X (ge .fst) y (xh .fst) (ge .snd)))
            (xh .snd y))) s)

{` eq:Gset-trans-gen: Π_{z:BG} ∃_{x:X(z)} Π_{y:X(z)} ∃_{g : z = z} (x = g · y).
   At z ≡ sh_G this is literally IsTransitive G X. `}
def GSetTransitiveAt (G : Group) (X : GSet G) (z : BG G .carrier) : Type
  ≔ Mere (Σ (X z .fst) (x ↦ (y : X z .fst) →
      Mere (Σ (Id (BG G .carrier) z z) (g ↦ Id (X z .fst) x (gset_act G X z z g y)))))

def GSetTransitiveEverywhere (G : Group) (X : GSet G) : Type
  ≔ (z : BG G .carrier) → GSetTransitiveAt G X z

def transitive_at_shape (G : Group) (X : GSet G)
  : Id Type (GSetTransitiveAt G X (shape G)) (IsTransitive G X)
  ≔ refl (IsTransitive G X)

def transitive_everywhere_iff (G : Group) (X : GSet G)
  : Product (IsTransitive G X → GSetTransitiveEverywhere G X) (GSetTransitiveEverywhere G X → IsTransitive G X)
  ≔ (t ↦ connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
        (z ↦ GSetTransitiveAt G X z)
        (z ↦ mere_isprop (Σ (X z .fst) (x ↦ (y : X z .fst) →
            Mere (Σ (Id (BG G .carrier) z z) (g ↦ Id (X z .fst) x (gset_act G X z z g y))))))
        t,
     h ↦ h (shape G))

{` Third form: X(sh_G) is nonempty and any two elements are related,
   ∀ x y ∃ g (x = g · y). `}
def GSetTransitivePairwise (G : Group) (X : GSet G) : Type
  ≔ Product (Mere (gset_underlying G X))
      ((x y : gset_underlying G X) → Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) x (gset_usym_act G X g y))))

def transitive_pair_step (G : Group) (X : GSet G) (x0 x y : gset_underlying G X)
  (g1 : USym G) (e1 : Id (gset_underlying G X) x0 (gset_usym_act G X g1 x))
  (g2 : USym G) (e2 : Id (gset_underlying G X) x0 (gset_usym_act G X g2 y))
  : Id (gset_underlying G X) x (gset_usym_act G X (usym_mul G (usym_inv G g1) g2) y)
  ≔ let S ≔ gset_underlying G X in
    let h1 ≔ usym_inv G g1 in
    concat S x (gset_usym_act G X h1 x0) (gset_usym_act G X (usym_mul G h1 g2) y)
      (gset_act_solve G X g1 x0 x e1)
      (concat S (gset_usym_act G X h1 x0) (gset_usym_act G X h1 (gset_usym_act G X g2 y))
        (gset_usym_act G X (usym_mul G h1 g2) y)
        (refl (gset_usym_act G X h1) e2)
        (inverse S (gset_usym_act G X (usym_mul G h1 g2) y) (gset_usym_act G X h1 (gset_usym_act G X g2 y))
          (gset_act_mul G X h1 g2 y)))

def transitive_pairwise_iff (G : Group) (X : GSet G)
  : Product (IsTransitive G X → GSetTransitivePairwise G X) (GSetTransitivePairwise G X → IsTransitive G X)
  ≔ let S ≔ gset_underlying G X in
    let R : S → S → Type ≔ x y ↦ Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))) in
    let Tr ≔ Σ S (x ↦ (y : S) → R x y) in
    (t ↦ (mere_rec Tr (Mere S) (mere_isprop S) (xh ↦ mere S (xh .fst)) t,
          x y ↦ mere_rec Tr (R x y) (mere_isprop (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))))
            (xh ↦ mere_rec (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g x))) (R x y)
              (mere_isprop (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))))
              (ge1 ↦ mere_rec (Σ (USym G) (g ↦ Id S (xh .fst) (gset_usym_act G X g y))) (R x y)
                (mere_isprop (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))))
                (ge2 ↦ mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))
                  (usym_mul G (usym_inv G (ge1 .fst)) (ge2 .fst),
                   transitive_pair_step G X (xh .fst) x y (ge1 .fst) (ge1 .snd) (ge2 .fst) (ge2 .snd)))
                (xh .snd y))
              (xh .snd x))
            t),
     p ↦ mere_rec S (IsTransitive G X) (is_transitive_prop G X)
        (x ↦ mere Tr (x, y ↦ p .snd x y)) (p .fst))

{` "The empty G-set is not transitive": a transitive G-set has an element,
   so triv_G ∅ is not transitive. `}
def gset_transitive_nonempty (G : Group) (X : GSet G) (t : IsTransitive G X) : Mere (gset_underlying G X)
  ≔ transitive_pairwise_iff G X .fst t .fst

def gset_empty_not_transitive (G : Group) (t : IsTransitive G (gset_trivial G (Empty, empty_set))) : Empty
  ≔ mere_rec Empty Empty empty_prop (e ↦ e) (gset_transitive_nonempty G (gset_trivial G (Empty, empty_set)) t)

{` xca:normal-action-equiv. Transport of equivalence-ness along a homotopy. `}
def book_isequiv_homotopic (A B : Type) (f g : A → B) (H : (a : A) → Id B (f a) (g a))
  (hf : BookIsEquiv A B f) : BookIsEquiv A B g
  ≔ transport (A → B) (BookIsEquiv A B) f g (funext A (_ ↦ B) f g H) hf

{` If ev_x is an equivalence and x' = ev_x(e), then ev_{x'} = ev_x ∘ (e · -):
   f_z(e_z(x)) = (e then f)_z(x). `}
def normal_eval_equiv_same_fiber (G : Group) (X : GSet G) (z : BG G .carrier) (x : X z .fst)
  (h : BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x)) (x' : X z .fst)
  : BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x')
  ≔ let P ≔ Id (GSet G) X X in
    let F : GSet G → Type ≔ W ↦ W z .fst in
    let ev ≔ gset_path_eval G X X z x in
    let c ≔ h x' .center in
    let e : P ≔ c .fst in
    let ex : Id (X z .fst) x' (ev e) ≔ c .snd in
    let E ≔ compose_equiv P P (X z .fst) (concat_left_equiv (GSet G) X X X e)
      (native_equivalence P (X z .fst) (ev, h)) in
    book_isequiv_homotopic P (X z .fst) (E .map) (gset_path_eval G X X z x')
      (f ↦ calc
        E .map f
        = transport (GSet G) F X X f (transport (GSet G) F X X e x)
          by transport_concat (GSet G) F X X X e f x
        = transport (GSet G) F X X f x'
          by refl (transport (GSet G) F X X f) (inverse (X z .fst) x' (ev e) ex) ∎)
      (book_equivalence P (X z .fst) E .equiv)

{` xca:normal-action-equiv: if ev_x is an equivalence for some z : BG and
   x : X(z), then for all w : BG and x' : X(w). Given p : z = w (merely),
   (w, x') = (z, p⁻¹ · x') in Tot(X), and ev at (z, p⁻¹ · x') is an
   equivalence by the previous lemma. Transitivity of X is not needed. `}
def normal_eval_equiv_everywhere (G : Group) (X : GSet G) (z : BG G .carrier) (x : X z .fst)
  (h : BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x)) : IsNormalGSet G X
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    let C : T → Type ≔ u ↦ BookIsEquiv (Id (GSet G) X X) (X (u .fst) .fst) (gset_path_eval G X X (u .fst) (u .snd)) in
    w x' ↦ mere_rec (Id B z w) (C (w, x')) (book_isequiv_isprop (Id (GSet G) X X) (X w .fst) (gset_path_eval G X X w x'))
      (p ↦ let x'' ≔ gset_act G X w z (inverse B z w p) x' in
        transport T C (z, x'') (w, x')
          (action_type_path G X z w x'' x' p (gset_act_inverse_right G X z w p x'))
          (normal_eval_equiv_same_fiber G X z x h x''))
      (bg_connected G .snd z w)

{` The book's exercise for transitive X (as in def:normal-action). `}
def normal_action_equiv (G : Group) (X : GSet G) (hX : IsTransitive G X) (z : BG G .carrier) (x : X z .fst)
  (h : BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x)) : IsNormalGSet G X
  ≔ normal_eval_equiv_everywhere G X z x h

{` Litmus: the underlying set of the empty G-set is Empty, and the principal
   G-set satisfies the pairwise form of transitivity. `}
def gset_empty_underlying (G : Group) : Id Type (gset_underlying G (gset_trivial G (Empty, empty_set))) Empty
  ≔ refl Empty

def principal_gset_pairwise (G : Group) : GSetTransitivePairwise G (gset_paths G (shape G))
  ≔ transitive_pairwise_iff G (gset_paths G (shape G)) .fst
      (connected_action_type_transitive G (gset_paths G (shape G))
        (contractible_connected (ActionType G (gset_paths G (shape G)))
          (book_pathspace_contractible (BG G .carrier) (shape G))))
