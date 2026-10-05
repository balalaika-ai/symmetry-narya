export "07-o-functor"

{` Blind statements, chapter 13 (fields.tex): con:swap-ptd-doms,
   xca:allptd-S1-contractible, con:swap-on-paths, def:O'. `}

{` con:swap-ptd-doms: a pointed equivalence
   swap : (X →* (Y →* Z)) →* (Y →* (X →* Z)) whose totally unpointed map
   swap÷÷ is the argument swap: (swap F)(y)(x) = F(x)(y) for every F (as
   functions Y÷ → X÷ → Z÷). `}
def BlindSwap (X Y Z : Pointed) : Type
  ≔ Σ (BookPointedEquiv (blind_ptd_maps X (blind_ptd_maps Y Z)) (blind_ptd_maps Y (blind_ptd_maps X Z)))
      (sw ↦ (F : BookPointedMap X (blind_ptd_maps Y Z))
        → Id (Y .carrier → X .carrier → Z .carrier)
            (y x ↦ sw .fst .fst F .fst y .fst x)
            (y x ↦ F .fst x .fst y))

def blind_con_swap_ptd_doms : Type ≔ (X Y Z : Pointed) → BlindSwap X Y Z

{` xca:allptd-S1-contractible: X, Y connected, Z a 1-type ⇒ X →* (Y →* Z) is
   contractible. `}
def blind_xca_allptd_S1_contractible : Type
  ≔ (X Y Z : Pointed) → Connected (X .carrier) → Connected (Y .carrier) → isGroupoid (Z .carrier)
    → BookIsContr (BookPointedMap X (blind_ptd_maps Y Z))

{` con:swap-on-paths: for f : A → (B → C), g(b)(a) ≔ f(a)(b) and q : b = b',
   the dependent functions a ↦ ap_{f(a)}(q) and ptw(ap_g(q)) are identified. `}
def blind_con_swap_on_paths : Type
  ≔ (A B C : Type) (f : A → B → C) (b b' : B) (q : Id B b b')
    → Id ((a : A) → Id C (f a b) (f a b'))
        (a ↦ refl (f a) q)
        (happly A (_ ↦ C) (a ↦ f a b) (a ↦ f a b') (refl ((b0 : B) (a : A) ↦ f a b0) q))

{` def:O'. As printed, O'_{A,B} : (A →* B) →* ((S¹ →* A) →* (S¹ →* B)) with
   O'_{A,B} ≔ (O_{A,B} ∘ swap⁻¹ ∘ -). The formula only typechecks when
   B = S¹ →* Y (as in fig:bjørn, where O' : (X →* ŜY) → (SX →* Ŝ(SY))):
   O'(φ) ≔ swap⁻¹ ∘ O(φ), with swap⁻¹ an automorphism of
   S¹ →* (S¹ →* Y). The book constructs swap only as a TBD; since the
   argument swap is an involution, swap⁻¹ (for X = Y = S¹) satisfies the same
   specification, so O' is taken relative to any sw : BlindSwap S¹ S¹ Y.
   No pointing of O' is given in the book; only the underlying map is
   defined. `}
def blind_O' (C : CircleSignature) (A Y : Pointed) (sw : BlindSwap (circle_pointed C) (circle_pointed C) Y)
  (φ : BookPointedMap A (blind_ptd_maps (circle_pointed C) Y))
  : BookPointedMap (blind_O C A) (blind_O C (blind_ptd_maps (circle_pointed C) Y))
  ≔ book_pointed_compose (blind_O C A) (blind_O C (blind_ptd_maps (circle_pointed C) Y))
      (blind_O C (blind_ptd_maps (circle_pointed C) Y))
      (blind_O_map C A (blind_ptd_maps (circle_pointed C) Y) φ) (sw .fst .fst)
