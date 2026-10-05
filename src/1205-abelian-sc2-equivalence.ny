export "1204-double-delooping"

{` Chapter 12, thm:abelian-groups-weq-sc2types (abelian.tex 409-666), second
   half: for a pointed simply connected 2-type (A, a), the pointed map
   Φ : (A, a) →* BB(Ω(A, a)), Φ(a') ≔ (a = a', κ_{a'}), is an equivalence;
   hence AbelianGroup ≃ SimplyConnectedTwoType with the maps BB and Ω.

   κ_{a'} : ‖(a = a) = (a = a')‖₀ is the common value of the weakly constant
   map p ↦ |ap_{a = -}(p)|₀ on the connected type a = a' (the book uses the
   contractible type T(a') of the same data). Instead of the book's direct
   computation of the fibers of Φ, Φ is shown to be an equivalence on loops
   (cor:fib-vs-path), using that ev_{refl a} ∘ ap_Φ is ℓ ↦ refl·ℓ and that
   ev_{refl a} on Ω BB(Ω(A, a)) is an equivalence (abelianness, as in the
   book). `}

{` 2-out-of-3: a map with a left inverse that is an equivalence is an
   equivalence. `}
def left_inverse_equiv_is_equiv (A B : Type) (g : B → A) (hg : BookIsEquiv B A g) (f : A → B)
  (h : (x : A) → Id A (g (f x)) x) : BookIsEquiv A B f
  ≔ let e ≔ native_equivalence B A (g, hg) in
    book_equivalence A B
      (equiv_change_map A B (canonical_inverse_equiv B A e) f
        (x ↦ concat B (equiv_inverse_map B A e x) (equiv_inverse_map B A e (g (f x))) (f x)
          (refl (equiv_inverse_map B A e) (inverse A (g (f x)) x (h x)))
          (equiv_retraction B A e (f x)))) .equiv

{` For (A, a) simply connected, every a = a' is connected. `}
def sc2_paths_connected (X : SimplyConnectedTwoType) (y : X .fst .carrier)
  : Connected (Id (X .fst .carrier) (X .fst .point) y)
  ≔ connected_based_elim native_truncation (X .fst .carrier) (X .snd .fst) (X .fst .point)
      (z ↦ Connected (Id (X .fst .carrier) (X .fst .point) z))
      (z ↦ connected_prop (Id (X .fst .carrier) (X .fst .point) z))
      (X .snd .snd .fst) y

def sc2_kappa_function (X : SimplyConnectedTwoType) (y : X .fst .carrier)
  (p : Id (X .fst .carrier) (X .fst .point) y)
  : SetTrunc (Id Type (Loop (X .fst)) (Id (X .fst .carrier) (X .fst .point) y))
  ≔ set_trunc (Id Type (Loop (X .fst)) (Id (X .fst .carrier) (X .fst .point) y))
      (refl ((z ↦ Id (X .fst .carrier) (X .fst .point) z) : X .fst .carrier → Type) p)

def sc2_kappa (X : SimplyConnectedTwoType) (y : X .fst .carrier)
  : SetTrunc (Id Type (Loop (X .fst)) (Id (X .fst .carrier) (X .fst .point) y))
  ≔ connected_set_map_value (Id (X .fst .carrier) (X .fst .point) y)
      (SetTrunc (Id Type (Loop (X .fst)) (Id (X .fst .carrier) (X .fst .point) y)))
      (sc2_paths_connected X y)
      (set_trunc_set (Id Type (Loop (X .fst)) (Id (X .fst .carrier) (X .fst .point) y)))
      (sc2_kappa_function X y)

{` Φ : A → BB(Ω(A, a)), a' ↦ (a = a', κ_{a'}). `}
def sc2_reconstruction (X : SimplyConnectedTwoType) (y : X .fst .carrier) : BB (sc2_loop_group X) .carrier
  ≔ (Id (X .fst .carrier) (X .fst .point) y, sc2_kappa X y)

def sc2_kappa_point (X : SimplyConnectedTwoType)
  : Id (SetTrunc (Id Type (Loop (X .fst)) (Loop (X .fst))))
      (set_trunc (Id Type (Loop (X .fst)) (Loop (X .fst))) (refl (Loop (X .fst)))) (sc2_kappa X (X .fst .point))
  ≔ inverse (SetTrunc (Id Type (Loop (X .fst)) (Loop (X .fst)))) (sc2_kappa X (X .fst .point))
      (sc2_kappa_function X (X .fst .point) (refl (X .fst .point)))
      (connected_set_map_value_beta (Loop (X .fst)) (SetTrunc (Id Type (Loop (X .fst)) (Loop (X .fst))))
        (sc2_paths_connected X (X .fst .point)) (set_trunc_set (Id Type (Loop (X .fst)) (Loop (X .fst))))
        (sc2_kappa_function X (X .fst .point)) (refl (X .fst .point)))

{` Φ is pointed: pt_{BB} = Φ(a), with first component refl. `}
def sc2_reconstruction_point (X : SimplyConnectedTwoType)
  : Id (BB (sc2_loop_group X) .carrier) (BB (sc2_loop_group X) .point) (sc2_reconstruction X (X .fst .point))
  ≔ (refl (Loop (X .fst)), sc2_kappa_point X)

def sc2_reconstruction_pointed (X : SimplyConnectedTwoType) : BookPointedMap (X .fst) (BB (sc2_loop_group X))
  ≔ (sc2_reconstruction X, sc2_reconstruction_point X)

{` Evaluation at y on loops of (Y, α) in Ũ_{B0} U, and its invariance under
   changing α along a path. `}
def univ_cover_loop_evaluation (B0 Y : Type) (α : SetTrunc (Id Type B0 Y)) (y : Y)
  (r : Id (UnivCover Type B0) (Y, α) (Y, α)) : Y
  ≔ r .fst .trr y

def univ_cover_loop_evaluation_transfer (B0 Y : Type) (α β : SetTrunc (Id Type B0 Y))
  (ζ : Id (SetTrunc (Id Type B0 Y)) α β) (y : Y)
  (h : BookIsEquiv (Id (UnivCover Type B0) (Y, α) (Y, α)) Y (univ_cover_loop_evaluation B0 Y α y))
  : BookIsEquiv (Id (UnivCover Type B0) (Y, β) (Y, β)) Y (univ_cover_loop_evaluation B0 Y β y)
  ≔ J (SetTrunc (Id Type B0 Y)) α
      (γ _ ↦ BookIsEquiv (Id (UnivCover Type B0) (Y, γ) (Y, γ)) Y (univ_cover_loop_evaluation B0 Y γ y))
      h β ζ

{` ev_{refl a} on loops at Φ(a) is an equivalence (since Ω(A, a) is abelian). `}
def sc2_reconstruction_loop_evaluation_equiv (X : SimplyConnectedTwoType)
  : BookIsEquiv (Id (BB (sc2_loop_group X) .carrier) (sc2_reconstruction X (X .fst .point))
        (sc2_reconstruction X (X .fst .point)))
      (Loop (X .fst))
      (univ_cover_loop_evaluation (Loop (X .fst)) (Loop (X .fst)) (sc2_kappa X (X .fst .point)) (refl (X .fst .point)))
  ≔ univ_cover_loop_evaluation_transfer (Loop (X .fst)) (Loop (X .fst))
      (set_trunc (Id Type (Loop (X .fst)) (Loop (X .fst))) (refl (Loop (X .fst))))
      (sc2_kappa X (X .fst .point)) (sc2_kappa_point X) (refl (X .fst .point))
      (abelian_bb_loops_equiv (sc2_loop_group X) (sc2_loop_group_abelian X))

{` ev_{refl a}(ap_Φ(ℓ)) = refl · ℓ = ℓ. `}
def sc2_reconstruction_ap_section (X : SimplyConnectedTwoType) (l : Loop (X .fst))
  : Id (Loop (X .fst))
      (univ_cover_loop_evaluation (Loop (X .fst)) (Loop (X .fst)) (sc2_kappa X (X .fst .point)) (refl (X .fst .point))
        (refl (sc2_reconstruction X) l))
      l
  ≔ concat_1p (X .fst .carrier) (X .fst .point) (X .fst .point) l

def sc2_reconstruction_ap_equiv (X : SimplyConnectedTwoType)
  : BookIsEquiv (Loop (X .fst))
      (Id (BB (sc2_loop_group X) .carrier) (sc2_reconstruction X (X .fst .point)) (sc2_reconstruction X (X .fst .point)))
      (map_path (X .fst .carrier) (BB (sc2_loop_group X) .carrier) (sc2_reconstruction X) (X .fst .point) (X .fst .point))
  ≔ left_inverse_equiv_is_equiv (Loop (X .fst))
      (Id (BB (sc2_loop_group X) .carrier) (sc2_reconstruction X (X .fst .point)) (sc2_reconstruction X (X .fst .point)))
      (univ_cover_loop_evaluation (Loop (X .fst)) (Loop (X .fst)) (sc2_kappa X (X .fst .point)) (refl (X .fst .point)))
      (sc2_reconstruction_loop_evaluation_equiv X)
      (map_path (X .fst .carrier) (BB (sc2_loop_group X) .carrier) (sc2_reconstruction X) (X .fst .point) (X .fst .point))
      (sc2_reconstruction_ap_section X)

def sc2_reconstruction_equiv (X : SimplyConnectedTwoType)
  : BookEquiv (X .fst .carrier) (BB (sc2_loop_group X) .carrier)
  ≔ connected_map_equiv_from_loops native_truncation (X .fst .carrier) (BB (sc2_loop_group X) .carrier)
      (sc2_reconstruction X) (X .snd .fst) (bb_simply_connected (sc2_loop_group X) .fst) (X .fst .point)
      (sc2_reconstruction_ap_equiv X)

def sc2_reconstruction_pointed_equiv (X : SimplyConnectedTwoType) : BookPointedEquiv (X .fst) (BB (sc2_loop_group X))
  ≔ (sc2_reconstruction_pointed X, sc2_reconstruction_equiv X .equiv)

def sc2_bb_loops_path (X : SimplyConnectedTwoType) : Id SimplyConnectedTwoType (bb_sc2 (sc2_loop_group X)) X
  ≔ sc2_path (bb_sc2 (sc2_loop_group X)) X
      (inverse Pointed (X .fst) (BB (sc2_loop_group X))
        (equiv_inverse_map (Id Pointed (X .fst) (BB (sc2_loop_group X))) (BookPointedEquiv (X .fst) (BB (sc2_loop_group X)))
          (pointed_path_equiv (X .fst) (BB (sc2_loop_group X))) (sc2_reconstruction_pointed_equiv X)))

{` thm:abelian-groups-weq-sc2types: AbelianGroup ≃ pointed simply connected
   2-types, by G ↦ BB G with inverse (A, a) ↦ Ω(A, a). `}
def abelian_groups_sc2_equiv : Equiv AbelianGroup SimplyConnectedTwoType
  ≔ quasi_inverse_equiv AbelianGroup SimplyConnectedTwoType (A ↦ bb_sc2 (A .fst)) sc2_loops
      abelian_bb_loops_path sc2_bb_loops_path

def abelian_groups_sc2_book_equiv : BookEquiv AbelianGroup SimplyConnectedTwoType
  ≔ book_equivalence AbelianGroup SimplyConnectedTwoType abelian_groups_sc2_equiv

{` Higher deloopings (abelian.tex 670-673): for abelian G, BB G is a
   delooping of BG, i.e. Ω(BB G) = BG as pointed types. `}
def abelian_bb_delooping (G : Group) (h : IsAbelian G) : Id Pointed (Omega (BB G)) (BG G)
  ≔ equiv_inverse_map (Id Pointed (Omega (BB G)) (BG G)) (BookPointedEquiv (Omega (BB G)) (BG G))
      (pointed_path_equiv (Omega (BB G)) (BG G)) (abelian_bb_loops_pointed_equiv G h)
