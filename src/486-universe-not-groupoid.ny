export "485-infinity-groups"

{` The universe is not a groupoid, relative to any circle C (instantiated at
   the constructed circle in module 487). Used for rem:autinfgp ("A_(a) can be
   a groupoid although A is not") and for the unconditional reading of
   xca:defgroup. The argument: a groupoid universe would make Equiv C C a set,
   hence every homotopy id ~ id trivial; but the central loop
   c : Π(x : C) x = x with c(base) = loop is not, since loop ≠ refl. `}
def int_one_code : Int → Type ≔ [
  | pos. zero. ↦ Empty
  | pos. (suc. _) ↦ Unit
  | neg. _ ↦ Empty ]

def int_one_ne_zero (p : Id Int (pos. (suc. zero.)) int_zero) : Empty
  ≔ transport Int int_one_code (pos. (suc. zero.)) int_zero p star.

def circle_loop_not_refl (C : CircleSignature)
  (p : Id (Id (C .carrier) (C .base) (C .base)) (C .loop) (refl (C .base))) : Empty
  ≔ int_one_ne_zero
      (concat Int (pos. (suc. zero.)) (circle_winding C (C .loop)) int_zero
        (inverse Int (circle_winding C (C .loop)) (pos. (suc. zero.)) (circle_winding_loop C))
        (concat Int (circle_winding C (C .loop)) (circle_winding C (refl (C .base))) int_zero
          (refl (circle_winding C) p) (circle_winding_refl C)))

{` Transport of loop along loop in x ↦ (x = x) is loop. `}
def circle_loop_self_transport (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base))
      (transport (C .carrier) (x ↦ Id (C .carrier) x x) (C .base) (C .base) (C .loop) (C .loop)) (C .loop)
  ≔ let X ≔ C .carrier in let b ≔ C .base in let l ≔ C .loop in
    calc
      transport X (x ↦ Id X x x) b b l l = loop_conjugate X b b l l by loop_transport_conjugate X b b l l
      = concat X b b b (concat X b b b (inverse X b b l) l) l
        by inverse (Id X b b) (concat X b b b (concat X b b b (inverse X b b l) l) l) (loop_conjugate X b b l l)
          (concat_assoc X b b b b (inverse X b b l) l l)
      = concat X b b b (refl b) l
        by refl ((q ↦ concat X b b b q l) : Id X b b → Id X b b) (concat_inverse_left X b b l)
      = l by concat_1p X b b l ∎

def circle_central_loop_data (C : CircleSignature)
  : CircleBoundary (C .carrier) (C .base) (C .loop) (x ↦ Id (C .carrier) x x)
  ≔ (C .loop, pathover_of_eq (C .carrier) (x ↦ Id (C .carrier) x x) (C .base) (C .base) (C .loop)
      (C .loop) (C .loop) (circle_loop_self_transport C))

{` The central loop c : Π(x : C) x = x with c(base) = loop. `}
def circle_central_loop (C : CircleSignature) : (x : C .carrier) → Id (C .carrier) x x
  ≔ C .induction (x ↦ Id (C .carrier) x x) (circle_central_loop_data C) .fst

def circle_central_loop_base (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base)) (circle_central_loop C (C .base)) (C .loop)
  ≔ C .induction (x ↦ Id (C .carrier) x x) (circle_central_loop_data C) .snd .fst

def universe_not_groupoid_of_circle (C : CircleSignature) (hT : isGroupoid Type) : Empty
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let hE : isSet (Equiv X X)
      ≔ hlevel_two_to_set (Equiv X X)
          (hlevel_equiv (suc. (suc. zero.)) (Id Type X X) (Equiv X X) (univalence_equiv X X)
            (set_to_hlevel_two (Id Type X X) (hT X X))) in
    let idE ≔ identity_equiv X in
    let c ≔ circle_central_loop C in
    let e2 : Id (Equiv X X) idE idE ≔ equiv_path X X idE idE (funext X (_ ↦ X) (identity X) (identity X) c) in
    let ev : Id (Equiv X X) idE idE → Id X b b ≔ r ↦ happly X (_ ↦ X) (identity X) (identity X) (r .map) b in
    circle_loop_not_refl C
      (calc
        C .loop = c b by inverse (Id X b b) (c b) (C .loop) (circle_central_loop_base C)
        = ev e2 by funext_beta X (_ ↦ X) (identity X) (identity X) c b
        = ev (refl idE) by refl ev (inverse (Id (Equiv X X) idE idE) (refl idE) e2 (hE idE idE (refl idE) e2))
        = refl b by refl (refl b) ∎)

{` The loop type of Empty in the universe is a set (it is Equiv Empty Empty),
   while the universe is not a groupoid: so "A is a groupoid iff a = a is a
   set" needs A connected (xca:defgroup). `}
def universe_empty_loops_set : isSet (Id Type Empty Empty)
  ≔ hlevel_two_to_set (Id Type Empty Empty)
      (hlevel_equiv (suc. (suc. zero.)) (Equiv Empty Empty) (Id Type Empty Empty)
        (canonical_inverse_equiv (Id Type Empty Empty) (Equiv Empty Empty) (univalence_equiv Empty Empty))
        (set_to_hlevel_two (Equiv Empty Empty) (equivalences_set Empty Empty empty_set)))

def loops_set_not_groupoid_of_circle (C : CircleSignature)
  : Product (isSet (Id Type Empty Empty)) (isGroupoid Type → Empty)
  ≔ (universe_empty_loops_set, universe_not_groupoid_of_circle C)

{` The same argument shows that the self-equivalences of a circle do not form
   a set; hence the connected type U_(S¹) (the component of the universe at the
   circle) has a loop type that is not a set: Aut_U(S¹) is an ∞-group that is
   not a group (group.tex 845, sec:inftygps). `}
def circle_automorphisms_not_set (C : CircleSignature) (hE : isSet (Equiv (C .carrier) (C .carrier))) : Empty
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let idE ≔ identity_equiv X in
    let c ≔ circle_central_loop C in
    let e2 : Id (Equiv X X) idE idE ≔ equiv_path X X idE idE (funext X (_ ↦ X) (identity X) (identity X) c) in
    let ev : Id (Equiv X X) idE idE → Id X b b ≔ r ↦ happly X (_ ↦ X) (identity X) (identity X) (r .map) b in
    circle_loop_not_refl C
      (calc
        C .loop = c b by inverse (Id X b b) (c b) (C .loop) (circle_central_loop_base C)
        = ev e2 by funext_beta X (_ ↦ X) (identity X) (identity X) c b
        = ev (refl idE) by refl ev (inverse (Id (Equiv X X) idE idE) (refl idE) e2 (hE idE idE (refl idE) e2))
        = refl b by refl (refl b) ∎)

def universe_circle_component_loops_not_set (C : CircleSignature)
  (h : isSet (Loop (infty_BG (infty_automorphism_group Type (C .carrier))))) : Empty
  ≔ circle_automorphisms_not_set C
      (hlevel_two_to_set (Equiv (C .carrier) (C .carrier))
        (hlevel_equiv (suc. (suc. zero.)) (Loop (infty_BG (infty_automorphism_group Type (C .carrier))))
          (Equiv (C .carrier) (C .carrier)) (infty_universe_automorphisms_equiv (C .carrier))
          (set_to_hlevel_two (Loop (infty_BG (infty_automorphism_group Type (C .carrier)))) h)))
