import "../../../src/1707-blass-two"
import "../../../src/1725-blass-cyclic-choice"
import "../../../src/404-group-examples"
import "01-lpo-topology"
import "02-choice-principles"
import "03-choice-cohomology"
import "bridge-02-choice-principles"

{` Bridges for choicefin.tex: choice versus triviality of ‖X → BG‖₀
   (lem:ac-impl-triv-coh-sets, the ∞-group xca, thm:Blass-1, thm:Blass-2,
   Blass's Theorem 6). `}

def bridge_def_trivial_h1 (X : Type) (G : Group)
  : Id Type (BlindTrivialH1 X G) (BookIsContr (SetTrunc (X → BG G .carrier)))
  ≔ refl (BookIsContr (SetTrunc (X → BG G .carrier)))

def bridge_def_group_torsors_trivial (X : Type)
  : Id Type ((G : Group) → BlindTrivialH1 X G) (GroupTorsorsTrivial X)
  ≔ refl (GroupTorsorsTrivial X)

def bridge_lemma_local_ac_trivial_h1 : blind_lemma_local_ac_trivial_h1
  ≔ X hX ac G ↦ local_choice_torsors_trivial X hX ac G

def bridge_xca_local_ac_infty_trivial_h1 : blind_xca_local_ac_infty_trivial_h1
  ≔ X hX ac G ↦ untruncated_local_choice_torsors_trivial X hX ac
      (G .classifying .carrier) (G .classifying .point) (G .classifying .connected)

{` thm:Blass-1: GAP for the literal blind reading (S arbitrary). Ours needs
   the component of a NON-EMPTY set S, as in the printed proof. The two
   variants below derive the blind statement from ours under either extra
   hypothesis ‖S‖ or ‖X‖ (with ‖X‖, ‖S‖ follows from ‖P x‖). Without them
   the blind statement asks for ‖X → S‖ from X → ‖S‖, i.e. choice over the
   proposition ‖X‖ for the constant family S, which the printed proof does
   not provide. `}
def BridgeBBlassOneNonemptyComponent : Type
  ≔ (X : Type) → isSet X → ((G : Group) → BlindTrivialH1 X G)
    → (P : X → SetTypes) → ((x : X) → Mere (P x .fst))
    → (S : SetTypes) → Mere (S .fst) → (h : X → NativeComponent SetTypes S)
    → Id (X → SetTypes) P (x ↦ h x .fst)
    → Mere ((x : X) → P x .fst)

def bridge_blass_one_nonempty_component : BridgeBBlassOneNonemptyComponent
  ≔ X hX H P ne S neS h e ↦
    transport (X → SetTypes) (Q ↦ Mere ((x : X) → Q x .fst)) (x ↦ h x .fst) P
      (inverse (X → SetTypes) P (x ↦ h x .fst) e)
      (blass_component_sections X hX H S neS h)

def BridgeBBlassOneInhabitedBase : Type
  ≔ (X : Type) → isSet X → ((G : Group) → BlindTrivialH1 X G)
    → (P : X → SetTypes) → ((x : X) → Mere (P x .fst))
    → (S : SetTypes) (h : X → NativeComponent SetTypes S)
    → Id (X → SetTypes) P (x ↦ h x .fst)
    → Mere X
    → Mere ((x : X) → P x .fst)

def bridge_blass_one_inhabited_base : BridgeBBlassOneInhabitedBase
  ≔ X hX H P ne S h e inh ↦
    blass_one_inhabited X hX H P ne inh
      (mere (Σ SetTypes (S' ↦ Σ (X → NativeComponent SetTypes S') (h' ↦ Id (X → SetTypes) (x ↦ h' x .fst) P)))
        (S, (h, inverse (X → SetTypes) P (x ↦ h x .fst) e)))

{` Converse direction (bonus): the blind reading implies ours. `}
def bridge_blass_one_converse (b : blind_blass_one) (X : Type) (hX : isSet X) (H : GroupTorsorsTrivial X)
  (P : X → SetTypes) (ne : (x : X) → Mere (P x .fst)) (fac : Mere (FactorsThroughNonemptyComponent X P))
  : Mere ((x : X) → P x .fst)
  ≔ mere_rec (FactorsThroughNonemptyComponent X P) (Mere ((x : X) → P x .fst)) (mere_isprop ((x : X) → P x .fst))
      (w ↦ b X hX H P ne (w .fst) (w .snd .snd .fst)
        (inverse (X → SetTypes) (x ↦ w .snd .snd .fst x .fst) P (w .snd .snd .snd)))
      fac

{` thm:Blass-1, formal reduction of the gap. The literal blind statement is
   equivalent to BlassOneConstantChoice: for a set X with ‖X → BG‖₀
   contractible for all groups G, and any set S, X → ‖S‖ implies ‖X → S‖
   (the converse of lem:ac-impl-triv-coh-sets for the constant families
   X × S → X, a special case of the converse the book calls open after
   thm:Blass-2). It holds when ‖X‖ is decided (below), when S or X is merely
   inhabited (above), and whenever X-AC holds; it is neither proved nor
   refuted here. `}
def BlassOneConstantChoice : Type
  ≔ (X : Type) → isSet X → GroupTorsorsTrivial X → (S : SetTypes) → (X → Mere (S .fst)) → Mere (X → S .fst)

def bridge_blass_one_component_constant_choice (cc : BlassOneConstantChoice)
  (X : Type) (hX : isSet X) (H : GroupTorsorsTrivial X) (S : SetTypes) (h : X → NativeComponent SetTypes S)
  (ne : (x : X) → Mere (h x .fst .fst)) : Mere ((x : X) → h x .fst .fst)
  ≔ let BAut ≔ NativeComponent SetTypes S in
    let sh ≔ component_point SetTypes S in
    mere_rec ((x : X) → Id BAut sh (h x)) (Mere ((x : X) → h x .fst .fst)) (mere_isprop ((x : X) → h x .fst .fst))
      (k ↦ trunc_map native_truncation (X → S .fst) ((x : X) → h x .fst .fst)
        (f x ↦ set_component_transport S (h x) (k x) (f x))
        (cc X hX H S (x ↦ trunc_map native_truncation (h x .fst .fst) (S .fst)
          (transport BAut (U ↦ U .fst .fst) (h x) sh (inverse BAut sh (h x) (k x))) (ne x))))
      (contractible_set_trunc_constant X BAut sh (H (automorphism_group SetTypes sets_groupoid S)) h)

def bridge_blass_one_from_constant_choice (cc : BlassOneConstantChoice) : blind_blass_one
  ≔ X hX H P ne S h e ↦
    transport (X → SetTypes) (Q ↦ ((x : X) → Mere (Q x .fst)) → Mere ((x : X) → Q x .fst))
      (x ↦ h x .fst) P (inverse (X → SetTypes) P (x ↦ h x .fst) e)
      (bridge_blass_one_component_constant_choice cc X hX H S h) ne

def bridge_blass_one_to_constant_choice (b : blind_blass_one) : BlassOneConstantChoice
  ≔ X hX H S ne ↦ b X hX H (_ ↦ S) ne S (_ ↦ component_point SetTypes S) (refl ((_ ↦ S) : X → SetTypes))

{` The blind statement when ‖X‖ is decided: the open case is exactly an
   undecided ‖X‖ with S not known to be inhabited. `}
def bridge_blass_one_decided_base (X : Type) (hX : isSet X) (H : (G : Group) → BlindTrivialH1 X G)
  (P : X → SetTypes) (ne : (x : X) → Mere (P x .fst))
  (S : SetTypes) (h : X → NativeComponent SetTypes S) (e : Id (X → SetTypes) P (x ↦ h x .fst))
  (d : Sum (Mere X) (Not X)) : Mere ((x : X) → P x .fst)
  ≔ match d [
  | inl. m ↦ bridge_blass_one_inhabited_base X hX H P ne S h e m
  | inr. nx ↦ mere ((x : X) → P x .fst) (x ↦ match nx x []) ]

{` thm:Blass-2. A decidable set (def:decidable-set) is a set with decidable equality. `}
def bridge_b_decidable_set_is_set (A : Type) (d : DecidableSet A) : isSet A ≔ x y ↦ d x y .fst

def bridge_b_decidable_set_eq (A : Type) (d : DecidableSet A) : DecidableEquality A ≔ x y ↦ d x y .snd

def bridge_blass_two : blind_blass_two
  ≔ X dX H P dP ne ↦
    blass_two X (bridge_b_decidable_set_is_set X dX) (bridge_b_decidable_set_eq X dX) H
      (x ↦ (P x, bridge_b_decidable_set_is_set (P x) (dP x)))
      (x ↦ bridge_b_decidable_set_eq (P x) (dP x)) ne

{` Blass's Theorem 6. The blind C_{k+1} = cyclic_group_fin k is identified
   with ours, cyclic_group (k+1) (BG = CycleComponent (k+1)), by module 404's
   cyclic_group_fin_path. `}
def bridge_b_cyclic_hypothesis
  (H : (X : Type) → isSet X → (k : Nat) → BlindTrivialH1 X (cyclic_group_fin k)) : CyclicTorsorsTrivial
  ≔ X k ↦ transport Group (G ↦ BookIsContr (SetTrunc (X .fst → BG G .carrier)))
      (cyclic_group_fin k) (cyclic_group (suc. k)) (cyclic_group_fin_path k) (H (X .fst) (X .snd) k)

def bridge_blass_cyclic : blind_blass_cyclic
  ≔ H n ↦ bridge_def_acn_from_ours n (blass_cyclic_choice (bridge_b_cyclic_hypothesis H) n)
