import "../../../src/485-infinity-groups"
import "02-choice-principles"

{` Blind statements for choicefin.tex: choice versus the triviality of
   ‖X → BG‖₀ ("H¹(X,G) is trivial"). BG G .carrier is the (unpointed)
   classifying type of a group G (chapter 4); maps X → BG are unpointed. `}

{` ‖X → BG‖₀ is contractible. `}
def BlindTrivialH1 (X : Type) (G : Group) : Type ≔ BookIsContr (SetTrunc (X → BG G .carrier))

{` lem:ac-impl-triv-coh-sets: if X-AC holds for a set X, then ‖X → BG‖₀ is
   contractible for any group G. `}
def blind_lemma_local_ac_trivial_h1 : Type
  ≔ (X : Type) → isSet X → BlindLocalAC X → (G : Group) → BlindTrivialH1 X G

{` xca: if X-AC_∞ holds for a set X, then ‖X → BG‖₀ is contractible for all
   ∞-groups G (def:inftygps: pointed connected types; BG = the carrier). `}
def blind_xca_local_ac_infty_trivial_h1 : Type
  ≔ (X : Type) → isSet X → BlindLocalACInfty X
    → (G : InftyGroup) → BookIsContr (SetTrunc (X → infty_BG G .carrier))

{` thm:Blass-1: X a set with ‖X → BG‖₀ contractible for all groups G. Then
   every family of non-empty sets P : X → Set that factors through a connected
   component Set_(S) = Σ(A : Set) ‖S = A‖ of Set (P = pr1 ∘ h) merely admits a
   section (an element of Π_x P(x)). `}
def blind_blass_one : Type
  ≔ (X : Type) → isSet X → ((G : Group) → BlindTrivialH1 X G)
    → (P : X → SetTypes) → ((x : X) → Mere (P x .fst))
    → (S : SetTypes) (h : X → NativeComponent SetTypes S)
    → Id (X → SetTypes) P (x ↦ h x .fst)
    → Mere ((x : X) → P x .fst)

{` thm:Blass-2: X a decidable set (def:decidable-set) with ‖X → BG‖₀
   contractible for all groups G. Then every family of non-empty decidable
   sets over X merely admits a section. `}
def blind_blass_two : Type
  ≔ (X : Type) → DecidableSet X → ((G : Group) → BlindTrivialH1 X G)
    → (P : X → Type) → ((x : X) → DecidableSet (P x)) → ((x : X) → Mere (P x))
    → Mere ((x : X) → P x)

{` Theorem (Blass, Theorem 6): if ‖X → BC_n‖₀ is contractible for all sets X
   and positive integers n, then AC(n) holds for all n. The positive integer
   n is written k+1 and C_{k+1} = cyclic_group_fin k = Aut_Cyc(Fin(k+1), s)
   (BC_n = Cyc_n). The conclusion ranges over all n : N (AC(0) holds
   trivially with the literal (eq:ac-impl) form). `}
def blind_blass_cyclic : Type
  ≔ ((X : Type) → isSet X → (k : Nat) → BlindTrivialH1 X (cyclic_group_fin k))
    → (n : Nat) → BlindACn n
