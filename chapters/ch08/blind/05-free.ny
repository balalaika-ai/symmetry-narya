{` Blind statements for chapter 8 (congp.tex), section "Free groups". BFG_S is a higher inductive
   type; it is a signature record with the induction principle and its computation rules as one Σ-path. `}
export "04-wedge"
export "../../../src/485-infinity-groups"

{` def:bfree. Data of the induction principle: a : A(base) and l_s : a =_{loop_s} a for every s. `}
def BlindFreeBoundary (S : Type) (B : Type) (base : B) (loop : S → Id B base base) (A : B → Type) : Type
  ≔ Σ (A base) (a ↦ (s : S) → Id A (loop s) a a)

def blind_free_evaluate (S : Type) (B : Type) (base : B) (loop : S → Id B base base) (A : B → Type)
  (f : (x : B) → A x) : BlindFreeBoundary S B base loop A
  ≔ (f base, s ↦ refl f (loop s))

def BlindFreeGroupSignature (S : SetTypes) : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop : S .fst → Id carrier base base,
  induction : (A : carrier → Type) (d : BlindFreeBoundary (S .fst) carrier base loop A)
    → Σ ((x : carrier) → A x) (f ↦
        Id (BlindFreeBoundary (S .fst) carrier base loop A) (blind_free_evaluate (S .fst) carrier base loop A f) d))

def blind_free_pointed (S : SetTypes) (F : BlindFreeGroupSignature S) : Pointed ≔ (F .carrier, F .base)

{` BFG_S is connected (induction into the propositions ‖base = x‖). `}
def blind_free_based_paths (S : SetTypes) (F : BlindFreeGroupSignature S)
  : (x : F .carrier) → Mere (Id (F .carrier) (F .base) x)
  ≔ F .induction (x ↦ Mere (Id (F .carrier) (F .base) x))
      (mere (Id (F .carrier) (F .base) (F .base)) (refl (F .base)),
       s ↦ prop_family_pathover (F .carrier) (x ↦ Mere (Id (F .carrier) (F .base) x))
             (x ↦ mere_isprop (Id (F .carrier) (F .base) x)) (F .base) (F .base) (F .loop s)
             (mere (Id (F .carrier) (F .base) (F .base)) (refl (F .base)))
             (mere (Id (F .carrier) (F .base) (F .base)) (refl (F .base)))) .fst

def blind_free_connected (S : SetTypes) (F : BlindFreeGroupSignature S) : Connected (F .carrier)
  ≔ equiv_inverse_map (Connected (F .carrier)) ((x : F .carrier) → Mere (Id (F .carrier) (F .base) x))
      (connected_based_equiv (F .carrier) (F .base)) (blind_free_based_paths S F)

{` FG_S ≔ mkgroup(BFG_S, base): a priori an ∞-group; a group when BFG_S is a groupoid. `}
def blind_free_infty_group (S : SetTypes) (F : BlindFreeGroupSignature S) : InftyGroup
  ≔ mk_infty_group (F .carrier, F .base, blind_free_connected S F)

def blind_free_group (S : SetTypes) (F : BlindFreeGroupSignature S) (hF : isGroupoid (F .carrier)) : Group
  ≔ mkgroup (F .carrier, F .base, blind_free_connected S F, hF)

{` congp.tex:782. Signed letters S̃ ≔ S + S and complementation (swap). The claims: S̃ is a decidable
   set and complementation is an involution and an equivalence. `}
def BlindSigned (S : Type) : Type ≔ Sum S S

def blind_complement (S : Type) : Sum S S → Sum S S ≔ [ inl. a ↦ inr. a | inr. a ↦ inl. a ]

def blind_signed_claims : Type
  ≔ (S : Type) (dS : DecidableSet S)
    → Product (DecidableSet (Sum S S))
        (Product ((x : Sum S S) → Id (Sum S S) (blind_complement S (blind_complement S x)) x)
                 (BookIsEquiv (Sum S S) (Sum S S) (blind_complement S)))

{` congp.tex:811. Reduced words (no consecutive complementary letters), one deletion step,
   its reflexive-transitive closure, and the specification of ρ_S. `}
def BlindIsReducedFrom (S : Type) (x : Sum S S) (w : List (Sum S S)) : Type
  ≔ match w [
    | nil. ↦ Unit
    | cons. y w' ↦ Product (Not (Id (Sum S S) y (blind_complement S x))) (BlindIsReducedFrom S y w') ]

def BlindIsReduced (S : Type) (w : List (Sum S S)) : Type
  ≔ match w [ nil. ↦ Unit | cons. x w' ↦ BlindIsReducedFrom S x w' ]

def BlindDeleteStep (S : Type) (u v : List (Sum S S)) : Type
  ≔ Σ (List (Sum S S)) (l ↦ Σ (List (Sum S S)) (r ↦ Σ (Sum S S) (x ↦
      Product (Id (List (Sum S S)) u (append (Sum S S) l (cons. x (cons. (blind_complement S x) r))))
              (Id (List (Sum S S)) v (append (Sum S S) l r)))))

def BlindReducesIn (S : Type) (k : Nat) (u w : List (Sum S S)) : Type
  ≔ match k [
    | zero. ↦ Id (List (Sum S S)) u w
    | suc. j ↦ Σ (List (Sum S S)) (v ↦ Product (BlindDeleteStep S u v) (BlindReducesIn S j v w)) ]

def BlindReducesTo (S : Type) (u w : List (Sum S S)) : Type ≔ Σ Nat (k ↦ BlindReducesIn S k u w)

def BlindReductionSpec (S : Type) (rho : List (Sum S S) → List (Sum S S)) : Type
  ≔ (w : List (Sum S S)) → Product (BlindIsReduced S (rho w)) (BlindReducesTo S w (rho w))

{` ρ_S by nested induction on words (decidable equality of S̃ decides whether to cancel). `}
def blind_signed_decidable (S : Type) (dS : DecidableSet S) : DecidableEquality (Sum S S)
  ≔ sum_decidable_equality S S (decidable_set_equality S dS) (decidable_set_equality S dS)

def blind_reduce_choose (S : Type) (x y : Sum S S) (r : List (Sum S S))
  (d : Decidable (Id (Sum S S) y (blind_complement S x))) : List (Sum S S)
  ≔ match d [ inl. _ ↦ r | inr. _ ↦ cons. x (cons. y r) ]

def blind_reduce_cons (S : Type) (dS : DecidableSet S) (x : Sum S S) (r : List (Sum S S)) : List (Sum S S)
  ≔ match r [
    | nil. ↦ cons. x nil.
    | cons. y r' ↦ blind_reduce_choose S x y r' (blind_signed_decidable S dS y (blind_complement S x)) ]

def blind_rho (S : Type) (dS : DecidableSet S) (w : List (Sum S S)) : List (Sum S S)
  ≔ match w [ nil. ↦ nil. | cons. x w' ↦ blind_reduce_cons S dS x (blind_rho S dS w') ]

{` congp.tex:819. The nested-induction ρ_S meets the definition: ρ_S(w) is reduced and is obtained
   from w by deleting complementary pairs. `}
def blind_xca_rho : Type ≔ (S : Type) (dS : DecidableSet S) → BlindReductionSpec S (blind_rho S dS)

{` congp.tex:824. R_S ≔ image of ρ_S, D_S ≔ ρ_S⁻¹(ε). `}
def BlindReducedWords (S : Type) (dS : DecidableSet S) : Type
  ≔ Image (List (Sum S S)) (List (Sum S S)) (blind_rho S dS)

def BlindDyckWords (S : Type) (dS : DecidableSet S) : Type
  ≔ BookFiber (List (Sum S S)) (List (Sum S S)) (blind_rho S dS) nil.

{` congp.tex:842. u ~ v iff ρ u = ρ v is an equivalence relation and S̃*/~ ≃ R_S, [u] ↦ ρ_S(u). `}
def blind_rem_reduction_quotient : Type
  ≔ (S : Type) (dS : DecidableSet S)
    → Σ (EquivalenceRelation (List (Sum S S))) (R ↦
        Product ((u v : List (Sum S S))
                  → Product (Rel (List (Sum S S)) R u v → Id (List (Sum S S)) (blind_rho S dS u) (blind_rho S dS v))
                            (Id (List (Sum S S)) (blind_rho S dS u) (blind_rho S dS v) → Rel (List (Sum S S)) R u v))
          (Σ (BookEquiv (Quotient (List (Sum S S)) R) (BlindReducedWords S dS)) (e ↦
             (u : List (Sum S S))
             → Id (List (Sum S S)) (e .map (quotient_class (List (Sum S S)) R u) .fst) (blind_rho S dS u))))

{` congp.tex:857. ⟦ε⟧ ≔ refl, ⟦a w⟧ ≔ loop_a · ⟦w⟧, ⟦A w⟧ ≔ loop_a⁻¹ · ⟦w⟧ (⟦w⟧ first). `}
def blind_interp (S : SetTypes) (F : BlindFreeGroupSignature S) (w : List (Sum (S .fst) (S .fst)))
  : Id (F .carrier) (F .base) (F .base)
  ≔ match w [
    | nil. ↦ refl (F .base)
    | cons. (inl. a) w' ↦ concat (F .carrier) (F .base) (F .base) (F .base) (blind_interp S F w') (F .loop a)
    | cons. (inr. a) w' ↦ concat (F .carrier) (F .base) (F .base) (F .base) (blind_interp S F w')
        (inverse (F .carrier) (F .base) (F .base) (F .loop a)) ]

def blind_decidable_settype (S : Type) (dS : DecidableSet S) : SetTypes ≔ (S, decidable_set_is_set S dS)

{` thm:free-group-elements. ⟦−⟧ restricted to R_S is an equivalence R_S ≃ UFG_S. `}
def blind_thm_free_group_elements : Type
  ≔ (S : Type) (dS : DecidableSet S) (F : BlindFreeGroupSignature (blind_decidable_settype S dS))
    → BookIsEquiv (BlindReducedWords S dS) (Id (F .carrier) (F .base) (F .base))
        (r ↦ blind_interp (blind_decidable_settype S dS) F (r .fst))

{` congp.tex:929. R_1 ≃ Z sending ε to 0, with s_* (w ↦ ρ(* w)) corresponding to the successor. `}
def blind_fin_one : Type ≔ Fin (suc. zero.)
def blind_fin_one_dset : DecidableSet blind_fin_one ≔ hedberg blind_fin_one (fin_decidable_equality (suc. zero.))
def blind_fin_one_star : blind_fin_one ≔ inr. star.

def blind_rs_empty (S : Type) (dS : DecidableSet S) : BlindReducedWords S dS
  ≔ (nil., mere (BookFiber (List (Sum S S)) (List (Sum S S)) (blind_rho S dS) nil.) (nil., refl (nil. : List (Sum S S))))

def blind_rs_succ (S : Type) (dS : DecidableSet S) (a : S) (r : BlindReducedWords S dS) : BlindReducedWords S dS
  ≔ (blind_rho S dS (cons. (inl. a) (r .fst)),
     mere (BookFiber (List (Sum S S)) (List (Sum S S)) (blind_rho S dS) (blind_rho S dS (cons. (inl. a) (r .fst))))
       (cons. (inl. a) (r .fst), refl (blind_rho S dS (cons. (inl. a) (r .fst)))))

def blind_xca_reduced_one_integers : Type
  ≔ Σ (BookEquiv (BlindReducedWords blind_fin_one blind_fin_one_dset) Int) (e ↦
      Product (Id Int (e .map (blind_rs_empty blind_fin_one blind_fin_one_dset)) int_zero)
        ((r : BlindReducedWords blind_fin_one blind_fin_one_dset)
         → Id Int (e .map (blind_rs_succ blind_fin_one blind_fin_one_dset blind_fin_one_star r)) (int_succ (e .map r))))

{` congp.tex:937 (1). FG_{n ⊔ 1} ≃ FG_n ∨ Z as pointed types (classifying types), for each n. `}
def blind_xca_free_wedge_step : Type
  ≔ (n : Nat) (C : CircleSignature)
    (F' : BlindFreeGroupSignature (Sum (Fin n) Unit, fin_set (suc. n)))
    (F : BlindFreeGroupSignature (Fin n, fin_set n))
    (W : BlindWedge (blind_free_pointed (Fin n, fin_set n) F) (circle_pointed C))
    → BookPointedEquiv (blind_free_pointed (Sum (Fin n) Unit, fin_set (suc. n)) F')
        (blind_wedge_pointed (blind_free_pointed (Fin n, fin_set n) F) (circle_pointed C) W)

{` congp.tex:937 (2). Left-nested wedges of m+1 circles: stage 0 is S¹, stage k+1 is (stage k) ∨ S¹
   (a wedge structure chosen at each stage). FG_{m+1} = ((Z ∨ Z) ∨ ⋯) ∨ Z. The case n = 0 (no copies)
   is not stated. `}
def BlindCircleTower (C : CircleSignature) (m : Nat) : Σ Type (D ↦ D → Pointed)
  ≔ match m [
    | zero. ↦ (Unit, _ ↦ circle_pointed C)
    | suc. k ↦ (Σ (BlindCircleTower C k .fst) (t ↦ BlindWedge (BlindCircleTower C k .snd t) (circle_pointed C)),
                u ↦ blind_wedge_pointed (BlindCircleTower C k .snd (u .fst)) (circle_pointed C) (u .snd)) ]

def blind_xca_free_iterated_wedge : Type
  ≔ (C : CircleSignature) (m : Nat) (F : BlindFreeGroupSignature (Fin (suc. m), fin_set (suc. m)))
    (t : BlindCircleTower C m .fst)
    → BookPointedEquiv (blind_free_pointed (Fin (suc. m), fin_set (suc. m)) F) (BlindCircleTower C m .snd t)
