export "10-hom-group"
export "01-abstract-rings"

{` Blind statements, chapter 13 (fields.tex), sec:concrings: def:ring, the
   example of the integers, xca:Rconcring->URabstring. The group ℤ is the
   circle group of any CircleSignature C. `}

def blind_Z (C : CircleSignature) : Group ≔ circle_group C

{` def:ring, data: an abelian group R, 1_R : Hom(ℤ, R) and
   μ : Hom(R, grpHom(R, R)). `}
def BlindConcRingData (C : CircleSignature) : Type ≔ sig (
  grp : AbelianGroup,
  one : GroupHom (blind_Z C) (grp .fst),
  mu : GroupHom (grp .fst) (blind_grphom (grp .fst) grp))

{` The map Bμ∘1_R as a symmetry-level function: USym(μ ∘ 1_R)(g), read
   through ptw_* and ev ∘ - (lem:grpHomOK chain, pointed level) as a
   pointed map BR →* BR. `}
def blind_concring_unit_map (C : CircleSignature) (D : BlindConcRingData C) (g : USym (blind_Z C))
  : BookPointedMap (BG (D .grp .fst)) (BG (D .grp .fst))
  ≔ let R ≔ D .grp .fst in
    book_pointed_compose (BG R) (Omega (BB R)) (BG R)
      (blind_ptw_loops (BG R) (BB R) .map
        (usym_hom (blind_Z C) (blind_grphom R (D .grp))
          (group_hom_compose (blind_Z C) R (blind_grphom R (D .grp)) (D .one) (D .mu)) g .fst))
      (bb_loops_evaluation_pointed R)

{` def:ring, ring:unit-laws, the one printed (left) unit law
   ev ∘ (USym(μ ∘ 1_R)(loop)) = B id_R, read via the footnote:
   USym Hom(R, R) ≃ (BR →* Ω BB R), then postcomposition with ev gives
   BR →* BR. The book marks it "≈ TBD"; the other unit law, the
   associative law (ring:assoc-law) and commutativity are TBD in the book
   and are not formalized. `}
def BlindConcRingUnitLaw (C : CircleSignature) (D : BlindConcRingData C) : Type
  ≔ Id (BookPointedMap (BG (D .grp .fst)) (BG (D .grp .fst)))
      (blind_concring_unit_map C D (C .loop)) (book_pointed_identity (BG (D .grp .fst)))

{` def:ring: non-trivial if 1_R is not trivial, i.e. not classified by the
   constant map at the shape (pointed by refl). `}
def BlindConcRingNonTrivial (C : CircleSignature) (D : BlindConcRingData C) : Type
  ≔ Not (Id (GroupHom (blind_Z C) (D .grp .fst)) (D .one)
      (mkhom (blind_Z C) (D .grp .fst) (book_pointed_constant (BG (blind_Z C)) (BG (D .grp .fst)))))

{` Example (ring of the integers), footnote: s : id_S¹ = id_S¹ by function
   extensionality from s(base) ≔ loop, s(loop) ≔ ! (the loop condition is a
   proposition; it is proved here since the definition needs it). `}
def blind_Zring_loop_case (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base))
      (transport (C .carrier) (x ↦ Id (C .carrier) x x) (C .base) (C .base) (C .loop) (C .loop)) (C .loop)
  ≔ let S ≔ C .carrier in let b ≔ C .base in let r ≔ C .loop in
    concat (Id S b b) (transport S (x ↦ Id S x x) b b r r) (loop_conjugate S b b r r) r
      (loop_transport_conjugate S b b r r)
      (concat (Id S b b) (loop_conjugate S b b r r)
        (concat S b b b (inverse S b b r) (concat S b b b (inverse S b b (inverse S b b r)) r)) r
        (refl ((t : Id S b b) ↦ concat S b b b (inverse S b b r) (concat S b b b t r))
          (inverse (Id S b b) (inverse S b b (inverse S b b r)) r (inverse_inverse S b b r)))
        (concat_left_right_inverse S b b b (inverse S b b r) r))

def blind_Zring_s_fun (C : CircleSignature) : (x : C .carrier) → Id (C .carrier) x x
  ≔ C .induction (x ↦ Id (C .carrier) x x)
      (C .loop, pathover_of_eq (C .carrier) (x ↦ Id (C .carrier) x x) (C .base) (C .base) (C .loop)
        (C .loop) (C .loop) (blind_Zring_loop_case C)) .fst

def blind_Zring_s (C : CircleSignature) : Id (C .carrier → C .carrier) (identity (C .carrier)) (identity (C .carrier))
  ≔ funext (C .carrier) (_ ↦ C .carrier) (identity (C .carrier)) (identity (C .carrier)) (blind_Zring_s_fun C)

{` e_z(base) ≔ z, e_z(loop) ≔ s(z). `}
def blind_Zring_e (C : CircleSignature) (z : C .carrier) : C .carrier → C .carrier
  ≔ circle_rec C (C .carrier) (z, blind_Zring_s_fun C z)

def blind_Zring_e_beta (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier) (blind_Zring_e C z (C .base)) z
  ≔ circle_rec_beta C (C .carrier) (z, blind_Zring_s_fun C z) .fst

{` Footnote claims: e_base = id_S¹ and e_loop = s (transported along that
   identification). `}
def blind_exa_Zring_e_base_loop : Type
  ≔ (C : CircleSignature)
    → Σ (Id (C .carrier → C .carrier) (blind_Zring_e C (C .base)) (identity (C .carrier)))
        (ι ↦ Id (Id (C .carrier → C .carrier) (identity (C .carrier)) (identity (C .carrier)))
          (concat (C .carrier → C .carrier) (identity (C .carrier)) (blind_Zring_e C (C .base)) (identity (C .carrier))
            (inverse (C .carrier → C .carrier) (blind_Zring_e C (C .base)) (identity (C .carrier)) ι)
            (concat (C .carrier → C .carrier) (blind_Zring_e C (C .base)) (blind_Zring_e C (C .base))
              (identity (C .carrier)) (refl (blind_Zring_e C) (C .loop)) ι))
          (blind_Zring_s C))

{` Footnote claim: e_p(base) = p for p : base = z (e_w(base) ≡ w holds up to
   the beta path, which conjugates). `}
def blind_exa_Zring_e_point : Type
  ≔ (C : CircleSignature) (z : C .carrier) (p : Id (C .carrier) (C .base) z)
    → Id (Id (C .carrier) (C .base) z)
        (concat (C .carrier) (C .base) (blind_Zring_e C (C .base) (C .base)) z
          (inverse (C .carrier) (blind_Zring_e C (C .base) (C .base)) (C .base) (blind_Zring_e_beta C (C .base)))
          (concat (C .carrier) (blind_Zring_e C (C .base) (C .base)) (blind_Zring_e C z (C .base)) z
            (refl ((w : C .carrier) ↦ blind_Zring_e C w (C .base)) p) (blind_Zring_e_beta C z)))
        p

{` The ring of the integers: 1_ℤ ≔ id_ℤ is non-trivial. `}
def blind_exa_Zring_one_nontrivial : Type
  ≔ (C : CircleSignature)
    → Not (Id (GroupHom (blind_Z C) (blind_Z C)) (group_hom_id (blind_Z C))
        (mkhom (blind_Z C) (blind_Z C) (book_pointed_constant (BG (blind_Z C)) (BG (blind_Z C)))))

{` The ring of the integers, μ and its computation. The book's
   Bμ(z) ≔ ve_{BBℤ}(sh, (e_z, !)) is not constructed here (the example is
   unfinished: "Almost there!"); the statement is existential: there is
   μ : Hom(ℤ, grpHom(ℤ, ℤ)) satisfying the printed unit law with 1_ℤ = id and
   with Bμ(loop^j, loop^k) = s^{jk}, read after evaluation at base
   (Ω(ev)), where s^{jk} becomes loop^{jk}. `}
def blind_exa_Zring_data (C : CircleSignature)
  (μ : GroupHom (blind_Z C) (blind_grphom (blind_Z C) (circle_abelian_group C)))
  : BlindConcRingData C
  ≔ (circle_abelian_group C, group_hom_id (blind_Z C), μ)

def blind_exa_Zring_mu : Type
  ≔ (C : CircleSignature)
    → Σ (GroupHom (blind_Z C) (blind_grphom (blind_Z C) (circle_abelian_group C)))
        (μ ↦ Product (BlindConcRingUnitLaw C (blind_exa_Zring_data C μ))
          ((j k : Int)
            → Id (USym (blind_Z C))
                (loops_map (Omega (BB (blind_Z C))) (BG (blind_Z C)) (bb_loops_evaluation_pointed (blind_Z C))
                  (loops_map (BG (blind_Z C)) (Omega (BB (blind_Z C)))
                    (blind_ptw_loops (BG (blind_Z C)) (BB (blind_Z C)) .map
                      (usym_hom (blind_Z C) (blind_grphom (blind_Z C) (circle_abelian_group C)) μ
                        (loop_power (C .carrier) (C .base) (C .loop) j) .fst))
                    (loop_power (C .carrier) (C .base) (C .loop) k)))
                (loop_power (C .carrier) (C .base) (C .loop) (int_mul j k))))

{` xca:Rconcring->URabstring: for a ring (R, 1_R, μ), USym R is an abstract
   ring with additive group abstr(R), unit USym(1_R)(loop) and multiplication
   g·h ≔ (abstr-chain of USym μ (g))(h) (USym μ(g) : USym grpHom(R, R) read
   as an abstract endomorphism by lem:grpHomOK). Only the data and the
   printed unit law are available as hypotheses (the other ring laws are
   TBD in the book). `}
def blind_concring_mul (C : CircleSignature) (D : BlindConcRingData C) (g h : USym (D .grp .fst)) : USym (D .grp .fst)
  ≔ blind_grphom_chain (D .grp .fst) (D .grp) (usym_hom (D .grp .fst) (blind_grphom (D .grp .fst) (D .grp)) (D .mu) g) .fst h

def blind_xca_Rconcring_URabstring : Type
  ≔ (C : CircleSignature) (D : BlindConcRingData C) → BlindConcRingUnitLaw C D
    → let R ≔ D .grp .fst in
      Product
        (MonoidLaws (USym R) (usym_hom (blind_Z C) R (D .one) (C .loop)) (blind_concring_mul C D))
        (BlindDistrLaws (USym R) (blind_concring_mul C D) (usym_mul R))
