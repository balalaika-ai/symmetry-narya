{` Blind statements for chapter 12 (abelian.tex), sec:abel-groups-simply. `}
export "02-universal-cover"

{` B²G ≔ U_(BG÷)<1> = Σ_{X:U} ‖BG÷ = X‖₀, pointed at (BG÷, |refl|₀) (proof of thm:abelian-groups-weq-sc2types).
   The book's universe-size footnote does not arise: Narya's Type contains Σ (X : Type) …. Defined for every group;
   the book only uses it for abelian G. `}
def BlindBB (G : Group) : Pointed ≔ blind_univ_cover_pointed Type (BG G .carrier)

{` Pointed simply connected 2-types, as in the statement: simply connected pointed types whose carrier is a 2-type
   (HLevel 4 = book level 2). `}
def BlindSimplyConnectedTwoTypes : Type
  ≔ Σ Pointed (X ↦ Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))

{` U_*^{=2} as printed in the proof: Σ_{(A,a):U_*} isconn(A) × isconn(a = a) × isgrpd(a = a). `}
def BlindUUsc2 : Type
  ≔ Σ Pointed (X ↦ Product (Connected (X .carrier)) (Product (Connected (Loop X)) (isGroupoid (Loop X))))

{` thm:abelian-groups-weq-sc2types (abelian.tex:409). AbGroup ≃ pointed simply connected 2-types. `}
def blind_abelian_groups_weq_sc2types : Type ≔ BookEquiv AbelianGroup BlindSimplyConnectedTwoTypes

{` The same with the codomain U_*^{=2} exactly as printed in the proof. `}
def blind_abelian_groups_weq_sc2types_proof_codomain : Type ≔ BookEquiv AbelianGroup BlindUUsc2
