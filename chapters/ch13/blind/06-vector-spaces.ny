import "01-abstract-rings"
import "05-fields"

{` Blind statements, chapter 13 (fields.tex), section "vector spaces".
   K : BlindField; its carrier is K .fst .add .carrier. The abelian group
   V is an abstract group with IsAbstractAbelian. `}

{` Bilinearity of the scalar multiplication K × V → V: additive in each
   argument, (a+b)v = av + bv and a(v+w) = av + aw. `}
def BlindScalarBilinear (K : BlindField) (V : AbstractGroup)
  (smul : Product (K .fst .add .carrier) (V .carrier) → V .carrier) : Type
  ≔ Product
      ((a b : K .fst .add .carrier) (v : V .carrier) →
         Id (V .carrier) (smul (K .fst .add .mul a b, v)) (V .mul (smul (a, v)) (smul (b, v))))
      ((a : K .fst .add .carrier) (v w : V .carrier) →
         Id (V .carrier) (smul (a, V .mul v w)) (V .mul (smul (a, v)) (smul (a, w))))

{` A K-vector space: an abelian group V with a bilinear scalar
   multiplication K × V → V such that 1v = v and (a·b)v = a(bv). `}
def BlindVectorSpace (K : BlindField) : Type ≔ sig (
  vec : AbstractGroup,
  abelian : IsAbstractAbelian vec,
  smul : Product (K .fst .add .carrier) (vec .carrier) → vec .carrier,
  bilinear : BlindScalarBilinear K vec smul,
  smul_one : (v : vec .carrier) → Id (vec .carrier) (smul (K .fst .one, v)) v,
  smul_mul : (a b : K .fst .add .carrier) (v : vec .carrier) →
    Id (vec .carrier) (smul (K .fst .mul a b, v)) (smul (a, smul (b, v))))

{` A K-linear map V → W: a group homomorphism h preserving scalar
   multiplication, h(av) = a h(v) (the book writes f for h, a typo). `}
def BlindLinearMap (K : BlindField) (V W : BlindVectorSpace K) : Type
  ≔ Σ (AbstractHom (V .vec) (W .vec)) (h ↦
      (a : K .fst .add .carrier) (v : V .vec .carrier) →
        Id (W .vec .carrier) (h .fst (V .smul (a, v))) (W .smul (a, h .fst v)))

{` The free K-vector space on a set S: (V, i : S → V) is homotopy initial,
   i.e. for every K-vector space W and j : S → W the type of linear maps
   h : V → W with h(i(s)) = j(s) for all s is contractible. `}
def BlindIsFreeVectorSpace (K : BlindField) (S : SetTypes) (V : BlindVectorSpace K)
  (i : S .fst → V .vec .carrier) : Type
  ≔ (W : BlindVectorSpace K) (j : S .fst → W .vec .carrier) →
      BookIsContr (Σ (BlindLinearMap K V W) (h ↦
        (s : S .fst) → Id (W .vec .carrier) (h .fst .fst (i s)) (j s)))

def BlindFreeVectorSpace (K : BlindField) (S : SetTypes) : Type
  ≔ Σ (BlindVectorSpace K) (V ↦
      Σ (S .fst → V .vec .carrier) (i ↦ BlindIsFreeVectorSpace K S V i))

{` An n-dimensional K-vector space: a free K-vector space on Fin(n). `}
def BlindNDimVectorSpace (K : BlindField) (n : Nat) : Type
  ≔ BlindFreeVectorSpace K (Fin n, fin_set n)
