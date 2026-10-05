export "1301-fields"

{` Chapter 13 (fields.tex 1285-1301), section "vector spaces": vector
   spaces over a field, linear maps, free vector spaces on a set and
   n-dimensional vector spaces.

   Conventions. The book's "abelian group V" with elements v : V is read as
   an abelian abstract group (record fields carrier, zero, add, neg,
   add_laws, add_comm), equivalent to a concrete abelian group by
   thm:Groupsareidentitytypes (module 709). The scalar multiplication is
   curried, smul : K → V → V; "bilinear" is read as additive in each
   argument ((a+b)v = av + bv and a(v+w) = av + aw). The definition does not
   use that K is a field, so it is stated for modules over any abstract
   ring (RingModule) and VectorSpace K is RingModule over the ring of K. `}

def RingModule (R : AbstractRing) : Type ≔ sig (
  carrier : Type,
  zero : carrier,
  add : carrier → carrier → carrier,
  neg : carrier → carrier,
  add_laws : AbstractGroupLaws carrier zero add neg,
  add_comm : (v w : carrier) → Id carrier (add v w) (add w v),
  smul : R .carrier → carrier → carrier,
  smul_one : (v : carrier) → Id carrier (smul (R .one) v) v,
  smul_mul : (a b : R .carrier) (v : carrier) → Id carrier (smul (R .mul a b) v) (smul a (smul b v)),
  smul_add_scalar : (a b : R .carrier) (v : carrier) → Id carrier (smul (R .add a b) v) (add (smul a v) (smul b v)),
  smul_add_vector : (a : R .carrier) (v w : carrier) → Id carrier (smul a (add v w)) (add (smul a v) (smul a w)))

{` A K-vector space. `}
def VectorSpace (K : Field) : Type ≔ RingModule (K .fst)

def module_group (R : AbstractRing) (V : RingModule R) : AbstractGroup
  ≔ (V .carrier, V .zero, V .add, V .neg, V .add_laws)

def module_group_abelian (R : AbstractRing) (V : RingModule R) : IsAbstractAbelian (module_group R V)
  ≔ v w ↦ V .add_comm v w

def module_set (R : AbstractRing) (V : RingModule R) : isSet (V .carrier) ≔ V .add_laws .carrier_set

{` 0 v = 0 and a 0 = 0. `}
def smul_zero_scalar (R : AbstractRing) (V : RingModule R) (v : V .carrier)
  : Id (V .carrier) (V .smul (R .zero) v) (V .zero)
  ≔ let S ≔ V .carrier in
    ag_idempotent_unit (module_group R V) (V .smul (R .zero) v)
      (calc
         V .add (V .smul (R .zero) v) (V .smul (R .zero) v) = V .smul (R .add (R .zero) (R .zero)) v
           by inverse S (V .smul (R .add (R .zero) (R .zero)) v) (V .add (V .smul (R .zero) v) (V .smul (R .zero) v))
             (V .smul_add_scalar (R .zero) (R .zero) v)
         = V .smul (R .zero) v by refl ((x ↦ V .smul x v) : R .carrier → S) (R .add_laws .unit_right (R .zero)) ∎)

def smul_zero_vector (R : AbstractRing) (V : RingModule R) (a : R .carrier)
  : Id (V .carrier) (V .smul a (V .zero)) (V .zero)
  ≔ let S ≔ V .carrier in
    ag_idempotent_unit (module_group R V) (V .smul a (V .zero))
      (calc
         V .add (V .smul a (V .zero)) (V .smul a (V .zero)) = V .smul a (V .add (V .zero) (V .zero))
           by inverse S (V .smul a (V .add (V .zero) (V .zero))) (V .add (V .smul a (V .zero)) (V .smul a (V .zero)))
             (V .smul_add_vector a (V .zero) (V .zero))
         = V .smul a (V .zero) by refl (V .smul a) (V .add_laws .unit_right (V .zero)) ∎)

{` K-linear maps: group homomorphisms h with h(a v) = a h(v). `}
def IsLinear (R : AbstractRing) (V W : RingModule R) (f : V .carrier → W .carrier) : Type
  ≔ (a : R .carrier) (v : V .carrier) → Id (W .carrier) (f (V .smul a v)) (W .smul a (f v))

def LinearMap (R : AbstractRing) (V W : RingModule R) : Type
  ≔ Σ (AbstractHom (module_group R V) (module_group R W)) (φ ↦ IsLinear R V W (φ .fst))

def linear_map_fn (R : AbstractRing) (V W : RingModule R) (h : LinearMap R V W) : V .carrier → W .carrier
  ≔ h .fst .fst

def is_linear_prop (R : AbstractRing) (V W : RingModule R) (f : V .carrier → W .carrier) : isProp (IsLinear R V W f)
  ≔ pi_prop (R .carrier) (a ↦ (v : V .carrier) → Id (W .carrier) (f (V .smul a v)) (W .smul a (f v)))
      (a ↦ pi_prop (V .carrier) (v ↦ Id (W .carrier) (f (V .smul a v)) (W .smul a (f v)))
        (v ↦ module_set R W (f (V .smul a v)) (W .smul a (f v))))

def linear_map_ext (R : AbstractRing) (V W : RingModule R) (h k : LinearMap R V W)
  (e : (v : V .carrier) → Id (W .carrier) (h .fst .fst v) (k .fst .fst v))
  : Id (LinearMap R V W) h k
  ≔ subtype_equal (AbstractHom (module_group R V) (module_group R W)) (φ ↦ IsLinear R V W (φ .fst))
      (φ ↦ is_linear_prop R V W (φ .fst)) h k
      (abstract_hom_ext (module_group R V) (module_group R W) (h .fst) (k .fst) e)

def linear_map_set (R : AbstractRing) (V W : RingModule R) : isSet (LinearMap R V W)
  ≔ sigma_set (AbstractHom (module_group R V) (module_group R W)) (φ ↦ IsLinear R V W (φ .fst))
      (abstract_hom_set (module_group R V) (module_group R W))
      (φ ↦ prop_is_set (IsLinear R V W (φ .fst)) (is_linear_prop R V W (φ .fst)))

def linear_id (R : AbstractRing) (V : RingModule R) : LinearMap R V V
  ≔ (abstract_hom_id (module_group R V), a v ↦ refl (V .smul a v))

{` k ∘ h (h first). `}
def linear_compose (R : AbstractRing) (U V W : RingModule R) (h : LinearMap R U V) (k : LinearMap R V W)
  : LinearMap R U W
  ≔ (abstract_hom_compose (module_group R U) (module_group R V) (module_group R W) (h .fst) (k .fst),
     a u ↦ concat (W .carrier) (k .fst .fst (h .fst .fst (U .smul a u))) (k .fst .fst (V .smul a (h .fst .fst u)))
       (W .smul a (k .fst .fst (h .fst .fst u)))
       (refl (k .fst .fst) (h .snd a u)) (k .snd a (h .fst .fst u)))

{` The free K-vector space on a set S: (V, i) such that for every
   K-vector space W and j : S → W the type of linear maps h : V → W with
   h(i(s)) = j(s) for all s is contractible. `}
def LinearExtensions (R : AbstractRing) (S : SetTypes) (V : RingModule R) (i : S .fst → V .carrier)
  (W : RingModule R) (j : S .fst → W .carrier) : Type
  ≔ Σ (LinearMap R V W) (h ↦ (s : S .fst) → Id (W .carrier) (h .fst .fst (i s)) (j s))

def IsFreeModuleOn (R : AbstractRing) (S : SetTypes) (V : RingModule R) (i : S .fst → V .carrier) : Type
  ≔ (W : RingModule R) (j : S .fst → W .carrier) → BookIsContr (LinearExtensions R S V i W j)

def IsFreeVectorSpace (K : Field) (S : SetTypes) (V : VectorSpace K) (i : S .fst → V .carrier) : Type
  ≔ IsFreeModuleOn (K .fst) S V i

def FreeVectorSpace (K : Field) (S : SetTypes) : Type
  ≔ Σ (VectorSpace K) (V ↦ Σ (S .fst → V .carrier) (i ↦ IsFreeVectorSpace K S V i))

{` An n-dimensional K-vector space: a free K-vector space on Fin(n). `}
def NDimensionalVectorSpace (K : Field) (n : Nat) : Type ≔ FreeVectorSpace K (standard_set n)

{` Helper for later chapters (not a book definition): V has dimension n
   if it merely is free on Fin n; V is finite dimensional if it has some
   dimension. `}
def HasDimension (K : Field) (n : Nat) (V : VectorSpace K) : Type
  ≔ Mere (Σ (Fin n → V .carrier) (i ↦ IsFreeVectorSpace K (standard_set n) V i))

def IsFiniteDimensional (K : Field) (V : VectorSpace K) : Type ≔ Mere (Σ Nat (n ↦ HasDimension K n V))

{` Litmus: a ring is a module over itself, and it is free on one
   generator (Fin 1, i(*) = 1): the linear maps h with h(1) = w are
   exactly a ↦ a w. Hence a field K is a 1-dimensional K-vector space. `}
def ring_self_module (R : AbstractRing) : RingModule R
  ≔ (R .carrier, R .zero, R .add, R .neg, R .add_laws, ring_add_comm R, R .mul,
     ring_mul_one_left R,
     a b v ↦ inverse (R .carrier) (R .mul a (R .mul b v)) (R .mul (R .mul a b) v) (ring_mul_assoc R a b v),
     a b v ↦ ring_rdistr R a b v,
     a v w ↦ ring_ldistr R a v w)

def fin_one_point : Fin (suc. zero.) ≔ inr. star.

def fin_one_contract (x : Fin (suc. zero.)) : Id (Fin (suc. zero.)) fin_one_point x
  ≔ match x [ inl. e ↦ match e [ ] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ]

def ring_self_generator (R : AbstractRing) : Fin (suc. zero.) → R .carrier ≔ _ ↦ R .one

def scalar_line_map (R : AbstractRing) (W : RingModule R) (w : W .carrier) : LinearMap R (ring_self_module R) W
  ≔ ((a ↦ W .smul a w, a b ↦ W .smul_add_scalar a b w),
     a b ↦ W .smul_mul a b w)

def ring_self_module_free (R : AbstractRing)
  : IsFreeModuleOn R (standard_set (suc. zero.)) (ring_self_module R) (ring_self_generator R)
  ≔ W j ↦
    let w ≔ j fin_one_point in
    let E ≔ LinearExtensions R (standard_set (suc. zero.)) (ring_self_module R) (ring_self_generator R) W j in
    let c : E
      ≔ (scalar_line_map R W w,
         s ↦ concat (W .carrier) (W .smul (R .one) w) w (j s) (W .smul_one w)
               (refl j (fin_one_contract s))) in
    (center ≔ c,
     contract ≔ u ↦
       subtype_equal (LinearMap R (ring_self_module R) W)
         (h ↦ (s : Fin (suc. zero.)) → Id (W .carrier) (h .fst .fst (R .one)) (j s))
         (h ↦ pi_prop (Fin (suc. zero.)) (s ↦ Id (W .carrier) (h .fst .fst (R .one)) (j s))
           (s ↦ module_set R W (h .fst .fst (R .one)) (j s)))
         c u
         (linear_map_ext R (ring_self_module R) W (c .fst) (u .fst)
           (a ↦ calc
              W .smul a w = W .smul a (u .fst .fst .fst (R .one))
                by refl (W .smul a) (inverse (W .carrier) (u .fst .fst .fst (R .one)) w (u .snd fin_one_point))
              = u .fst .fst .fst (R .mul a (R .one))
                by inverse (W .carrier) (u .fst .fst .fst (R .mul a (R .one))) (W .smul a (u .fst .fst .fst (R .one)))
                  (u .fst .snd a (R .one))
              = u .fst .fst .fst a by refl (u .fst .fst .fst) (ring_mul_one_right R a) ∎)))

def field_one_dimensional (K : Field) : NDimensionalVectorSpace K (suc. zero.)
  ≔ (ring_self_module (K .fst), (ring_self_generator (K .fst), ring_self_module_free (K .fst)))
