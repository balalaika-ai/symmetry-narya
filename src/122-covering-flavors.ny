export "121-covering-connectedness-examples"

{` def:covering. These predicates concern fibers, not the total space. `}
def FiniteCoverings (B : Type) : Type
  ≔ Σ (Coverings B) (CoveringFinite B)

def DecidableCoverings (B : Type) : Type
  ≔ Σ (Coverings B) (CoveringDecidable B)

def predicate_coverings_groupoid (B : Type) (P : Coverings B → Type)
  (h : (c : Coverings B) → isProp (P c))
  : isGroupoid (Σ (Coverings B) P)
  ≔ hlevel_to_groupoid (Σ (Coverings B) P)
      (subtype_hlevel (suc. (suc. zero.)) (Coverings B) P
        (groupoid_to_hlevel (Coverings B) (coverings_groupoid B)) h)

def finite_coverings_groupoid (B : Type) : isGroupoid (FiniteCoverings B)
  ≔ predicate_coverings_groupoid B (CoveringFinite B) (covering_finite_prop B)

def decidable_coverings_groupoid (B : Type) : isGroupoid (DecidableCoverings B)
  ≔ predicate_coverings_groupoid B (CoveringDecidable B) (covering_decidable_prop B)

def connected_coverings_groupoid (B : Type) : isGroupoid (ConnectedCoverings B)
  ≔ predicate_coverings_groupoid B (c ↦ Connected (c .fst))
      (c ↦ connected_isprop (c .fst))

def connected_finite_coverings_groupoid (B : Type)
  : isGroupoid (ConnectedFiniteCoverings B)
  ≔ hlevel_to_groupoid (ConnectedFiniteCoverings B)
      (subtype_hlevel (suc. (suc. zero.)) (ConnectedCoverings B)
        (c ↦ CoveringFinite B (c .fst))
        (groupoid_to_hlevel (ConnectedCoverings B) (connected_coverings_groupoid B))
        (c ↦ covering_finite_prop B (c .fst)))

def connected_decidable_coverings_groupoid (B : Type)
  : isGroupoid (ConnectedDecidableCoverings B)
  ≔ hlevel_to_groupoid (ConnectedDecidableCoverings B)
      (subtype_hlevel (suc. (suc. zero.)) (ConnectedCoverings B)
        (c ↦ CoveringDecidable B (c .fst))
        (groupoid_to_hlevel (ConnectedCoverings B) (connected_coverings_groupoid B))
        (c ↦ covering_decidable_prop B (c .fst)))

{` The footnote's equivalence uses the actual map forgetting the target
   point and the pointed-map path. Pointed coverings were defined in 98. `}
def pointed_map_chosen_target_equiv (A : Pointed) (B : Type)
  : Equiv (Σ B (b ↦ BookPointedMap A (B, b))) (A .carrier → B)
  ≔ compose_equiv (Σ B (b ↦ BookPointedMap A (B, b)))
      (Σ (A .carrier → B) (f ↦ Σ B (b ↦ Id B b (f (A .point)))))
      (A .carrier → B)
      (sigma_comm B (A .carrier → B) (b f ↦ Id B b (f (A .point))))
      (contractible_fiber_projection (A .carrier → B)
        (f ↦ Σ B (b ↦ Id B b (f (A .point))))
        (f ↦ path_to_contractible B (f (A .point))))

def pointed_map_chosen_target_map (A : Pointed) (B : Type)
  (u : Σ B (b ↦ BookPointedMap A (B, b)))
  : Id (A .carrier → B) (pointed_map_chosen_target_equiv A B .map u)
      (u .snd .fst)
  ≔ refl (u .snd .fst)
