export "117-truncated-map-calculus"

def set_hlevel_above_two (n : Nat) (A : Type) (ha : isSet A) : HLevel (suc. (suc. n)) A
  ≔ match n [
  | zero. ↦ set_to_hlevel_two A ha
  | suc. n ↦ hlevel_raise (suc. (suc. n)) A (set_hlevel_above_two n A ha) ]

{` xca:covering-utils, item 6: book n-types use h-level n+2. `}
def covering_domain_hlevel (n : Nat) (A B : Type) (f : A → B) (hf : IsCovering A B f)
  (hb : HLevel (suc. (suc. n)) B) : HLevel (suc. (suc. n)) A
  ≔ truncated_map_domain_hlevel (suc. (suc. n)) A B f
      (b ↦ set_hlevel_above_two n (BookFiber A B f b) (hf b)) hb

def covering_domain_set (A B : Type) (f : A → B) (hf : IsCovering A B f) (hb : isSet B) : isSet A
  ≔ hlevel_two_to_set A (covering_domain_hlevel zero. A B f hf (set_to_hlevel_two B hb))

def covering_domain_groupoid (A B : Type) (f : A → B) (hf : IsCovering A B f) (hb : isGroupoid B)
  : isGroupoid A
  ≔ hlevel_to_groupoid A (covering_domain_hlevel (suc. zero.) A B f hf (groupoid_to_hlevel B hb))

{` xca:covering-utils, item 3. `}
def coverings_compose (A B C : Type) (f : A → B) (g : B → C) (hf : IsCovering A B f) (hg : IsCovering B C g)
  : IsCovering A C (compose A B C g f)
  ≔ c ↦ hlevel_two_to_set (BookFiber A C (compose A B C g f) c)
      (truncated_maps_compose (suc. (suc. zero.)) A B C f g
        (b ↦ set_to_hlevel_two (BookFiber A B f b) (hf b))
        (c ↦ set_to_hlevel_two (BookFiber B C g c) (hg c)) c)

{` xca:covering-utils, item 4. Both g and g o f are required. `}
def coverings_left_cancel (A B C : Type) (f : A → B) (g : B → C)
  (hg : IsCovering B C g) (hgf : IsCovering A C (compose A B C g f)) : IsCovering A B f
  ≔ b ↦ hlevel_two_to_set (BookFiber A B f b)
      (truncated_maps_left_cancel (suc. zero.) A B C f g
        (c ↦ set_to_hlevel_two (BookFiber B C g c) (hg c))
        (c ↦ set_to_hlevel_two (BookFiber A C (compose A B C g f) c) (hgf c)) b)

{` xca:covering-utils, item 5. Connectivity of the loops is needed only
   at the supplied point; the proposition-valued conclusion propagates. `}
def covering_connected_loops_contractible (A B : Type) (f : A → B) (hf : IsCovering A B f)
  (ha : Connected A) (a : A) (hloops : Connected (Id A a a)) (hb : isGroupoid B) : BookIsContr A
  ≔ let ga ≔ covering_domain_groupoid A B f hf hb in
    let loops ≔ native_connected_set_contractible (Id A a a) hloops (ga a a) in
    connected_loops_prop_contractible native_truncation A ha
      (connected_based_elim native_truncation A ha a (x ↦ isProp (Id A x x))
        (x ↦ isprop_isprop (Id A x x))
        (contractible_prop (Id A a a) (native_contraction (Id A a a) loops)))
