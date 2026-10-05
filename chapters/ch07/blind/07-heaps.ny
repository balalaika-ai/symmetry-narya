export "03-torsors"

{` Blind statements, chapter 7, section "Heaps". `}

{` def:bipt-conn-groupoid: U^{=1}_{••} ≔ Σ (A : U^{=1}) (A × A), with
   U^{=1} = Σ (A : U) isconn(A) × isgrpd(A). `}
def BlindConnGroupoid : Type ≔ Σ Type (A ↦ Product (Connected A) (isGroupoid A))

def BlindBiPCG : Type ≔ Σ BlindConnGroupoid (A ↦ Product (A .fst) (A .fst))

{` def:heap: a wrapped copy of U^{=1}_{••} (one-field record, as Group). `}
def BlindHeap : Type ≔ sig (classifying : BlindBiPCG)

def blind_mkheap (X : BlindBiPCG) : BlindHeap ≔ (classifying ≔ X)
def blind_heap_B (H : BlindHeap) : BlindBiPCG ≔ H .classifying
def blind_heap_carrier (H : BlindHeap) : Type ≔ H .classifying .fst .fst
def blind_heap_start (H : BlindHeap) : blind_heap_carrier H ≔ H .classifying .snd .fst
def blind_heap_end (H : BlindHeap) : blind_heap_carrier H ≔ H .classifying .snd .snd

{` ISym(A, a, a') ≔ (a = a'); USym H ≔ ISym(B H), a set. `}
def blind_heap_usym (H : BlindHeap) : Type
  ≔ Id (blind_heap_carrier H) (blind_heap_start H) (blind_heap_end H)

def blind_heap_usym_set (H : BlindHeap) : SetTypes
  ≔ (blind_heap_usym H, H .classifying .fst .snd .snd (blind_heap_start H) (blind_heap_end H))

{` The groups at the start and at the end shape. `}
def blind_heap_start_group (H : BlindHeap) : Group
  ≔ mkgroup (blind_heap_carrier H, blind_heap_start H, H .classifying .fst .snd .fst, H .classifying .fst .snd .snd)

def blind_heap_end_group (H : BlindHeap) : Group
  ≔ mkgroup (blind_heap_carrier H, blind_heap_end H, H .classifying .fst .snd .fst, H .classifying .fst .snd .snd)

{` xca:group+torsor-heap: l, r : Heap ≃ Σ (G : Group) BG and c : Group ≃
   Σ (H : Heap) USym H, with l taking the start shape as designated shape,
   r the end shape, and c doubling the shape (with refl). `}
def blind_heap_l (H : BlindHeap) : Σ Group (G ↦ BG G .carrier) ≔ (blind_heap_start_group H, blind_heap_end H)
def blind_heap_r (H : BlindHeap) : Σ Group (G ↦ BG G .carrier) ≔ (blind_heap_end_group H, blind_heap_start H)
def blind_heap_c (G : Group) : Σ BlindHeap blind_heap_usym
  ≔ (blind_mkheap ((BG G .carrier, (bg_connected G, bg_groupoid G)), (shape G, shape G)), refl (shape G))

def blind_xca_group_torsor_heap : Type
  ≔ Product (BookIsEquiv BlindHeap (Σ Group (G ↦ BG G .carrier)) blind_heap_l)
      (Product (BookIsEquiv BlindHeap (Σ Group (G ↦ BG G .carrier)) blind_heap_r)
        (BookIsEquiv Group (Σ BlindHeap blind_heap_usym) blind_heap_c))

{` The ternary operation (p, q, r) ↦ p q⁻¹ r (r first, then q⁻¹, then p). `}
def blind_heap_t (H : BlindHeap) (p q r : blind_heap_usym H) : blind_heap_usym H
  ≔ let A ≔ blind_heap_carrier H in let a ≔ blind_heap_start H in let a' ≔ blind_heap_end H in
    concat A a a' a' r (concat A a' a a' (inverse A a a' q) p)

{` Exercise (absgroup.tex 1384): the symmetries r ↦ p q⁻¹ r of USym H form a
   group (an abstract group under composition, made concrete by concr);
   it is identified with the symmetry group of the end shape. `}
def BlindHeapShear (H : BlindHeap) : Type
  ≔ Σ (blind_heap_usym H → blind_heap_usym H) (s ↦
      Mere (Σ (blind_heap_usym H) (p ↦ Σ (blind_heap_usym H) (q ↦
        Id (blind_heap_usym H → blind_heap_usym H) s (r ↦ blind_heap_t H p q r)))))

def blind_xca_heap_to_group : Type
  ≔ (H : BlindHeap)
    → Σ (BlindHeapShear H) (e ↦
      Σ (BlindHeapShear H → BlindHeapShear H → BlindHeapShear H) (mul ↦
      Σ (BlindHeapShear H → BlindHeapShear H) (inv ↦
        Product (Id (blind_heap_usym H → blind_heap_usym H) (e .fst) (r ↦ r))
          (Product ((s u : BlindHeapShear H) → Id (blind_heap_usym H → blind_heap_usym H) (mul s u .fst) (r ↦ s .fst (u .fst r)))
            (Σ (BlindGroupLaws (BlindHeapShear H) e mul inv) (laws ↦
              Id Group (blind_concr (BlindHeapShear H, e, mul, inv, laws)) (blind_heap_end_group H)))))))

{` Exercise (absgroup.tex 1391): the symmetry groups of the endpoints are
   merely isomorphic; for abelian heaps (here: p q⁻¹ r = r q⁻¹ p) they are
   purely isomorphic. `}
def BlindIsAbelianHeap (H : BlindHeap) : Type
  ≔ (p q r : blind_heap_usym H) → Id (blind_heap_usym H) (blind_heap_t H p q r) (blind_heap_t H r q p)

def blind_xca_heap_endpoints : Type
  ≔ Product ((H : BlindHeap) → Mere (GroupIso (blind_heap_start_group H) (blind_heap_end_group H)))
      ((H : BlindHeap) → BlindIsAbelianHeap H → GroupIso (blind_heap_start_group H) (blind_heap_end_group H))

{` xca:heap-variety. `}
def BlindTernary (S : SetTypes) : Type ≔ Product (S .fst) (Product (S .fst) (S .fst)) → S .fst

def blind_heap_ternary_structure (H : BlindHeap) : Σ SetTypes BlindTernary
  ≔ (blind_heap_usym_set H, u ↦ blind_heap_t H (u .fst) (u .snd .fst) (u .snd .snd))

def blind_xca_heap_variety : Type
  ≔ Product ((S : SetTypes) → isSet (Σ BlindHeap (H ↦ Id SetTypes S (blind_heap_usym_set H))))
      ((S : SetTypes) (t : BlindTernary S)
        → isProp (BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t)))

{` The description asked for (our answer, not printed in the book): the
   fiber is the proposition "S is inhabited and t is para-associative with
   t(p,p,r) = r and t(p,q,q) = p". `}
def BlindHeapLaws (S : SetTypes) (t : BlindTernary S) : Type
  ≔ Product (Mere (S .fst))
      (Product ((p q r s u : S .fst) → Id (S .fst) (t (t (p, (q, r)), (s, u))) (t (p, (q, t (r, (s, u))))))
        (Product ((p r : S .fst) → Id (S .fst) (t (p, (p, r))) r) ((p q : S .fst) → Id (S .fst) (t (p, (q, q))) p)))

def blind_xca_heap_variety_description : Type
  ≔ (S : SetTypes) (t : BlindTernary S)
    → BookEquiv (BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t)) (BlindHeapLaws S t)
