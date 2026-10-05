export "1112-nielsen-schreier-count"

{` Corollary at fggroups.tex:851: if H has index n in F(S) (S finite), then
   rk H = 1 + n(card S - 1).

   subgroup_free_rank: for a subgroup H of F_S (Subgroups, chapter 5; its group
   is subgroup_group with B H = Σ_{z} X(z), pointed at (base, x0)) of index m
   (def:finite-index) and S of cardinality k, H is merely isomorphic, as a
   group, to the constructed free group F_T on a set T of cardinality c with
   c + m = m·k + 1 (the book's 1 + m(k - 1), stated without subtraction, see
   module 1112).  The pointed equivalence is obtained from the unpointed one of
   Nielsen–Schreier by connecting the image of the base point to base (B F_T is
   connected).  That the rank is well defined (F_T ≅ F_T' implies |T| = |T'|)
   is free_rank_unique in module 1116. `}

def HasFreeRank (G : Group) (r : Nat) : Type
  ≔ Mere (Σ Type (T ↦ Σ (DecidableEquality T) (dT ↦
      Product (Mere (Id Type T (Fin r))) (GroupIso G (constructed_free_group T dT)))))

def pointed_iso_from_equiv (T : Type) (dT : DecidableEquality T) (G : Group)
  (e : Equiv (BG G .carrier) (constructed_free_group_signature T dT .carrier))
  : Mere (GroupIso G (constructed_free_group T dT))
  ≔ let F ≔ constructed_free_group_signature T dT in
    mere_rec (Id (F .carrier) (F .base) (e .map (shape G))) (Mere (GroupIso G (constructed_free_group T dT)))
      (mere_isprop (GroupIso G (constructed_free_group T dT)))
      (p ↦ mere (GroupIso G (constructed_free_group T dT))
        (book_pointed_equiv_group_iso_equiv G (constructed_free_group T dT) .map
          ((e .map, p), book_equivalence (BG G .carrier) (F .carrier) e .equiv)))
      (free_connected T F .snd (F .base) (e .map (shape G)))

def subgroup_free_rank (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (H : Subgroups (free_group S dec F)) (m : Nat) (hm : SubgroupHasIndex (free_group S dec F) H m)
  (k : Nat) (hS : Mere (Id Type S (Fin k)))
  : Mere (Σ Nat (c ↦ Product (Id Nat (add c m) (add (mul m k) (suc. zero.)))
      (HasFreeRank (subgroup_group (free_group S dec F) H) c)))
  ≔ let G ≔ free_group S dec F in
    let Goal ≔ Σ Nat (c ↦ Product (Id Nat (add c m) (add (mul m k) (suc. zero.))) (HasFreeRank (subgroup_group G H) c)) in
    mere_rec (NielsenSchreierBasisCount S F (H .gset) m k) (Mere Goal) (mere_isprop Goal)
      (b ↦ mere_rec (GroupIso (subgroup_group G H) (constructed_free_group (b .fst) (b .snd .fst))) (Mere Goal)
        (mere_isprop Goal)
        (i ↦ mere Goal (b .snd .snd .snd .fst, (b .snd .snd .snd .snd .snd,
          mere (Σ Type (T ↦ Σ (DecidableEquality T) (dT ↦
              Product (Mere (Id Type T (Fin (b .snd .snd .snd .fst)))) (GroupIso (subgroup_group G H) (constructed_free_group T dT)))))
            (b .fst, (b .snd .fst, (b .snd .snd .snd .snd .fst, i))))))
        (pointed_iso_from_equiv (b .fst) (b .snd .fst) (subgroup_group G H) (b .snd .snd .fst)))
      (nielsen_schreier_finite S dec F (H .gset) (H .transitive) m hm k hS)
