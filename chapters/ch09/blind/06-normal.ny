{` Blind statements for chapter 9 (subgroups.tex), section "Normal subgroups" and "The associated kernel". `}
export "04-images"
export "05-subgroup-action"

{` def:normalsubgroup. Nor(G) ≔ Π_{y:BG} Sub(G)(y). `}
def BlindNor (G : Group) : Type ≔ (y : BG G .carrier) → Subgroups (group_at G y)

{` def:normalsubgroup. i : Nor(G) → Sub(G), i(N) ≔ N(sh_G). `}
def blind_nor_incl (G : Group) (N : BlindNor G) : Subgroups G ≔ N (shape G)

{` Remark (subgroups.tex:1330). i is an injection. `}
def blind_nor_incl_injective : Type
  ≔ (G : Group) → IsEmbedding (BlindNor G) (Subgroups G) (blind_nor_incl G)

{` Remark (subgroups.tex:1330). A subgroup H is normal when the fiber i^{-1}(H) has an element; that fiber is a proposition. `}
def BlindIsNormalSubgroup (G : Group) (S : Subgroups G) : Type ≔ BookFiber (BlindNor G) (Subgroups G) (blind_nor_incl G) S

def blind_is_normal_subgroup_prop : Type ≔ (G : Group) (S : Subgroups G) → isProp (BlindIsNormalSubgroup G S)

{` def:setofkernels. The kernel function restricted to epimorphisms, Epi(G) → Mono(G). `}
def blind_ker_epi (G : Group) (e : BlindEpi G) : GroupMonos G ≔ blind_ker G (e .fst) (e .snd .fst)

{` def:setofkernels. Ker_G ≔ the (propositional) image of ker : Epi(G) → Mono(G), with ker : Epi(G) ↠ Ker_G and
   i : Ker_G ↣ Mono(G). `}
def BlindKernels (G : Group) : Type ≔ Image (BlindEpi G) (GroupMonos G) (blind_ker_epi G)

def blind_ker_corestrict (G : Group) (e : BlindEpi G) : BlindKernels G
  ≔ (blind_ker_epi G e, mere (BookFiber (BlindEpi G) (GroupMonos G) (blind_ker_epi G) (blind_ker_epi G e)) (e, refl (blind_ker_epi G e)))

def blind_kernels_incl (G : Group) (k : BlindKernels G) : GroupMonos G ≔ k .fst

def blind_kernels_factorization : Type
  ≔ (G : Group)
    → Product (Surjective (BlindEpi G) (BlindKernels G) (blind_ker_corestrict G))
        (IsEmbedding (BlindKernels G) (GroupMonos G) (blind_kernels_incl G))

{` def:ker2. For (G', f, !) : Epi(G) and y : BG, the G-set P_{f(y)} f : z ↦ (f(y) = f(z)). `}
def blind_nor_gset (G : Group) (e : BlindEpi G) (y : BG G .carrier) : GSet G
  ≔ gset_restrict G (e .fst) (e .snd .fst) (gset_paths (e .fst) (hom_function G (e .fst) (e .snd .fst) y))

{` The transitivity proofs "!" in nor (a consequence of f being an epimorphism), as a parameter. `}
def BlindNorTransitivity (G : Group) : Type
  ≔ (e : BlindEpi G) (y : BG G .carrier) → IsTransitive (group_at G y) (blind_nor_gset G e y)

def blind_nor_transitive : Type ≔ (G : Group) → BlindNorTransitivity G

{` def:ker2. nor(G', f, !)(y) ≔ (P_{f(y)} f, refl_{f(y)}, !). `}
def blind_nor (G : Group) (ht : BlindNorTransitivity G) (e : BlindEpi G) : BlindNor G
  ≔ y ↦ (blind_nor_gset G e y, refl (hom_function G (e .fst) (e .snd .fst) y), ht e y)

{` Remark (subgroups.tex:1408). P_{f(y)} f is not a G-torsor unless f is an isomorphism. `}
def blind_nor_gset_torsor_iff_iso : Type
  ≔ (G : Group) (e : BlindEpi G) (y : BG G .carrier)
    → BlindIff (Mere (Id (GSet G) (principal_gset G) (blind_nor_gset G e y))) (IsGroupIso G (e .fst) (e .snd .fst))

{` lem:diagfornormal. E(i(ker(f))) = i(nor(f)) in Sub(G) for every (G', f, !) : Epi(G). `}
def blind_diagfornormal : Type
  ≔ (G : Group) (ht : BlindNorTransitivity G) (e : BlindEpi G)
    → Id (Subgroups G) (mono_to_subgroup G (blind_kernels_incl G (blind_ker_corestrict G e))) (blind_nor_incl G (blind_nor G ht e))

{` lem:evaliseqwhennormal (1). For N : Nor(G) with N(y) = (X_y, pt_y, !), ev_{yz} : (X_y = X_z) → X_z(y),
   f ↦ f_y(pt_y), is an equivalence. `}
def blind_evaliseqwhennormal : Type
  ≔ (G : Group) (N : BlindNor G) (y z : BG G .carrier)
    → BookIsEquiv (Id (GSet G) (N y .gset) (N z .gset)) (N z .gset y .fst)
        (f ↦ gset_path_eval G (N y .gset) (N z .gset) y (N y .point) f)

{` lem:evaliseqwhennormal (2). The map X : (y = z) → (X_y = X_z) (ap of y ↦ X_y) is surjective. `}
def blind_normal_ap_surjective : Type
  ≔ (G : Group) (N : BlindNor G) (y z : BG G .carrier)
    → Surjective (Id (BG G .carrier) y z) (Id (GSet G) (N y .gset) (N z .gset))
        (map_path (BG G .carrier) (GSet G) (w ↦ N w .gset) y z)

{` def:normalquotient. G/N ≔ Aut_{G-Set}(X_{sh_G}). `}
def BlindQuotientGroup (G : Group) (N : BlindNor G) : Group
  ≔ automorphism_group (GSet G) (gset_groupoid G) (N (shape G) .gset)

{` def:normalquotient. q_N : Hom(G, G/N), Bq_N(z) ≔ X_z, strictly pointed. `}
def blind_quotient_hom (G : Group) (N : BlindNor G) : GroupHom G (BlindQuotientGroup G N)
  ≔ mkhom G (BlindQuotientGroup G N)
      (blind_into_component (BG G .carrier) (bg_connected G) (shape G) (GSet G) (N (shape G) .gset)
        (w ↦ N w .gset) (refl (N (shape G) .gset)))

{` def:normalquotient. q_N is an epimorphism. `}
def blind_quotient_hom_epi : Type
  ≔ (G : Group) (N : BlindNor G) → BlindIsEpi G (BlindQuotientGroup G N) (blind_quotient_hom G N)

def BlindQuotientEpi (G : Group) : Type
  ≔ (N : BlindNor G) → BlindIsEpi G (BlindQuotientGroup G N) (blind_quotient_hom G N)

{` def:normalquotient. q : Nor(G) → Epi(G), q(N) ≔ (G/N, q_N, !). `}
def blind_q (G : Group) (hq : BlindQuotientEpi G) (N : BlindNor G) : BlindEpi G
  ≔ (BlindQuotientGroup G N, (blind_quotient_hom G N, hq N))

{` Remark (subgroups.tex:1466). For a G-type Y, Y/N(y) ≔ Σ_{z:BG} Y(z) × X_z(y). `}
def BlindTypeQuotient (G : Group) (N : BlindNor G) (Y : BG G .carrier → Type) (y : BG G .carrier) : Type
  ≔ Σ (BG G .carrier) (z ↦ Product (Y z) (N z .gset y .fst))

{` Remark: P_G/N(y) ≃ X_{sh_G}(y). `}
def blind_principal_quotient : Type
  ≔ (G : Group) (N : BlindNor G) (y : BG G .carrier)
    → BookEquiv (BlindTypeQuotient G N (z ↦ Id (BG G .carrier) (shape G) z) y) (N (shape G) .gset y .fst)

{` Remark: for a G-torsor Y, Y/N lies in the component of X_{sh_G}. `}
def blind_torsor_quotient_component : Type
  ≔ (G : Group) (N : BlindNor G) (Y : Torsors G)
    → Mere (Id (BG G .carrier → Type) (y ↦ N (shape G) .gset y .fst) (BlindTypeQuotient G N (z ↦ Y .fst z .fst)))

{` Remark: q_N is the composite of P : BG ≃ Torsor_G and -/N, i.e. X_z = P_z/N. `}
def blind_quotient_hom_via_torsors : Type
  ≔ (G : Group) (N : BlindNor G) (z : BG G .carrier)
    → Id (BG G .carrier → Type) (y ↦ N z .gset y .fst) (BlindTypeQuotient G N (w ↦ Id (BG G .carrier) z w))

{` lem:qeq. nor : Epi(G) → Nor(G) is an equivalence with inverse q. `}
def blind_qeq : Type
  ≔ (G : Group) (ht : BlindNorTransitivity G) (hq : BlindQuotientEpi G)
    → Product (BookIsEquiv (BlindEpi G) (BlindNor G) (blind_nor G ht))
        (Product ((N : BlindNor G) → Id (BlindNor G) (blind_nor G ht (blind_q G hq N)) N)
                 ((e : BlindEpi G) → Id (BlindEpi G) (blind_q G hq (blind_nor G ht e)) e))

{` cor:normalisnormal. ker : Epi(G) → Ker_G is an equivalence of sets. `}
def blind_normalisnormal : Type
  ≔ (G : Group) → Product (isSet (BlindEpi G)) (BookIsEquiv (BlindEpi G) (BlindKernels G) (blind_ker_corestrict G))

{` Fixed points of the G-set Mono(G), and of the abstract G-set of lem:conj-abstract. `}
def BlindFixMono (G : Group) : Type ≔ (y : BG G .carrier) → BlindMonoGSet G y .fst

def BlindFixAbsMonos (G : Group) : Type
  ≔ Σ (BlindAbsMonos G) (x ↦ (g : USym G)
      → Id (BlindAbsMonoData G) (blind_abs_conj_act G g (blind_abs_mono_data G x)) (blind_abs_mono_data G x))

{` lem:characterizations of normal. Epi(G) ≃ Ker_G ≃ Nor(G) ≃ (Mono(G))^G ≃ fixed abstract subgroups. `}
def blind_characterizations_of_normal : Type
  ≔ (G : Group)
    → Product (Equiv (BlindEpi G) (BlindKernels G))
        (Product (Equiv (BlindKernels G) (BlindNor G))
          (Product (Equiv (BlindNor G) (BlindFixMono G)) (Equiv (BlindFixMono G) (BlindFixAbsMonos G))))

{` def:associatednormal / sec:assker. Ass(N) ≔ Aut_{Σ_{x:BG} X_{sh_G}(x)}(sh_G, pt_{sh_G}) with the first projection;
   ass(N) : Mono(G). `}
def blind_ass (G : Group) (N : BlindNor G) : GroupMonos G ≔ stabilizer_mono G (N (shape G) .gset) (N (shape G) .point)

{` sec:assker: ass(N) ≔ E^{-1} i(N), i.e. E(ass(N)) = i(N). `}
def blind_ass_E : Type
  ≔ (G : Group) (N : BlindNor G) → Id (Subgroups G) (mono_to_subgroup G (blind_ass G N)) (blind_nor_incl G N)

{` sec:assker: ass(N) is the kernel of q(N) (identification via ev_{x sh_G}). `}
def blind_ass_is_ker_q : Type
  ≔ (G : Group) (N : BlindNor G)
    → Id (GroupMonos G) (blind_ker G (BlindQuotientGroup G N) (blind_quotient_hom G N)) (blind_ass G N)

{` def:associatednormal. ass(N) is a kernel: ass(N) : Ker_G. `}
def blind_ass_is_kernel : Type
  ≔ (G : Group) (N : BlindNor G) → Mere (BookFiber (BlindEpi G) (GroupMonos G) (blind_ker_epi G) (blind_ass G N))

def BlindAssKernelProofs (G : Group) : Type
  ≔ (N : BlindNor G) → Mere (BookFiber (BlindEpi G) (GroupMonos G) (blind_ker_epi G) (blind_ass G N))

def blind_ass_kernel (G : Group) (hk : BlindAssKernelProofs G) (N : BlindNor G) : BlindKernels G ≔ (blind_ass G N, hk N)

{` lem:normalsarekernels. The diagram of equivalences commutes: ass ∘ nor = ker, ass is an equivalence
   (and i ∘ ass = E^{-1} ∘ i is blind_ass_E). "Nor(G)'" in the printed diagram is Nor(G). `}
def blind_normalsarekernels : Type
  ≔ (G : Group) (ht : BlindNorTransitivity G) (hk : BlindAssKernelProofs G)
    → Product (BookIsEquiv (BlindNor G) (BlindKernels G) (blind_ass_kernel G hk))
        ((e : BlindEpi G) → Id (BlindKernels G) (blind_ass_kernel G hk (blind_nor G ht e)) (blind_ker_corestrict G e))
