export "903-normal-subgroups"
export "954-abstract-kernel"
export "952-cokernels-of-composites"
export "934-epi-connected-fibers"

{` Chapter 9: the book's "epimorphism" forms of cor:cokermaps (7) and
   xca:abstract-kernel, obtained from the connected-fibers versions
   (modules 952, 954) with lem:epi-surj (gepi_epi_connected_fibers, 934). `}

{` cor:cokermaps (7): if f1 is an epimorphism, tot(‖F1'‖₀) is an
   equivalence of G2-sets, and coker(f2 f1) = coker(f2). `}
def kc_coker_hom_is_equiv_of_epi (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (e : IsGroupEpi G0 G1 f1) (w : BG G2 .carrier)
  : BookIsEquiv (SetTrunc (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w)) (SetTrunc (HomFiber G1 G2 f2 w))
      (kc_coker_hom G0 G1 G2 f1 f2 w)
  ≔ kc_coker_hom_is_equiv G0 G1 G2 f1 f2 (gepi_epi_connected_fibers G0 G1 f1 e) w

def kc_coker_path_of_epi (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (e : IsGroupEpi G0 G1 f1)
  : Id (GSet G2) (cokernel G0 G2 (kc_compose G0 G1 G2 f1 f2)) (cokernel G1 G2 f2)
  ≔ kc_coker_path G0 G1 G2 f1 f2 (gepi_epi_connected_fibers G0 G1 f1 e)

{` xca:abstract-kernel, last part: for an epimorphism f, X(f) simplifies to
   z ↦ (sh_H = Bf(z)). `}
def abstract_kernel_epi_equiv_of_epi (G H : Group) (f : GroupHom G H) (e : IsGroupEpi G H f) (z : BG G .carrier)
  : Equiv (abstract_kernel_gset G H f z .fst) (Id (BG H .carrier) (shape H) (hom_function G H f z))
  ≔ abstract_kernel_epi_equiv G H f (gepi_epi_connected_fibers G H f e) z

def abstract_kernel_epi_path_of_epi (G H : Group) (f : GroupHom G H) (e : IsGroupEpi G H f)
  : Id (GSet G) (abstract_kernel_gset G H f) (kernel_gset G H f)
  ≔ abstract_kernel_epi_path G H f (gepi_epi_connected_fibers G H f e)
