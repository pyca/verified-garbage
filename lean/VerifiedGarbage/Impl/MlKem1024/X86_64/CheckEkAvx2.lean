module

public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEkAvx2

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_check_ek_avx2`

The key check with AVX2 (`Impl/MlKem/X86_64/CheckEkAvx2.lean`) for
ML-KEM-1024: the 128 groups of 12 bytes of `ek[0 : 1536]`.
-/

@[expose] public section

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

abbrev checkEk1024Avx2 : Prog isa := checkEkAvx2K 4

end VG.Impl.MlKem1024.X86_64
