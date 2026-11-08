module

public import VerifiedGarbage.Impl.CallWipe.RISCV64
public import VerifiedGarbage.Impl.Zeroize.RISCV64
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
public import VerifiedGarbage.Impl.MlKem1024.RISCV64.Top

/-!
# ML-KEM on RISC-V: the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`Impl.MlKem.RISCV64.keygen`, …) as the internal function named for it,
then `vg_zeroize` on all of `scratch` (`callWipe`): 32768 bytes for
ML-KEM-768 and 49152 for ML-KEM-1024, with no proven smaller bound on what
the code writes there.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64.Wipe

open VG.RISCV64 VG.Impl.CallWipe.RISCV64

/-- A call of the code `body` of the function `fn`, then of `vg_zeroize` on
the first `n` bytes of the buffer whose address is in `r`. -/
def wiped (r : Reg) (n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipe r n (fn ++ "_body") body "vg_zeroize" Impl.Zeroize.RISCV64.zeroize

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := wiped .a3 32768 "vg_mlkem768_keygen" Impl.MlKem.RISCV64.keygen

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := wiped .a5 32768 "vg_mlkem768_encaps_h" Impl.MlKem.RISCV64.encapsH

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := wiped .a4 32768 "vg_mlkem768_encaps" Impl.MlKem.RISCV64.encaps

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := wiped .a3 32768 "vg_mlkem768_decaps" Impl.MlKem.RISCV64.decaps

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := wiped .a3 49152 "vg_mlkem1024_keygen" Impl.MlKem1024.RISCV64.keygen1024

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := wiped .a5 49152 "vg_mlkem1024_encaps_h" Impl.MlKem1024.RISCV64.encapsH1024

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := wiped .a4 49152 "vg_mlkem1024_encaps" Impl.MlKem1024.RISCV64.encaps1024

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := wiped .a3 49152 "vg_mlkem1024_decaps" Impl.MlKem1024.RISCV64.decaps1024

end VG.Impl.MlKem.RISCV64.Wipe
