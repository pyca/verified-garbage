module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Wipe
public import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
public import VerifiedGarbage.Impl.MlKem1024.RISCV64.Poly
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# ML-KEM-768 and ML-KEM-1024 on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use (1200 bytes; none for the encapsulation key check), so
that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := scrub 32 1200 Wipe.keyGen

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := scrub 32 1200 Wipe.encaps

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := scrub 32 1200 Wipe.encapsH

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := scrub 32 1200 Wipe.decaps

/-- `vg_mlkem768_check_ek`. -/
def checkEk : Prog isa := scrub 32 0 VG.Impl.MlKem.RISCV64.checkEk

/-- `vg_mlkem1024_check_ek`. -/
def checkEk1024 : Prog isa := scrub 32 0 Impl.MlKem1024.RISCV64.checkEk1024

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := scrub 32 1200 Wipe.keyGen1024

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := scrub 32 1200 Wipe.encaps1024

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := scrub 32 1200 Wipe.encapsH1024

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := scrub 32 1200 Wipe.decaps1024

end VG.Impl.MlKem.RISCV64.Fn
