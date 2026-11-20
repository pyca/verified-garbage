module

public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.MlKem.Arm.Wipe
public import VerifiedGarbage.Impl.MlKem.Arm.Poly
public import VerifiedGarbage.Impl.MlKem1024.Arm.Poly

/-!
# ML-KEM's functions on ARMv7, as emitted

Each function of ML-KEM-768 and ML-KEM-1024 with its cleanup: the registers
a callee may change set to constants, but the result's 32 bits. Key
generation, encapsulation (with `H(ek)` given or not) and decapsulation
(`Impl.MlKem.Arm.Wipe`) have frames: they first zero the stack their
contracts reserve, 24 bytes (key generation and decapsulation: the wrapper's
16 and its calls' 8) or 32 (encapsulation: its copy of the stack arguments,
8 more). The encapsulation key checks have no frames.
-/

@[expose] public section

namespace VG.Impl.MlKem.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := scrubF 32 24 Wipe.keyGen

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := scrubF 32 32 Wipe.encapsH

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := scrubF 32 32 Wipe.encaps

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := scrubF 32 24 Wipe.decaps

/-- `vg_mlkem768_check_ek`. -/
def checkEk : Prog isa := scrub 32 Impl.MlKem.Arm.checkEk

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := scrubF 32 24 Wipe.keyGen1024

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := scrubF 32 32 Wipe.encapsH1024

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := scrubF 32 32 Wipe.encaps1024

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := scrubF 32 24 Wipe.decaps1024

/-- `vg_mlkem1024_check_ek`. -/
def checkEk1024 : Prog isa := scrub 32 Impl.MlKem1024.Arm.checkEk1024

end VG.Impl.MlKem.Arm.Fn
