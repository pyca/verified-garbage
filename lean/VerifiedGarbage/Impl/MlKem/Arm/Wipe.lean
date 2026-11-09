module

public import VerifiedGarbage.Impl.CallWipe.Arm
public import VerifiedGarbage.Impl.CallWipe.ArmStack
public import VerifiedGarbage.Impl.Zeroize.Arm
public import VerifiedGarbage.Impl.MlKem.Arm.Top
public import VerifiedGarbage.Impl.MlKem1024.Arm.Top

/-!
# ML-KEM on 32-bit ARM: the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`Impl.MlKem.Arm.keygen`, …) as the internal function named for it,
then `vg_zeroize` on all of `scratch`: 32768 bytes for ML-KEM-768 and 49152
for ML-KEM-1024, with no proven smaller bound on what the code writes there.
Key generation and decapsulation get `scratch` in `r3` (`callWipe`);
encapsulation gets it on the stack, as its one stack argument, and
encapsulation with `H(ek)` as the second of its two (`callWipeStack`, which
copies them into its frame for the call).
-/

@[expose] public section

namespace VG.Impl.MlKem.Arm.Wipe

open VG.Arm VG.Impl.CallWipe.Arm VG.Impl.CallWipe.ArmStack

/-- A call of the code `body` of the function `fn`, then of `vg_zeroize` on
the first `n` bytes of the buffer whose address is in `r`. -/
def wiped (r : Reg) (n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipe r n (fn ++ "_body") body "vg_zeroize" Impl.Zeroize.Arm.zeroize

/-- A call of the code `body` of the function `fn`, whose arguments take `k`
words of stack, then of `vg_zeroize` on the first `n` bytes of the buffer
whose address is the stack argument at byte offset `off`. -/
def wipedStack (k off n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipeStack k off n (fn ++ "_body") body "vg_zeroize" Impl.Zeroize.Arm.zeroize

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := wiped .r3 32768 "vg_mlkem768_keygen" Impl.MlKem.Arm.keygen

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := wipedStack 2 4 32768 "vg_mlkem768_encaps_h" Impl.MlKem.Arm.encapsH

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := wipedStack 1 0 32768 "vg_mlkem768_encaps" Impl.MlKem.Arm.encaps

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := wiped .r3 32768 "vg_mlkem768_decaps" Impl.MlKem.Arm.decaps

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := wiped .r3 49152 "vg_mlkem1024_keygen" Impl.MlKem1024.Arm.keygen1024

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := wipedStack 2 4 49152 "vg_mlkem1024_encaps_h" Impl.MlKem1024.Arm.encapsH1024

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := wipedStack 1 0 49152 "vg_mlkem1024_encaps" Impl.MlKem1024.Arm.encaps1024

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := wiped .r3 49152 "vg_mlkem1024_decaps" Impl.MlKem1024.Arm.decaps1024

end VG.Impl.MlKem.Arm.Wipe
