module

public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86
public import VerifiedGarbage.Impl.MlKem.X86.KeyGen
public import VerifiedGarbage.Impl.MlKem.X86.Encaps
public import VerifiedGarbage.Impl.MlKem.X86.Decaps
public import VerifiedGarbage.Impl.MlKem1024.X86.Kem

/-!
# ML-KEM on x86 (32-bit): the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`Impl.MlKem.X86.keyGen`, …) as the internal function named for it, with
the arguments it was given, then `vg_zeroize` on all of `scratch`, its last
argument: 32768 bytes for ML-KEM-768 and 49152 for ML-KEM-1024, with no
proven smaller bound on what the code writes there (`callWipe`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86.Wipe

open VG.X86 VG.Impl.CallWipe.X86

/-- A call of the code `body` of the function `fn`, whose arguments take `m`
slots of stack, then of `vg_zeroize` on the first `n` bytes of the buffer
whose address is the last of them. -/
def wiped (m n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipe m (m - 1) n (fn ++ "_body") body "vg_zeroize" Impl.Zeroize.X86.zeroize

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := wiped 4 32768 "vg_mlkem768_keygen" Impl.MlKem.X86.keyGen

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := wiped 6 32768 "vg_mlkem768_encaps_h" Impl.MlKem.X86.encapsH

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := wiped 5 32768 "vg_mlkem768_encaps" Impl.MlKem.X86.encaps

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := wiped 4 32768 "vg_mlkem768_decaps" Impl.MlKem.X86.decaps

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := wiped 4 49152 "vg_mlkem1024_keygen" Impl.MlKem1024.X86.keyGen

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := wiped 6 49152 "vg_mlkem1024_encaps_h" Impl.MlKem1024.X86.encapsH

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := wiped 5 49152 "vg_mlkem1024_encaps" Impl.MlKem1024.X86.encaps

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := wiped 4 49152 "vg_mlkem1024_decaps" Impl.MlKem1024.X86.decaps

end VG.Impl.MlKem.X86.Wipe
