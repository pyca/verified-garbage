module

public import VerifiedGarbage.Impl.CallWipe.PPC64LE
public import VerifiedGarbage.Impl.Zeroize.PPC64LE
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Top

/-!
# ML-KEM on PPC64LE: the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`Impl.MlKem.PPC64LE.keygen`, …) as the internal function named for it,
then `vg_zeroize` on all of `scratch` (`callWipe`, in a frame of 128 bytes,
so that the code's stack pointer is the caller's modulo POWER's 128-byte
cache line): 32768 bytes for ML-KEM-768 and 49152 for ML-KEM-1024, with no
proven smaller bound on what the code writes there.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE.Wipe

open VG.PPC64LE VG.Impl.CallWipe.PPC64LE

/-- A call of the code `body` of the function `fn`, then of `vg_zeroize` on
the first `n` bytes of the buffer whose address is in `r`. -/
def wiped (r : Reg) (n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipe 128 r n (fn ++ "_body") body "vg_zeroize" Impl.Zeroize.PPC64LE.zeroize

/-- `vg_mlkem768_keygen`. -/
def keyGen : Prog isa := wiped .r6 32768 "vg_mlkem768_keygen" Impl.MlKem.PPC64LE.keygen

/-- `vg_mlkem768_encaps_h`. -/
def encapsH : Prog isa := wiped .r8 32768 "vg_mlkem768_encaps_h" Impl.MlKem.PPC64LE.encapsH

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := wiped .r7 32768 "vg_mlkem768_encaps" Impl.MlKem.PPC64LE.encaps

/-- `vg_mlkem768_decaps`. -/
def decaps : Prog isa := wiped .r6 32768 "vg_mlkem768_decaps" Impl.MlKem.PPC64LE.decaps

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 : Prog isa := wiped .r6 49152 "vg_mlkem1024_keygen" Impl.MlKem1024.PPC64LE.keygen1024

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 : Prog isa := wiped .r8 49152 "vg_mlkem1024_encaps_h" Impl.MlKem1024.PPC64LE.encapsH1024

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 : Prog isa := wiped .r7 49152 "vg_mlkem1024_encaps" Impl.MlKem1024.PPC64LE.encaps1024

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 : Prog isa := wiped .r6 49152 "vg_mlkem1024_decaps" Impl.MlKem1024.PPC64LE.decaps1024

end VG.Impl.MlKem.PPC64LE.Wipe
