module

public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86
public import VerifiedGarbage.Impl.MlKem.X86.KeyGen
public import VerifiedGarbage.Impl.MlKem.X86.Encaps
public import VerifiedGarbage.Impl.MlKem.X86.Decaps
public import VerifiedGarbage.Impl.MlKem1024.X86.Kem
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# ML-KEM on x86 (32-bit): the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`Impl.MlKem.X86.keyGen`, …) as the internal function named for it, with
the arguments it was given, then `vg_zeroize`'s code (the internal
`vg_zeroize_core`) on all of `scratch`, its last argument: 32768 bytes for
ML-KEM-768 and 49152 for ML-KEM-1024, with no proven smaller bound on what
the code writes there (`callWipe`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86.Wipe

open VG.X86 VG.Impl.CallWipe.X86

/-- A call of the code `body` of the function `fn`, whose arguments take `m`
slots of stack, then of `vg_zeroize`'s code (the internal `vg_zeroize_core`)
on the first `n` bytes of the buffer whose address is the last of them. -/
def wiped (m n : Nat) (fn : String) (body : Prog isa) : Prog isa :=
  callWipe m (m - 1) n (fn ++ "_body") body "vg_zeroize_core" Impl.Zeroize.X86.zeroize

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

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.MlKem.X86.Fn

open VG.X86

/-- `vg_mlkem768_keygen`, as emitted. -/
def keyGen : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.keyGen

/-- `vg_mlkem768_encaps_h`, as emitted. -/
def encapsH : Prog isa := Impl.Scrub.X86.scrubAll 32 136 Impl.MlKem.X86.Wipe.encapsH

/-- `vg_mlkem768_encaps`, as emitted. -/
def encaps : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.encaps

/-- `vg_mlkem768_decaps`, as emitted. -/
def decaps : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.decaps

/-- `vg_mlkem768_check_ek`, as emitted. -/
def checkEk : Prog isa := Impl.Scrub.X86.scrubAll 32 16 Impl.MlKem.X86.checkEk

/-- `vg_mlkem1024_keygen`, as emitted. -/
def keyGen1024 : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.keyGen1024

/-- `vg_mlkem1024_encaps_h`, as emitted. -/
def encapsH1024 : Prog isa := Impl.Scrub.X86.scrubAll 32 136 Impl.MlKem.X86.Wipe.encapsH1024

/-- `vg_mlkem1024_encaps`, as emitted. -/
def encaps1024 : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.encaps1024

/-- `vg_mlkem1024_decaps`, as emitted. -/
def decaps1024 : Prog isa := Impl.Scrub.X86.scrubAll 32 120 Impl.MlKem.X86.Wipe.decaps1024

/-- `vg_mlkem1024_check_ek`, as emitted. -/
def checkEk1024 : Prog isa := Impl.Scrub.X86.scrubAll 32 16 Impl.MlKem1024.X86.checkEk

end VG.Impl.MlKem.X86.Fn
