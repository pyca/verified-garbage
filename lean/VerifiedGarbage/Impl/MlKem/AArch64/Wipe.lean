module

public import VerifiedGarbage.Impl.CallWipe.AArch64
public import VerifiedGarbage.Impl.Zeroize.AArch64Wide
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8

/-!
# ML-KEM on AArch64: the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls the
function named for it and `sfx` (the suffix of its instance), then
`vg_zeroize` on all of `scratch` (`callWipe`): 32768 bytes for ML-KEM-768
and 49152 for ML-KEM-1024, none of whose implementations has a smaller bound
on what it writes there. That function calls its code `body`, named for the
function and `xsfx` (the suffix of the two-state permutation it calls), with
the address of the single-state permutation `n` in `d8` (`entryD8`): `body`
is the same code for every single-state permutation.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Wipe

open VG.AArch64 VG.Impl.CallWipe.AArch64

/-- A call of the code `body` of the function `fn` with `p`'s address in
`d8`, then of `vg_zeroize` on the first `n` bytes of the buffer whose address
is in `r`. -/
def wiped (r : Reg) (n : Nat) (fn sfx xsfx p : String) (body : Prog isa) : Prog isa :=
  callWipe r n (fn ++ "_body" ++ sfx) (Impl.Sha3.AArch64.entryD8 p (fn ++ "_core" ++ xsfx) body) "vg_zeroize"
    Impl.Zeroize.AArch64.zeroizeWide

/-- `vg_mlkem768_keygen`. -/
def keyGen (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x3 32768 "vg_mlkem768_keygen" sfx xsfx p body

/-- `vg_mlkem768_encaps_h`. -/
def encapsH (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x5 32768 "vg_mlkem768_encaps_h" sfx xsfx p body

/-- `vg_mlkem768_encaps`. -/
def encaps (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x4 32768 "vg_mlkem768_encaps" sfx xsfx p body

/-- `vg_mlkem768_decaps`. -/
def decaps (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x3 32768 "vg_mlkem768_decaps" sfx xsfx p body

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x3 49152 "vg_mlkem1024_keygen" sfx xsfx p body

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 (sfx xsfx p : String) (body : Prog isa) : Prog isa :=
  wiped .x5 49152 "vg_mlkem1024_encaps_h" sfx xsfx p body

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x4 49152 "vg_mlkem1024_encaps" sfx xsfx p body

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 (sfx xsfx p : String) (body : Prog isa) : Prog isa := wiped .x3 49152 "vg_mlkem1024_decaps" sfx xsfx p body

end VG.Impl.MlKem.AArch64.Wipe
