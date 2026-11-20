module

public import VerifiedGarbage.Impl.MlKem.AArch64.Wipe
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
public import VerifiedGarbage.Impl.MlKem.AArch64.OptimizedUsing
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Impl.MlKem1024.AArch64.CheckEk
public import VerifiedGarbage.Impl.Residue.AArch64.Writes
public import VerifiedGarbage.Impl.Residue.AArch64

-- separate module: the functions as emitted name code of the modules above, which do not import one another

/-!
# ML-KEM on AArch64: the functions as emitted

Key generation, encapsulation (hashing the key, or with `H(ek)` given) and
decapsulation of ML-KEM-768 and ML-KEM-1024 with paired sampling, over the
single-state Keccak-f[1600] implementation `c` they call and with the SHA-3
extension's two- and three-state functions or the baseline's (`sha3`): each
is its code, which calls its body and wipes `scratch` (`Wipe`), then its
cleanup, which clears the registers the code may write and zeroes its 160
bytes of stack (`scrubOf`), so that it returns without secret residue. `sfx`
is the suffix of the instance, which names its body.

`vg_mlkem768_check_ek` and `vg_mlkem1024_check_ek` have no stack and no
secrets but in the registers they clear.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64 (scrubOf withClears)

/-- `PRF₂` and `SamplePolyCBD₂`, with the polynomial stored with 16 bits,
hashing with the fixed hash over `c`. -/
def prf (c : Impl.Sha3.AArch64.Callee) : Nat → Nat → Prog isa := fun N off =>
  Optimized.prfCbdUsing (FixedHash.code c .x28 KEM.ST KEM.WK 136 31 [⟨.x28, KEM.RB, 33⟩] [⟨.x28, KEM.PB, 128⟩]) N off

/-- `vg_mlkem768_keygen`. -/
def keyGen (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32 (Wipe.keyGen sfx (Kem16P.keyGen sha3 (FixedHash.code c) c lay768))

/-- `vg_mlkem768_encaps`. -/
def encaps (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32 (Wipe.encaps sfx (Kem16P.encaps sha3 (FixedHash.code c) (prf c) lay768))

/-- `vg_mlkem768_encaps_h`. -/
def encapsH (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32 (Wipe.encapsH sfx (Kem16P.encapsH sha3 (FixedHash.code c) (prf c) lay768))

/-- `vg_mlkem768_decaps`. -/
def decaps (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32 (Wipe.decaps sfx (Kem16P.decaps sha3 (FixedHash.code c) (prf c) lay768))

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024 (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32 (Wipe.keyGen1024 sfx (Kem16P.keyGen sha3 (FixedHash.code c) c Impl.MlKem1024.AArch64.lay1024))

/-- `vg_mlkem1024_encaps`. -/
def encaps1024 (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32
    (Wipe.encaps1024 sfx (Kem16P.encaps sha3 (FixedHash.code c) (prf c) Impl.MlKem1024.AArch64.lay1024))

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024 (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32
    (Wipe.encapsH1024 sfx (Kem16P.encapsH sha3 (FixedHash.code c) (prf c) Impl.MlKem1024.AArch64.lay1024))

/-- `vg_mlkem1024_decaps`. -/
def decaps1024 (sfx : String) (sha3 : Bool) (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  scrubOf 160 32
    (Wipe.decaps1024 sfx (Kem16P.decaps sha3 (FixedHash.code c) (prf c) Impl.MlKem1024.AArch64.lay1024))

/-- `vg_mlkem768_check_ek`, then the registers it leaves cleared. -/
def checkEk : Prog isa :=
  withClears [.x9, .x10] [.v0, .v1, .v2, .v3, .v16, .v19, .v20] none Impl.MlKem.AArch64.checkEk

/-- `vg_mlkem1024_check_ek`, then the registers it leaves cleared. -/
def checkEk1024 : Prog isa :=
  withClears [.x9, .x10] [.v0, .v1, .v2, .v3, .v16, .v19, .v20] none Impl.MlKem1024.AArch64.checkEk

end VG.Impl.MlKem.AArch64.Fn
