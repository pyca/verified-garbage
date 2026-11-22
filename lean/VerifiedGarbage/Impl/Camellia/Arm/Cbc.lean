module

public import VerifiedGarbage.Impl.Camellia.Arm.Keyed
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wide
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Impl.Scrub.Arm.Sel

/-!
# Camellia-CBC on ARMv7

`vg_camellia_cbc_encrypt_chained` and `vg_camellia_cbc_decrypt_chained`
are the generic modes (`Impl/Modes/Arm/Seq.lean`), which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`). Decryption, whose blocks
can be deciphered independently, calls Camellia's ECB function,
`vg_camellia_ecb_decrypt` as it is emitted, with the number of rounds (`ecbCore`), once for a
group of 8, 4 or 2 blocks, then once per block for those left
(`Impl/Modes/Arm/Wide.lean`). Encryption, whose every block needs the one
before, has the table of subkeys built once, in its own working space
(`Impl/Modes/Arm/SeqKeyed.lean`: `vg_camellia_ecb_encrypt_keys`), and calls
`vg_camellia_ecb_keyed` on each block (`Keyed.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_camellia_ecb_encrypt` or `vg_camellia_ecb_decrypt`, as
its artifact has it. -/
def ecbCode (dir : Dir) : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (ecb dir)

namespace Fn

open VG.Impl.Scrub.Arm

/-- The words ECB leaves secret. -/
def ecbWords : List Nat := [0, 1] ++ List.range' 682 22

/-- `vg_camellia_ecb_encrypt`: its code, then its cleanup
(`Impl/Camellia/Arm/Fn.lean`). -/
def ecbEncrypt : Prog isa := scrubSel 0 2816 ecbWords (ecbCode .encrypt)

/-- `vg_camellia_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 2816 ecbWords (ecbCode .decrypt)

end Fn

/-- Camellia's ECB function in the direction `dir`, as the modes call it:
the artifact `vg_camellia_ecb_encrypt` or `vg_camellia_ecb_decrypt`, as it
is emitted, cleanup included (`Fn.ecbEncrypt`), so that its code is in the
crate once. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Camellia.ecbEncryptApi.name
    | .decrypt => Spec.Camellia.ecbDecryptApi.name
  code := match dir with
    | .encrypt => Fn.ecbEncrypt
    | .decrypt => Fn.ecbDecrypt
  bw := 4
  rounds := true

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (scrCore .encrypt).seqK (keyed .encrypt) cbcEncChained

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq8 cbcDecChained cbcDecW

end VG.Impl.Camellia.Arm
