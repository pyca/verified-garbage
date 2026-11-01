module

public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4-CBC on ARMv7

`vg_sm4_cbc_encrypt_chained` and `vg_sm4_cbc_decrypt_chained` are the
generic modes one block at a time (`Impl/Modes/Arm/Seq.lean`), which return
the chaining value in the IV (`Impl/Modes/Arm/CbcChained.lean`), over SM4's
ECB functions,
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`, which they call once per
block (`ecbCore`). Those call `vg_sm4_ecb` (`ecbCall`).
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_sm4_ecb`, as its artifact has it: `ecbAny` with its
scratch buffer in a frame on the stack. -/
def ecbAnyCode : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 1472 0 364 ecbAny

/-- `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`: `decrypt := 0` or `1` in
`r3` and a call of `vg_sm4_ecb`, in a frame saving `r4` and `lr` (8 bytes,
keeping the stack 8-byte aligned), with `lr` kept in `r4` across the call,
which preserves `r4`. -/
def ecbCall (dir : Dir) : Prog isa :=
  .frame (.push [.r4, .lr])
    (.seq (.block [.mov .r4 (.reg .lr), .mov .r3 (.imm (match dir with | .encrypt => 0 | .decrypt => 1))])
      (.seq (.call "vg_sm4_ecb" ecbAnyCode) (.block [.mov .lr (.reg .r4)])))
    (.pop .r4 8)

/-- The code of `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`, as its
artifact has it. -/
def ecbCode (dir : Dir) : Prog isa := ecbCall dir

/-- SM4's ECB function in the direction `dir`, as the modes call it. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Sm4.ecbEncryptApi.name
    | .decrypt => Spec.Sm4.ecbDecryptApi.name
  code := ecbCode dir
  bw := 4

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq cbcDecChained

end VG.Impl.Sm4.Arm
