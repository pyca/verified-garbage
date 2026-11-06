module

public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's ECB functions on ARMv7, as the modes call them

The code of `vg_sm4_ecb` as its artifact has it (`ecbAnyCode`), and SM4's
ECB functions, `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`, which call it
(`ecbCall`).
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

end VG.Impl.Sm4.Arm
