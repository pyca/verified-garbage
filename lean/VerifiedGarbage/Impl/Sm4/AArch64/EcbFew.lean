module

public import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
public import VerifiedGarbage.Impl.Modes.AArch64.Ecb
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# SM4-ECB on AArch64: a few blocks one at a time

`ecbFew d c` is `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`: for fewer than
seven blocks (`few7`, on `x2`) the modes' generic ECB
(`Impl/Modes/AArch64/Ecb.lean`) over the one-block core of the direction,
in a frame of its working space (`ecbShortFramed`); otherwise the call of
`vg_sm4_ecb` (`ecbCall`, whose code is `c`), which runs the bitsliced batch
of sixteen. Only `n` decides which.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64
open VG.Spec.Sm4 (Direction)

/-- ECB encryption one block at a time (schedule = x0, data = x1, n = x2,
scratch = x3). -/
def ecbShortEncrypt : Prog isa := Serial.core.ecb .x1 .x2 .x3

/-- ECB decryption one block at a time. -/
def ecbShortDecrypt : Prog isa := Serial.decCore.ecb .x1 .x2 .x3

def ecbShort : Direction → Prog isa
  | .encrypt => ecbShortEncrypt
  | .decrypt => ecbShortDecrypt

/-- `ecbShort` with its working space, 408 words, on the stack, zeroed on
return. -/
def ecbShortFramed (d : Direction) : Prog isa :=
  Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x3 408 (ecbShort d)

/-- The direction `ecbCall` takes. -/
def callDir : Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`, with `vg_sm4_ecb`'s code `c`. -/
def ecbFew (d : Direction) (c : Prog isa) : Prog isa :=
  few7 .x2 (ecbShortFramed d) (ecbCall (callDir d) c)

end VG.Impl.Sm4.AArch64
