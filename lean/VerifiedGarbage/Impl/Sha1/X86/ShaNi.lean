import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.X86.Isa

/-!
# SHA-1 compression function: x86 (32-bit) implementation with the SHA extensions

`vg_sha1_compress_shani(state, blocks, n, scratch)`, cdecl (the arguments at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`), with the contract
of `vg_sha1_compress`, for CPUs with the SHA extensions and SSSE3.

The x86-64 implementation (`Impl/Sha1/X86_64/ShaNi.lean`) with eight XMM
registers instead of sixteen:

* The working variables `a, b, c, d` are kept as `ABCD` in `xmm0` (`A` in
  bits 127:96, as `sha1rnds4` reads them). `e` is not kept: `sha1rnds4` adds
  it to the first message word it is given, and four rounds later it is the
  old `A` rotated left by 30, which `sha1nexte` adds to the next message
  word. So `xmm1` holds the value of `xmm0` before the last four rounds, or,
  at the start of a block, `e` in bits 127:96 and zeros elsewhere.
* The message schedule is kept four words to a register, `W₄ᵢ … W₄ᵢ₊₃` in
  `xmm(3 + i mod 4)` (`W₄ᵢ` in bits 127:96), computed with `sha1msg1`, `pxor`
  and `sha1msg2`.
* `xmm7` holds the `pshufb` mask that reverses the bytes of a register, which
  makes the message words big-endian and puts the first in bits 127:96; it is
  built from immediates through `eax` and `xmm2`. `xmm2` is a temporary.
* `xmm0` and `xmm1` at the start of a block are kept in `scratch[0..32)`
  (where x86-64 keeps them in `xmm8` and `xmm9`), and added back at its end.
* `eax` counts the blocks left, `ecx` points to the next block and `edx` to
  `scratch`; the state pointer is read from its argument slot when the hash
  value is loaded and stored. The hash value is loaded and stored 16 bytes
  at a time: `e` is loaded with `b, c, d` from `state + 4`, and stored with
  them there before `a, b, c, d` are stored at `state`.
* Only `eax`, `ecx` and `edx` (caller-saved) are written, so nothing is
  saved. `esp` and the arguments (the pointers and the block count) are
  public; no address and no branch depends on anything else.
-/

namespace VG.Impl.Sha1.X86.ShaNi

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃`. -/
def msg (i : Nat) : XReg := [.xmm3, .xmm4, .xmm5, .xmm6].getD (i % 4) .xmm3

/-- The `pshufb` mask that reverses the bytes of a register. -/
def bswapMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128

/-- The 128-bit constant `c` into `xmm7`, a doubleword at a time through
`eax` and `xmm2`. -/
def const (c : BitVec 128) : List Instr :=
  [.mov .eax (.imm (dword c 0)), .xop (.movd .xmm7 .eax),
   .mov .eax (.imm (dword c 1)), .xop (.movd .xmm2 .eax),
   .xop (.bin .punpckldq .xmm7 .xmm2),
   .mov .eax (.imm (dword c 2)), .xop (.movd .xmm2 .eax),
   .xop (.bin .punpcklqdq .xmm7 .xmm2),
   .mov .eax (.imm (dword c 3)), .xop (.movd .xmm2 .eax),
   .xop (.shift .pslldq .xmm2 12), .xop (.bin .por .xmm7 .xmm2)]

/-- `W₄ᵢ … W₄ᵢ₊₃` into `msg i`: loaded from the block for `i < 4`, otherwise
from the previous sixteen words (whose register `msg i` held the oldest four). -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.movdquLoad (msg i) (at_ .ecx (16 * i)), .xop (.bin .pshufb (msg i) .xmm7)]
  else
    [.xop (.bin .sha1msg1 (msg i) (msg (i + 1))),
     .xop (.bin .pxor (msg i) (msg (i + 2))),
     .xop (.bin .sha1msg2 (msg i) (msg (i + 3)))]

/-- Rounds `4i … 4i+3`, with `W₄ᵢ … W₄ᵢ₊₃` in `msg i`: `e` is added to `W₄ᵢ`
(for `i = 0`, it is in `xmm1`; after that, `sha1nexte` computes it from the
`ABCD` of four rounds before), and `sha1rnds4` selects the function and
constant of rounds `4i … 4i+3`, which are in group `i / 5` of 20 rounds. -/
def rounds4 (i : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm2 .xmm0),
   .xop (.bin (if i = 0 then .paddd else .sha1nexte) .xmm1 (msg i)),
   .xop (.sha1rnds4 .xmm0 .xmm1 (BitVec.ofNat 8 (i / 5))),
   .xop (.bin .movdqa .xmm1 .xmm2)]

/-- Rounds `0 … 4n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

/-- Keep `xmm0` and `xmm1` in `scratch[0..32)`. -/
def save : List Instr :=
  [.movdquStore (at_ .edx 0) .xmm0, .movdquStore (at_ .edx 16) .xmm1]

/-- Add them back, and move to the next block. -/
def finish : List Instr :=
  [.movdquLoad .xmm2 (at_ .edx 0), .xop (.bin .paddd .xmm0 .xmm2),
   .movdquLoad .xmm2 (at_ .edx 16), .xop (.bin .sha1nexte .xmm1 .xmm2),
   .alu .add .ecx (.imm 64), .alu .sub .eax (.imm 1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block save) (.seq (rounds 20) (.block finish))

/-- Load the hash value `H₀ … H₄` as `ABCD` into `xmm0` and `E` into bits
127:96 of `xmm1`. -/
def loadState : List Instr :=
  [.mov .edx (.mem (at_ .esp 4)),
   .movdquLoad .xmm0 (at_ .edx 0), .xop (.pshufd .xmm0 .xmm0 0x1b),
   .movdquLoad .xmm1 (at_ .edx 4), .xop (.shift .psrldq .xmm1 12),
   .xop (.shift .pslldq .xmm1 12)]

/-- The pointers and the count of blocks into registers. -/
def loadArgs : List Instr :=
  [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.mem (at_ .esp 16)), .mov .eax (.mem (at_ .esp 12)),
   .alu .test .eax (.reg .eax)]

def load : List Instr := loadState ++ const bswapMask ++ loadArgs

/-- Store `ABCD` and `E` back as the hash value: `H₁ … H₄` at `state + 4`,
then `H₀ … H₃` at `state`. -/
def store : List Instr :=
  [.mov .edx (.mem (at_ .esp 4)),
   .xop (.pshufd .xmm0 .xmm0 0x1b),
   .xop (.bin .movdqa .xmm2 .xmm0),
   .xop (.shift .psrldq .xmm2 4),
   .xop (.bin .por .xmm2 .xmm1),
   .movdquStore (at_ .edx 4) .xmm2, .movdquStore (at_ .edx 0) .xmm0]

def compress : Prog isa :=
  .seq (.block load)
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block store))

end VG.Impl.Sha1.X86.ShaNi
