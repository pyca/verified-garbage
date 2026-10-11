import VerifiedGarbage.TCB.Arm.Isa

/-!
# Block cipher modes on ARMv7, one block at a time, for any block cipher

`seq core mode`: a mode of operation (CBC, OFB, CFB) over a block cipher's
*core* (`Core`): its ECB function, `f(schedule = r0, data = r1, n = r2)`,
which replaces `n` blocks of `bw` 32-bit words at `data` with their
encryptions (or decryptions) in place, and which the mode calls (`bl`) once
for each block, with `n = 1`. Each cipher's ECB function is already an
artifact, so the mode adds no cryptographic code of its own.

The function, `(schedule = r0, iv = r1, data = r2, n = r3, scratch = [sp])`,
with `scratch` working space of `scratchBytes core` bytes:

* `save`: our caller's `r4`–`r11` and our return address `lr` to the first
  36 bytes of the scratch buffer; `setup`: the schedule's address to `r4`,
  the IV's to `r5`, the data's to `r6` (the next block), `n` to `r7` (the
  blocks left), the scratch buffer's to `r8`, and the IV copied to the
  *chaining block* `O` (at `r8 + oOff`); Z is set if there are no blocks.
* Each block (`body`): the mode's block operations before the call
  (`mode.pre`), the call on the chaining block or on the data block
  (`mode.tgt`), the operations after it (`mode.post`), and on to the next
  block. The operations (`Op`) copy a block to another or XOR it into
  another, a word at a time through `r9` and `r10`; the blocks are the data
  block `D` (at `r6`), the chaining block `O` and a spare block `T` (at
  `r8 + oOff + 4 bw`).
* `mode.finish`: the chaining block back to the IV, if the mode returns the
  value to continue from there; and our caller's registers restored.

The callee may change `r0`–`r3`, `r12`, `lr` and the flags (and our scratch
buffer is above the stack pointer, out of its reach); the mode keeps what it
needs in `r4`–`r8`, which the callee preserves.

Only the pointers and `n` can affect timing: the only branches are on `n`,
and the callee is constant time with the same public data.
-/

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- A block cipher's ECB function, as a mode calls it: its name and code (an
artifact's), and its blocks' size in 32-bit words. -/
structure Core where
  name : String
  code : Prog isa
  bw : Nat

/-- The blocks a mode works on: the data block (`r6`), the chaining block
and the spare block (in the scratch buffer). -/
inductive Blk | d | o | t
  deriving DecidableEq, Repr

/-- A block operation: `copy x y` stores block `y` in block `x`, `xor x y`
XORs block `y` into block `x`; `xorB x y` XORs the first byte of `y` into
the first byte of `x`, and `shift x y` shifts block `x` left by a byte,
with the first byte of `y` shifted in (for CFB8). -/
inductive Op
  | copy (x y : Blk)
  | xor (x y : Blk)
  | xorB (x y : Blk)
  | shift (x y : Blk)
  deriving DecidableEq, Repr

/-- A mode, one block at a time: the operations before the call, the block
the cipher is applied to, the operations after it, whether the chaining
block is returned in the IV, and whether the data comes a byte at a time
(CFB8: the data block is then a single byte) rather than a block at a
time. -/
structure Mode where
  pre : List Op
  tgt : Blk
  post : List Op
  finish : Bool
  byte : Bool := false

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .mov d (.reg n)

/-- Word `w` of the block at `rs + os` stored in the block at `rd + od`,
through `r9`. -/
def copyWord (rd rs : Reg) (od os w : Nat) : List Instr :=
  [.ldr .r9 rs (os + 4 * w), .str .r9 rd (od + 4 * w)]

/-- Word `w` of the block at `rs + os` XORed into the block at `rd + od`,
through `r9` and `r10`. -/
def xorWord (rd rs : Reg) (od os w : Nat) : List Instr :=
  [.ldr .r9 rd (od + 4 * w), .ldr .r10 rs (os + 4 * w), .dp .eor .r9 .r9 (.reg .r10), .str .r9 rd (od + 4 * w)]

/-- The offset of the chaining block in the scratch buffer. -/
def oOff : Nat := 40

/-- The saved registers and their offsets in the scratch buffer. -/
def saved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32), (.r8, 16)]

/-- Saves them, with the scratch buffer (the first stack argument) in `r12`. -/
def save : List Instr := .ldrSp .r12 0 :: saved.map fun (r, d) => .str r .r12 d

/-- Restores them, with `r8` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r8 d

namespace Core

variable (c : Core)

/-- The size of a block, in bytes. -/
def bs : Nat := 4 * c.bw

/-- The size of the data's elements, in bytes, under the mode `m`: a block,
or a byte. -/
def ds (m : Mode) : Nat := if m.byte then 1 else c.bs

/-- The scratch buffer's size: the saved registers (and a word to keep the
blocks 8-byte aligned), the chaining block and the spare block. -/
def scratchBytes : Nat := oOff + 2 * c.bs

/-- Where a block is: its base register and offset. -/
def base : Blk → Reg × Nat
  | .d => (.r6, 0)
  | .o => (.r8, oOff)
  | .t => (.r8, oOff + c.bs)

/-- A block operation, a word at a time. -/
def opCode : Op → List Instr
  | .copy x y => (List.range c.bw).flatMap (copyWord (c.base x).1 (c.base y).1 (c.base x).2 (c.base y).2)
  | .xor x y => (List.range c.bw).flatMap (xorWord (c.base x).1 (c.base y).1 (c.base x).2 (c.base y).2)
  | .xorB x y =>
    [.ldrb .r9 (c.base x).1 (c.base x).2, .ldrb .r10 (c.base y).1 (c.base y).2, .dp .eor .r9 .r9 (.reg .r10),
     .strb .r9 (c.base x).1 (c.base x).2]
  | .shift x y =>
    (List.range (c.bs - 1)).flatMap (fun k =>
      [.ldrb .r9 (c.base x).1 ((c.base x).2 + k + 1), .strb .r9 (c.base x).1 ((c.base x).2 + k)]) ++
    [.ldrb .r9 (c.base y).1 (c.base y).2, .strb .r9 (c.base x).1 ((c.base x).2 + (c.bs - 1))]

/-- A list of block operations. -/
def opsCode (ops : List Op) : List Instr := ops.flatMap c.opCode

/-- The arguments to their registers, and the IV (at `r5`) to the chaining
block; Z is set if there are no blocks. -/
def setup : List Instr :=
  [mov .r4 .r0, mov .r5 .r1, mov .r6 .r2, mov .r7 .r3, mov .r8 .r12] ++
    (List.range c.bw).flatMap (copyWord .r8 .r5 oOff 0) ++
    [.cmp .r7 (.imm 0)]

/-- The arguments of the call on block `x`: the schedule, the block, `n = 1`. -/
def callArgs (x : Blk) : List Instr :=
  [mov .r0 .r4, .dp .add .r1 (c.base x).1 (.imm (BitVec.ofNat 32 (c.base x).2)), .mov .r2 (.imm 1)]

/-- On to the next block, or byte (Z is set when none are left). -/
def advance (m : Mode) : List Instr := [.dp .add .r6 .r6 (.imm (BitVec.ofNat 32 (c.ds m))), .subs .r7 .r7 (.imm 1)]

/-- The chaining block back to the IV, if the mode returns it. -/
def finish (m : Mode) : List Instr :=
  if m.finish then (List.range c.bw).flatMap (copyWord .r5 .r8 0 oOff) else []

/-- One block. -/
def body (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode m.pre ++ c.callArgs m.tgt)) (.seq (.call c.name c.code)
    (.block (c.opsCode m.post ++ c.advance m)))

/-- The whole function. -/
def seq (m : Mode) : Prog isa :=
  .seq (.block (save ++ c.setup)) (.seq (.ite .eq (.block []) (.loop (c.body m) .ne))
    (.block (c.finish m ++ restore)))

end Core

/-! ## The modes -/

/-- CBC encryption (SP 800-38A §6.2): `O ⊕= Pⱼ`, `O := CIPH_K(O)`, `Cⱼ := O`. -/
def cbcEnc : Mode := { pre := [.xor .o .d], tgt := .o, post := [.copy .d .o], finish := false }

/-- CBC decryption: `T := Cⱼ`, `Cⱼ := CIPH⁻¹_K(Cⱼ)`, `Pⱼ := Cⱼ ⊕ O`, `O := T`. -/
def cbcDec : Mode := { pre := [.copy .t .d], tgt := .d, post := [.xor .d .o, .copy .o .t], finish := false }

/-- OFB (SP 800-38A §6.4), encryption and decryption: `O := CIPH_K(O)`,
`Yⱼ := Xⱼ ⊕ O`; the last output block is returned in the IV. -/
def ofb : Mode := { pre := [], tgt := .o, post := [.xor .d .o], finish := true }

/-- CFB encryption with `s = b` (§6.3): `O := CIPH_K(O)`, `Cⱼ := Pⱼ ⊕ O`,
`O := Cⱼ`; the last ciphertext block is returned in the IV. -/
def cfbEnc : Mode := { pre := [], tgt := .o, post := [.xor .d .o, .copy .o .d], finish := true }

/-- CFB decryption with `s = b`: `T := Cⱼ`, `O := CIPH_K(O)`,
`Pⱼ := Cⱼ ⊕ O`, `O := T`; the last ciphertext block is returned in the IV. -/
def cfbDec : Mode := { pre := [.copy .t .d], tgt := .o, post := [.xor .d .o, .copy .o .t], finish := true }

/-- CFB8 encryption (§6.3, `s = 8`), a byte at a time: `T := I` (the input
block, in the chaining block), `T := CIPH_K(T)`, `C#ⱼ := P#ⱼ ⊕ MSB₈(T)`, and
`C#ⱼ` shifted into `I`, which is returned in the IV. -/
def cfb8Enc : Mode :=
  { pre := [.copy .t .o], tgt := .t, post := [.xorB .d .t, .shift .o .d], finish := true, byte := true }

/-- CFB8 decryption: as encryption, with `C#ⱼ` shifted into `I` before
`P#ⱼ := C#ⱼ ⊕ MSB₈(T)` replaces it. -/
def cfb8Dec : Mode :=
  { pre := [.copy .t .o], tgt := .t, post := [.shift .o .d, .xorB .d .t], finish := true, byte := true }

end VG.Impl.Modes.Arm
