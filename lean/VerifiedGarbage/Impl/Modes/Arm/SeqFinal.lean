module

public import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# CFB of a message's last piece on ARMv7, for any block cipher

`seqFinal core mode`: `seq` (`Seq.lean`) over the `len` bytes at the data,
in segments of a block, `L = bs` bytes, the last of which may be shorter,
as on x86-64 and AArch64 (`Impl/Modes/X86_64/FbFinal.lean`,
`Impl/Modes/AArch64/FbFinal.lean`). The arguments are `seq`'s, but the
count, in `r7`, is the bytes left, not the blocks.

Each segment (`seg`) calls the core on the chaining block (the mode's
operations before the call are none: `cfbEnc`'s, and `cfbDecF`'s, which
reads the data block only after the call, so that a partial segment reads
only its bytes), giving `Oⱼ`. Then `r9 := r7 >> lg` (`L = 2 ^ lg`) is zero
exactly when fewer than `L` bytes are left (`segTest`). If a whole block is
left, the mode's operations after the call (`post`), and on by `L` bytes
(`advanceBytes`, which sets Z when none is left). If fewer, `r`, the first
`r` bytes of `Oⱼ` are XORed into the data a byte at a time (`xorByte`,
through `r0` into the chaining block, `r9` and `r10`), which leaves none
and Z set; `Oⱼ` stays in the chaining block, the block to continue from,
which goes back to the IV at the end as after a whole one. The core is
called once per segment, from one call site.

As in `seq`, only the pointers and `len` can affect timing: the branches are
on the count alone.
-/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- The data's byte at `r6` XORed with the byte at `r0`, through `r9` and
`r10`; both on to the next byte, and one fewer left in `r7` (Z set after the
last). -/
def xorByte : List Instr :=
  [.ldrb .r9 .r6 0, .ldrb .r10 .r0 0, .dp .eor .r9 .r9 (.reg .r10), .strb .r9 .r6 0,
   .dp .add .r0 .r0 (.imm 1), .dp .add .r6 .r6 (.imm 1), .subs .r7 .r7 (.imm 1)]

/-- A partial segment: the chaining block's first bytes XORed into the
bytes left, none left after them. -/
def tailCode : Prog isa :=
  .seq (.block [.dp .add .r0 .r8 (.imm (BitVec.ofNat 32 oOff))]) (.loop (.block xorByte) .ne)

namespace Core

variable (c : Core)

/-- `lg` with `bs = 2 ^ lg`, for blocks of a power of two bytes. -/
def lg : Nat := Nat.log2 c.bs

/-- `r9 := r7 >> lg`, Z set when it is zero: fewer than a block's bytes
left. -/
def segTest : List Instr := [.mov .r9 (.shifted .r7 .lsr c.lg), .cmp .r9 (.imm 0)]

/-- On by a block, a block's bytes fewer left (Z set when none is left). -/
def advanceBytes : List Instr :=
  [.dp .add .r6 .r6 (.imm (BitVec.ofNat 32 c.bs)), .subs .r7 .r7 (.imm (BitVec.ofNat 32 c.bs))]

/-- After the call: a partial segment, or the mode's operations and on to
the next. -/
def segRest (m : Mode) : Prog isa :=
  .seq (.block c.segTest) (.ite .eq tailCode (.block (c.opsCode m.post ++ c.advanceBytes)))

/-- One segment: the call on the chaining block, then `segRest`. -/
def seg (m : Mode) : Prog isa :=
  .seq (.block (c.callArgs .o)) (.seq c.callStep (c.segRest m))

/-- The whole function: `seq`'s, over segments. -/
def seqFinal (m : Mode) : Prog isa :=
  .seq (.block (c.save ++ c.setup)) (.seq (.ite .eq (.block []) (.loop (c.seg m) .ne))
    (.block (c.finish m ++ restore)))

end Core

/-- CFB decryption with `s = b`, the operations all after the call (for
`seqFinal`): `O := CIPH_K(O)`, `T := Cⱼ`, `Pⱼ := Cⱼ ⊕ O`, `O := T`. -/
def cfbDecF : Mode := { pre := [], tgt := .o, post := [.copy .t .d, .xor .d .o, .copy .o .t], finish := true }

end VG.Impl.Modes.Arm
