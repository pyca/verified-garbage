module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq

/-!
# CFB of a message's last piece on PPC64LE, for any block cipher

`seqFinal core mode`: `seq` (`Seq.lean`) over the `len` bytes at the data,
in segments of a block, `L = 4 bw` bytes, the last of which may be shorter
(for CFB with segments of a whole block, the extension of SP 800-38A §6.3
that `Spec/Cfb/Final.lean` states), as on x86 (`Impl/Modes/X86/SeqFinal.lean`).
The arguments are `seq`'s, `f(key = r3, iv = r4, data = r5, len = r6,
scratch = r7)`, but the count, in `r30`, is the bytes left, not the steps.

Each segment is `pre` and the core's `crypt`, as a step of `seq`, giving
`Oⱼ` in the buffer (the modes here, whose `pre` copies the chaining value to
the buffer, never read the data before `crypt`, so that a partial segment
reads only its bytes). Then `r8 := r30 >> lg` (`L = 2 ^ lg`) is zero exactly
when fewer than `L` bytes are left (`segTest`): PPC64LE branches on a
register being zero. If a whole block is left, `post`, and on by `L` bytes
(`advanceBytes`). If fewer, `r`, the buffer is copied to the chaining value
(`Oⱼ`, the block to continue from, which goes back to the IV at the end as
after a whole one), and the first `r` bytes of the buffer are XORed into the
data a byte at a time (`tailByte`, through `r8`, `r9` and `r10`), which
leaves none. The core is inlined once, in the loop's body.

As in `seq`, only the pointers and `len` are public: no address or branch
depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes

/-- The data's byte at `r31` XORed with the byte at `r8`, through `r9` and
`r10`; both on to the next byte, and one fewer left in `r30`. -/
def tailByte : List Instr :=
  [.lbz .r9 .r31 0, .lbz .r10 .r8 0, .logic .xor .r9 .r9 .r10, .stb .r9 .r31 0,
   .addi .r8 .r8 1, .addi .r31 .r31 1, .subi .r30 .r30 1]

namespace Core

variable (c : Core)

/-- `lg` with `4 bw = 2 ^ lg`. -/
def lg : Nat := Nat.log2 (4 * c.bw)

/-- `r8 := r30 >> lg`: zero when fewer than a block's bytes are left. -/
def segTest : List Instr := [.lsr .d .r8 .r30 c.lg]

/-- On by a block, a block's bytes fewer left. -/
def advanceBytes : List Instr := [.addi .r31 .r31 (4 * c.bw), .subi .r30 .r30 (4 * c.bw)]

/-- A partial segment: the buffer to the chaining value, and its first
bytes XORed into the bytes left, none left after them. -/
def tailCode : Prog isa :=
  .seq (.block (c.opsCode (copyBlk c.bw .chn .buf) ++ ([.addi .r8 sb (8 * c.buf)] : List Instr)))
    (.loop (.block tailByte) (.nonzero .d .r30))

/-- After `crypt`: a partial segment, or `post` and on to the next. -/
def segRest (m : Mode) : Prog isa :=
  .seq (.block c.segTest) (.ite (.zero .d .r8) c.tailCode (.block (c.opsCode m.post ++ c.advanceBytes)))

/-- One segment. -/
def seg (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode m.pre)) (.seq c.crypt (c.segRest m))

/-- The whole function: `seq`'s, over segments, the chaining value always
back to the IV. -/
def seqFinal (m : Mode) : Prog isa :=
  .seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare
    (.seq (.ite (.zero .d .r30) (.block []) (.loop (c.seg m) (.nonzero .d .r30)))
      (.block (c.ivBack ++ c.restore))))

end Core

end VG.Impl.Modes.PPC64LE
