module

public import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# OFB and CFB of a message's last piece on x86 (32-bit), for any block cipher

`seqFinal core mode`: `seq` (`Seq.lean`) over the `len` bytes at the data,
in segments of a block, `L = 4 bw` bytes, the last of which may be shorter
(SP 800-38A §6.4 for OFB, whose last block may be partial; for CFB with
segments of a whole block, the same extension of §6.3), as on x86-64
(`Impl/Modes/X86_64/FbFinal.lean`). The arguments are `seq`'s,
`f(key, iv, data, len, scratch)`, but the count, in `nSlot` and `ebp`, is
the bytes left, not the blocks.

Each segment is `pre` and the core's `crypt`, as a step of `seq`, giving
`Oⱼ` in the buffer; then the data pointer and the bytes left are loaded
again and compared with `L`. If a whole block is left, `post`, and on by `L`
bytes (`advanceBytes`, which sets ZF when none is left). If fewer, `r`, the
buffer is copied to the chaining value (`Oⱼ`, the block to continue from,
which goes back to the IV at the end as after a whole one), and the first
`r` bytes of the buffer are XORed into the data a byte at a time
(`tailByte`, through `ebx`, `esi` and `ebp`), which leaves none and ZF set.
Both ways end by storing the data pointer and the count back from
registers (`storeBack`): the stores through `esi` make the analysis of
constant time forget what the scratch buffer holds, and the loop's analysis
meets the two ways.
The core is called once per segment, so its code appears once; the modes
here (`pre` copies the chaining value to the buffer) never read the data
before `crypt`, so the partial segment reads only its `r` bytes.

As in `seq`, only the pointers and `len` are public: no address or branch
depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.X86

open VG.X86
open VG.Impl.Modes

/-- The byte at `ebx` XORed into the byte at `esi`, through `eax` and
`ecx`; both on to the next byte, and one fewer left in `ebp`, ZF set after
the last. -/
def tailByte : List Instr :=
  [.movzx8 .eax (at_ .ebx 0), .movzx8 .ecx (at_ .esi 0), .alu .xor .ecx (.reg .eax), .store8 (at_ .esi 0) .cl,
   .alu .add .ebx (.imm 1), .alu .add .esi (.imm 1), .alu .sub .ebp (.imm 1)]

namespace Core

variable (c : Core)

/-- The buffer's first block's address, to `ebx`. -/
def tailStart : List Instr := [.mov .ebx (.reg sb), .alu .add .ebx (.imm (BitVec.ofNat 32 (4 * c.buf)))]

/-- The data pointer and the bytes left back to their slots, from `esi`
and `ebp`. -/
def storeBack : List Instr := [.store (slotAt c.dSlot) .esi, .store (slotAt c.nSlot) .ebp]

/-- On by a block, a block's bytes fewer left (ZF set when none is left),
both stored back. -/
def advanceBytes : List Instr :=
  ([.alu .add .esi (.imm (BitVec.ofNat 32 (4 * c.bw))), .alu .sub .ebp (.imm (BitVec.ofNat 32 (4 * c.bw)))] :
    List Instr) ++ c.storeBack

/-- After `crypt`, with the data pointer and the bytes left in `esi` and
`ebp` compared with a block (CF set if fewer are left): if fewer, the
buffer to the chaining value and its first bytes XORed into the data, none
left (the pointer and the count stored back); otherwise `post` and on to
the next segment. -/
def segOp (m : Mode) : Prog isa :=
  .ite .b (.seq (.block (c.opsCode (copyBlk c.bw .chn .buf) ++ c.tailStart))
      (.seq (.loop (.block tailByte) .ne) (.block c.storeBack)))
    (.block (c.opsCode m.post ++ c.advanceBytes))

/-- One segment. -/
def seg (m : Mode) : Prog isa :=
  .seq (.block (c.load ++ c.opsCode m.pre)) (.seq c.crypt
    (.seq (.block (c.load ++ ([.alu .cmp .ebp (.imm (BitVec.ofNat 32 (4 * c.bw)))] : List Instr))) (c.segOp m)))

/-- The whole function: `seq`'s, over segments, the chaining value always
back to the IV. -/
def seqFinal (m : Mode) : Prog isa :=
  .seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare (.seq (.block c.args)
    (.seq (.ite .e (.block []) (.loop (c.seg m) .ne)) (.block (c.ivBack ++ c.restore)))))

end Core

end VG.Impl.Modes.X86
