module

public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# AES-GCM's counter blocks, kept in memory

The AVX-512 loops (`Impl.Gcm.X86_64.StitchZ` and the loops built on it) keep
the sixteen counter blocks of the next group in the working space, at
`scratch + slot` (`r11 + slot`), rather than in `zmm14`: a group loads its
blocks' counters into `zmm3` … from there, as they are in memory, then writes
the next group's, with the counter in `r10d` (`refill`): for each block, the
32 bits `inc₃₂` increments, byte-reversed (`bswap32`), over the last four
bytes of the block, whose first twelve are those of the first counter block
and never change. That takes the counters' byte reversal and additions off
the vector ports, which the loop is bound by, onto the scalar ones; nothing
depends on the counter but the values written, so it stays secret.

The counter is the 32 bits `inc₃₂` increments of the slot's first block,
read back from it for each group. `r10` holds the address of the last round
key through the loops, so they compute it again from `rdi` and `rsi` after
each use of `r10d` (`restoreK`): a value loaded from memory would be secret
to the constant-time analysis, which an address may not be.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Slot

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)

/-- Where the sixteen counter blocks are, in the working space. -/
def slot : Nat := 1024

/-- Counter block `i` of the slot: its last four bytes from `r10d`
(byte-reversed), and `r10d` advanced. -/
def put (i : Nat) : List Instr :=
  [.bswap32 .r10, .store32 (at_ .r11 (slot + 16 * i + 12)) .r10, .bswap32 .r10, .alu32 .add .r10 (.imm 1)]

/-- Counter blocks `0` … `n - 1` of the slot. -/
def puts : Nat → List Instr
  | 0 => []
  | n + 1 => puts n ++ put n

/-- The address of the last round key back in `r10`: `rdi + 16 rsi`. -/
def restoreK : List Instr :=
  [.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

/-- The sixteen counter blocks after the first `d`, written over the slot,
from the counter of its first block (its last four bytes, byte-reversed),
through `r10d`; then the address of the last round key back in `r10`. -/
def refill (d : Nat) : List Instr :=
  ([.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10, .alu32 .add .r10 (.imm (BitVec.ofNat 32 d))] :
    List Instr) ++ puts 16 ++ restoreK

/-- The counter blocks of the registers `rs`, from the `k`-th four of the slot. -/
def loads : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, k => .vmovdqu32Load b (at_ .r11 (slot + 64 * k)) :: loads bs (k + 1)

/-- The counter blocks of a group in the registers `rs`, and the next
group's in the slot. -/
def ctrsM (rs : List XReg) : List Instr := loads rs 0 ++ refill (4 * rs.length)

/-- `zmm13` (four copies of the first counter block) stored over the first
`n` fours of the slot. -/
def copies : Nat → List Instr
  | 0 => []
  | n + 1 => copies n ++ ([.vmovdqu32Store (at_ .r11 (slot + 64 * n)) .xmm13] : List Instr)

/-- The first counter block at `rax` copied into the sixteen of the slot
(through `zmm13`), before the sixteen counters are written from its counter
through `r10d`: the slot then holds the first group, and `r10` the address of
the last round key again. -/
def init : List Instr :=
  ([.vbroadcasti32x4 .xmm13 (at_ .rax 0)] : List Instr) ++ copies 4 ++
  ([.mov32 .r10 (.mem (at_ .rax 12)), .bswap32 .r10] : List Instr) ++ puts 16 ++ restoreK

/-- The counter of the slot's first block stored to `rax`. -/
def storeCtr : List Instr :=
  [.vmovdquLoad .l128 .xmm13 (at_ .r11 slot), .vmovdquStore .l128 (at_ .rax 0) .xmm13]

/-- The counter `r9 - 16` blocks after the slot's first stored to `rax`,
through `r10d`. -/
def storeCtrAt : List Instr :=
  storeCtr ++ ([.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10, .alu32 .add .r10 (.reg .r9),
    .alu32 .sub .r10 (.imm 16), .bswap32 .r10, .store32 (at_ .rax 12) .r10] : List Instr)

end VG.Impl.Gcm.X86_64.Slot
