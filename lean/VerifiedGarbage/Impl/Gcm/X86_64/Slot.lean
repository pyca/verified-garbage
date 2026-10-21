module

public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# AES-GCM's counter blocks, kept in memory

The AVX-512 loops with cached round keys (`Impl.Gcm.X86_64.StitchZH`) keep
the sixteen counter blocks of the next group in the working space, at
`scratch + slot` (`r11 + slot`), rather than in `zmm14`: a group loads its
blocks' counters into `zmm3` … from there, as they are in memory, then writes
the next group's, with the counter in `ecx` (`refill`): for each block, the
32 bits `inc₃₂` increments, byte-reversed (`bswap32`), over the last four
bytes of the block, whose first twelve are those of the first counter block
and never change. That takes the counters' byte reversal and additions off
the vector ports, which the loop is bound by, onto the scalar ones; nothing
depends on the counter but the values written, so it stays secret.

The counter is the 32 bits `inc₃₂` increments of the slot's first block,
read back from it for each group. `rcx` holds the address of `Y` throughout
the loops, so they keep it at `scratch + ySave`, and reload it after each use
of `ecx`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Slot

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)

/-- Where the sixteen counter blocks are, in the working space. -/
def slot : Nat := 1024

/-- Where the address of `Y` is kept, in the working space. -/
def ySave : Nat := 1280

/-- Counter block `i` of the slot: its last four bytes from `ecx`
(byte-reversed), and `ecx` advanced. -/
def put (i : Nat) : List Instr :=
  [.bswap32 .rcx, .store32 (at_ .r11 (slot + 16 * i + 12)) .rcx, .bswap32 .rcx, .alu32 .add .rcx (.imm 1)]

/-- Counter blocks `0` … `n - 1` of the slot. -/
def puts : Nat → List Instr
  | 0 => []
  | n + 1 => puts n ++ put n

/-- The address of `Y` back in `rcx`. -/
def restoreY : List Instr := [.mov .rcx (.mem (at_ .r11 ySave))]

/-- The sixteen counter blocks after the first `d`, written over the slot,
from the counter of its first block (its last four bytes, byte-reversed),
through `ecx`; then the address of `Y` back in `rcx`. -/
def refill (d : Nat) : List Instr :=
  ([.mov32 .rcx (.mem (at_ .r11 (slot + 12))), .bswap32 .rcx, .alu32 .add .rcx (.imm (BitVec.ofNat 32 d))] :
    List Instr) ++ puts 16 ++ restoreY

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
(through `zmm13`), and the address of `Y` kept, before the sixteen counters
are written from its counter through `ecx`: the slot then holds the first
group, and `rcx` the address of `Y` again. -/
def init : List Instr :=
  ([.vbroadcasti32x4 .xmm13 (at_ .rax 0)] : List Instr) ++ copies 4 ++
  ([.store (at_ .r11 ySave) .rcx, .mov32 .rcx (.mem (at_ .rax 12)), .bswap32 .rcx] : List Instr) ++
  puts 16 ++ restoreY

/-- The counter of the slot's first block stored to `rax`. -/
def storeCtr : List Instr :=
  [.vmovdquLoad .l128 .xmm13 (at_ .r11 slot), .vmovdquStore .l128 (at_ .rax 0) .xmm13]

/-- The counter `r10` blocks after the slot's first stored to `rax`. -/
def storeCtrAt : List Instr :=
  storeCtr ++ ([.mov32 .rcx (.mem (at_ .r11 (slot + 12))), .bswap32 .rcx, .alu32 .add .rcx (.reg .r10),
    .bswap32 .rcx, .store32 (at_ .rax 12) .rcx] : List Instr) ++ restoreY

end VG.Impl.Gcm.X86_64.Slot
