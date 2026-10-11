import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Impl.Idea.Key32

/-!
# IDEA on x86 (32-bit)

cdecl: the arguments are at `[esp + 4]`, `[esp + 8]`, … on entry.

## ⊙ without branches

`mulCode src` computes `edx := eax ⊙ src` on the low 16 bits of each, using
only `eax` and `edx`: each operand becomes its residue
`((x - 1) & 0xffff) + 1` (0 stands for 2¹⁶), `mul` (whose timing does not
depend on its operands) gives their product `p ≤ 2³²` in `edx:eax`, of which
the code keeps `q = p - 1 < 2³²`, the low half less one. Since `2¹⁶ ≡ -1`,
`p ≡ q_lo + 1 - q_hi` modulo 2¹⁶ + 1, which adding its sign bit and keeping
the low 16 bits corrects to `0 … 2¹⁶`, as on ARMv7 (`Impl/Idea/Arm.lean`):
no branch, no division.

## `vg_idea_expand_key` (`key`, `schedule`)

Each 32-bit word of the schedule (two subkeys) is a fixed bit permutation of
the key's four 32-bit words (`Impl.Idea.expandGroups32`): a group of bits
with the same rotation at a time is loaded from the key (at `eax`),
rotated and masked in `edx`, and stored to (the first) or XORed into the
schedule word (at `ecx`). Only `eax`, `ecx` and `edx` are written.

## `vg_idea_invert_key` (`schedule`, `inverse`, scratch)

`ebx`, `esi`, `edi` and `ebp` are saved in the scratch buffer (four words)
and restored. Each decryption subkey is a copy, the negation or the
⊙-inverse of an encryption subkey (at `esi`; `Impl.Idea.invOp`), the inverse
`a ^ (2¹⁶ - 1)` by fifteen iterations of `t := (t ⊙ t) ⊙ a`, a loop with a
public count (`a = ebx`, `t = ecx`, the count in `ebp`). Each is computed
into `ecx` and stored a byte at a time (at `edi`).

## `vg_idea_ecb` (`schedule`, `data`, `n`, scratch)

The scratch buffer (`slot`) holds a copy of the subkeys (bytes 0–103), a
round's `t₀` (`t0Slot`), the data pointer and the blocks left
(`dataSlot`, `leftSlot`) and the saved `ebx`, `esi`, `edi`, `ebp`
(`savedSlot`); its address is in `esi`, so one register addresses both the
subkeys and the spilled words. The subkeys are read with 32-bit loads at
their own offsets, of which the code uses the low 16 bits (the last reads
into `t₀`'s slot, which follows them).

`cryptBlock` replaces the block at the address in `dataSlot` by its
encryption under the subkeys at `esi`, writing only `eax`, `ebx`, `ecx`,
`edx`, `edi`, `ebp` and `t₀`'s slot (`cryptBlockWith` runs given code just
before the stores, which ECB uses to read the count). The block is loaded into `ebx`, `ecx`,
`edi`, `ebp` (one 16-bit word each, two 32-bit loads and `bswap`), run
through the eight rounds (unrolled) and the output transformation, and
stored by two 32-bit stores. Round `j` keeps `X₂` and `X₃` in `ecx` and
`edi` when `j` is even and in `edi` and `ecx` when it is odd, so the
exchange of the middle words costs no instruction.

After each block the data pointer and the count go back to their slots from
registers: the analysis of constant time forgets what the scratch buffer
holds after the stores through the data pointer.

The only branches are on `n` and the loop counts.
-/

namespace VG.Impl.Idea.X86

open VG.X86 VG.Impl.Idea

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Argument `i` (from 0), on entry. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-! ## ⊙ -/

/-- `edx := eax ⊙ src` (low 16 bits of each; the result zero-extended),
clobbering `eax`. -/
def mulCode (src : Src) : List Instr := [
  .alu .sub .eax (.imm 1), .alu .and .eax (.imm 0xffff), .alu .add .eax (.imm 1),
  .mov .edx src, .alu .sub .edx (.imm 1), .alu .and .edx (.imm 0xffff), .alu .add .edx (.imm 1),
  .mul .edx,
  .alu .sub .eax (.imm 1),
  .mov .edx (.reg .eax), .alu .and .edx (.imm 0xffff), .alu .add .edx (.imm 1),
  .shift .shr .eax 16, .alu .sub .edx (.reg .eax),
  .mov .eax (.reg .edx), .shift .shr .eax 31, .alu .add .edx (.reg .eax),
  .alu .and .edx (.imm 0xffff)]

/-! ## Key expansion -/

/-- One group, its key word (at `eax`) into `edx`, masked, to (the first)
or XORed into schedule word `w` (at `ecx`). -/
def groupCode (w : Nat) (first : Bool) (g : Nat × Nat × Nat) : List Instr :=
  ([.mov .edx (.mem (at_ .eax (4 * g.1)))] : List Instr) ++
  (if g.2.1 = 0 then [] else [.shift .ror .edx g.2.1]) ++
  ([.alu .and .edx (.imm (BitVec.ofNat 32 g.2.2))] : List Instr) ++
  (if first then [] else [.alu .xor .edx (.mem (at_ .ecx (4 * w)))]) ++
  [.store (at_ .ecx (4 * w)) .edx]

/-- Schedule word `w`, at `ecx + 4w`. -/
def expandWord (w : Nat) : List Instr :=
  (expandGroups32 w).zipIdx.flatMap fun (g, k) => groupCode w (k = 0) g

def expandBody : List Instr := (List.range 26).flatMap expandWord

def expandKey : Prog isa :=
  .block ([.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1))] ++ expandBody)

/-! ## Saving registers -/

/-- The callee-saved registers, at their offsets from `off` in a buffer at `b`. -/
def saveAt (b : Reg) (off : Nat) : List Instr :=
  [.store (at_ b off) .ebx, .store (at_ b (off + 4)) .esi, .store (at_ b (off + 8)) .edi,
   .store (at_ b (off + 12)) .ebp]

/-- Restoring them, `b` last (if it is one of them). -/
def restoreAt (b : Reg) (off : Nat) : List Instr :=
  [.mov .ebx (.mem (at_ b off)), .mov .edi (.mem (at_ b (off + 8))),
   .mov .ebp (.mem (at_ b (off + 12))), .mov .esi (.mem (at_ b (off + 4)))]

/-! ## Inversion -/

/-- Subkey `k` (at `esi`) into the low 16 bits of `r`: a 32-bit load at its
offset (for the last, at 100, shifted). -/
def loadKey (r : Reg) (k : Nat) : List Instr :=
  if k = 51 then [.mov r (.mem (at_ .esi 100)), .shift .shr r 16] else [.mov r (.mem (at_ .esi (2 * k)))]

/-- `t := (t ⊙ t) ⊙ a` with `t = ecx`, `a = ebx`, and the count in `ebp`. -/
def invStep : List Instr :=
  ([.mov .eax (.reg .ecx)] : List Instr) ++ mulCode (.reg .ecx) ++
  ([.mov .eax (.reg .edx)] : List Instr) ++ mulCode (.reg .ebx) ++
  ([.mov .ecx (.reg .edx), .alu .sub .ebp (.imm 1)] : List Instr)

/-- Decryption subkey `n` into `ecx`, zero-extended. -/
def invWord (n : Nat) : Prog isa :=
  match invOp n with
  | (.copy, k) => .block (loadKey .ecx k ++ ([.alu .and .ecx (.imm 0xffff)] : List Instr))
  | (.neg, k) => .block (loadKey .edx k ++
      ([.mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx), .alu .and .ecx (.imm 0xffff)] : List Instr))
  | (.inv, k) => .seq (.block (loadKey .ebx k ++ ([.mov .ecx (.reg .ebx), .mov .ebp (.imm 15)] : List Instr)))
      (.loop (.block invStep) .ne)

/-- Decryption subkey `n`, in `ecx`, stored (a byte at a time, at `edi`). -/
def invStore (n : Nat) : List Instr :=
  [.store8 (at_ .edi (2 * n)) .cl, .shift .shr .ecx 8, .store8 (at_ .edi (2 * n + 1)) .cl]

def invertKey : Prog isa :=
  .seq (.block ([.mov .eax (.mem (argOp 2))] ++ saveAt .eax 0 ++
      [.mov .esi (.mem (argOp 0)), .mov .edi (.mem (argOp 1))]))
    (.seq ((List.range 52).foldr (fun n rest => .seq (invWord n) (.seq (.block (invStore n)) rest)) (.block []))
      (.block ([.mov .eax (.mem (argOp 2))] ++ restoreAt .eax 0)))

/-! ## ECB: the scratch buffer -/

/-- A round's `t₀`. -/
def t0Slot : Nat := 104
/-- The address of the next block. -/
def dataSlot : Nat := 108
/-- The blocks left. -/
def leftSlot : Nat := 112
/-- The saved `ebx`, `esi`, `edi`, `ebp`. -/
def savedSlot : Nat := 116
/-- The scratch buffer's size, in 32-bit words. -/
def slots : Nat := 33

/-! ## A block -/

/-- The registers of `X₂` and `X₃` in round `j`. -/
def regB (j : Nat) : Reg := if j % 2 = 0 then .ecx else .edi

def regC (j : Nat) : Reg := if j % 2 = 0 then .edi else .ecx

/-- `r := (r + Zₖ) & 0xffff`. -/
def addKey (r : Reg) (k : Nat) : List Instr :=
  [.alu .add r (.mem (at_ .esi (2 * k))), .alu .and r (.imm 0xffff)]

/-- `edx := a ⊙ Zₖ`, `a` in `eax`. -/
def mulKey (k : Nat) : List Instr := mulCode (.mem (at_ .esi (2 * k)))

/-- Round `j` (0–7), with `X₁ … X₄` in `ebx`, `b`, `c`, `ebp`; after it, the
new `X₂` is in `c` and the new `X₃` in `b`. -/
def roundWith (j : Nat) (b c : Reg) : List Instr :=
  let o := 6 * j
  ([.mov .eax (.reg .ebx)] : List Instr) ++ mulKey o ++ ([.mov .ebx (.reg .edx)] : List Instr) ++
  ([.mov .eax (.reg .ebp)] : List Instr) ++ mulKey (o + 3) ++ ([.mov .ebp (.reg .edx)] : List Instr) ++
  addKey b (o + 1) ++ addKey c (o + 2) ++
  ([.mov .eax (.reg .ebx), .alu .xor .eax (.reg c)] : List Instr) ++ mulKey (o + 4) ++
  ([.store (at_ .esi t0Slot) .edx, .mov .eax (.reg b), .alu .xor .eax (.reg .ebp),
    .alu .add .eax (.reg .edx)] : List Instr) ++ mulKey (o + 5) ++
  ([.mov .eax (.mem (at_ .esi t0Slot)), .alu .add .eax (.reg .edx), .alu .and .eax (.imm 0xffff),
    .alu .xor .ebx (.reg .edx), .alu .xor c (.reg .edx),
    .alu .xor b (.reg .eax), .alu .xor .ebp (.reg .eax)] : List Instr)

def round (j : Nat) : List Instr := roundWith j (regB j) (regC j)

/-- The block at the address in `dataSlot` into `ebx`, `ecx`, `edi`, `ebp`,
one big-endian word each (through `eax`). -/
def load : List Instr :=
  [.mov .eax (.mem (at_ .esi dataSlot)),
   .mov .ebx (.mem (at_ .eax 0)), .bswap .ebx, .mov .ecx (.reg .ebx), .shift .shr .ebx 16,
   .alu .and .ecx (.imm 0xffff),
   .mov .edi (.mem (at_ .eax 4)), .bswap .edi, .mov .ebp (.reg .edi), .shift .shr .edi 16,
   .alu .and .ebp (.imm 0xffff)]

/-- The output transformation (subkeys 48–51), after the eighth round (`X₂`
in `ecx`, `X₃` in `edi`), with the middle words exchanged back: `edi` gets
`Y₂ = X₃ ⊞ Z₅₀`, `ecx` gets `Y₃ = X₂ ⊞ Z₅₁`. -/
def output : List Instr :=
  ([.mov .eax (.reg .ebx)] : List Instr) ++ mulKey 48 ++ ([.mov .ebx (.reg .edx)] : List Instr) ++
  ([.mov .eax (.reg .ebp)] : List Instr) ++ mulKey 51 ++ ([.mov .ebp (.reg .edx)] : List Instr) ++
  addKey .edi 49 ++ addKey .ecx 50

/-- `ebx, edi, ecx, ebp` (`Y₁ … Y₄`) to the block at `eax`, two words at a
time (`Y₁ · 2¹⁶ + Y₂`, byte-swapped). -/
def store : List Instr :=
  [.shift .ror .ebx 16, .alu .or .ebx (.reg .edi), .bswap .ebx, .store (at_ .eax 0) .ebx,
   .shift .ror .ecx 16, .alu .or .ecx (.reg .ebp), .bswap .ecx, .store (at_ .eax 4) .ecx]

/-- The block at the address in `dataSlot`, under the subkeys at `esi`, with
`pre` run just before the stores (whose address is in `eax`). -/
def cryptBlockWith (pre : List Instr) : List Instr :=
  load ++ (List.range 8).flatMap round ++ output ++ ([.mov .eax (.mem (at_ .esi dataSlot))] : List Instr) ++
    pre ++ store

def cryptBlock : List Instr := cryptBlockWith []

/-! ## ECB -/

/-- Subkey word `k` (two subkeys) from the schedule at `edx` to the copy at `esi`. -/
def copyWord (k : Nat) : List Instr := [.mov .eax (.mem (at_ .edx (4 * k))), .store (at_ .esi (4 * k)) .eax]

/-- Save the registers, copy the subkeys, and set up the slots; `n` in `eax`. -/
def prologue : List Instr :=
  [.mov .eax (.mem (argOp 3))] ++ saveAt .eax savedSlot ++
  [.mov .esi (.reg .eax), .mov .edx (.mem (argOp 0))] ++ (List.range 26).flatMap copyWord ++
  [.mov .eax (.mem (argOp 1)), .store (at_ .esi dataSlot) .eax,
   .mov .eax (.mem (argOp 2)), .store (at_ .esi leftSlot) .eax, .alu .cmp .eax (.imm 0)]

/-- One block, then the next block's address and the count back to their
slots (`edx` the blocks left before this one, read before the block's
stores). -/
def ecbBody : List Instr :=
  cryptBlockWith [.mov .edx (.mem (at_ .esi leftSlot))] ++
  [.alu .add .eax (.imm 8), .store (at_ .esi dataSlot) .eax, .alu .sub .edx (.imm 1),
   .store (at_ .esi leftSlot) .edx]

def ecb : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .e (.block []) (.loop (.block ecbBody) .ne))
      (.block (restoreAt .esi savedSlot)))

end VG.Impl.Idea.X86
