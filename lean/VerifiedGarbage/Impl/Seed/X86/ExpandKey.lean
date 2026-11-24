module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32
public import VerifiedGarbage.Impl.Seed.X86.Sse
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# SEED key expansion on x86 (32-bit)

`expandKey(key, schedule, scratch)`, cdecl: `vg_seed_expand_key` with its
working space in the scratch buffer, which the artifact allocates on the
stack.

All 32 inputs of `G` are computed first (`keyRound`), in general-purpose
registers, into the slots `uSlot i`; then `G` of sixteen of them at a time
(`keyChunk`), in XMM registers (`Sse.g`, whose slots of 16 bytes are the
buffer's first 36), is written to the schedule.

`Key0`, …, `Key3` are kept in the slots `keySlot w`. The rotation by eight
bits of `Key0 || Key1` (odd rounds) is, with `a` and `b` its words rotated
right by eight bits and `m = 0xFF000000`, `a ⊕ ((a ⊕ b) & m)` and
`b ⊕ ((a ⊕ b) & m)`; that of `Key2 || Key3` left (even rounds) the same with
rotations by 24 bits and `m = 0x000000FF`. Nothing depends on the key but
the data.
-/

@[expose] public section

namespace VG.Impl.Seed.X86

open VG.X86 VG.Impl.Aes.X86

/-! ## The slots, of 4 bytes, after the 36 of 16 bytes that `G` uses -/

/-- `G`'s input `i` (`i < 32`). -/
def uSlot (i : Nat) : Nat := 144 + i

/-- The key's word `w`. -/
def keySlot (w : Nat) : Nat := 176 + w

/-- The caller's registers. -/
def savedSlot : Nat := 180

/-- The number of slots. -/
def kSlots : Nat := 184

/-- The callee-saved registers, and their slots. -/
def savedRegs : List (Reg × Nat) :=
  [(.ebx, savedSlot), (.esi, savedSlot + 1), (.edi, savedSlot + 2), (.ebp, savedSlot + 3)]

/-- Load the scratch buffer's address (argument `k`) to `edi`, saving the
registers there first. -/
def saveRegs (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp k))] ++ savedRegs.map (fun (r, j) => .store (slotAt .eax j) r) ++ [movR .edi .eax]

/-- Restore the registers (`edi`, the base, last). -/
def restoreRegs : List Instr :=
  [movS .ebx savedSlot, movS .esi (savedSlot + 1), movS .ebp (savedSlot + 3), movS .edi (savedSlot + 2)]

def addS (d : Reg) (k : Nat) : Instr := .alu .add d (.mem (slotAt sb k))
def subS (d : Reg) (k : Nat) : Instr := .alu .sub d (.mem (slotAt sb k))

/-! ## The inputs of `G` -/

/-- The 64-bit word `keySlot k || keySlot (k + 1)` rotated: each word rotated
right by `n`, and the bits `m` exchanged. -/
def rot64 (k n : Nat) (m : BitVec 32) : List Instr :=
  [movS .eax (keySlot k), rorI .eax n, movS .ebx (keySlot (k + 1)), rorI .ebx n, movR .ecx .eax,
   xorR .ecx .ebx, andI .ecx m, xorR .eax .ecx, xorR .ebx .ecx, st (keySlot k) .eax, st (keySlot (k + 1)) .ebx]

/-- Round `j + 1`'s two inputs of `G`, then the rotation of `Key0 || Key1`
(odd rounds) or `Key2 || Key3` (even). -/
def keyRound (j : Nat) : List Instr :=
  [movS .eax (keySlot 0), addS .eax (keySlot 2), subI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j)) .eax,
   movS .eax (keySlot 1), subS .eax (keySlot 3), addI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j + 1)) .eax] ++
  (if j % 2 = 0 then rot64 0 8 0xFF000000 else rot64 2 24 0x000000FF)

/-- The key's big-endian words (argument 0, through `ecx`) to their slots. -/
def keyLoad : List Instr :=
  .mov .ecx (.mem (argOp 0)) ::
    (List.range 4).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .bswap .eax, st (keySlot w) .eax]

/-! ## `G` -/

/-- Inputs `16 h` to `16 h + 15` to `G`'s words. -/
def copyIn (h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [Sse.ldS .xmm0 (36 + 4 * h + k), Sse.stS (Sse.gS + k) .xmm0]

/-- `G`'s words to words `16 h` to `16 h + 15` of the schedule, at `esi`. -/
def copyOut (h : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [Sse.ldS .xmm0 (Sse.gS + k), Sse.stx .esi (16 * (4 * h + k)) .xmm0]

/-- `G` of sixteen inputs, to the schedule. -/
def keyChunk (h : Nat) : Prog isa := .seq (.block (copyIn h)) (.seq Sse.gCall (.block (copyOut h)))

/-- The table's address (from `eax`) to the register `G` has it in. -/
def keyTable : List Instr := [Sse.ownTable, .mov Sse.tbr (.reg .eax)]

def expandKey : Prog isa :=
  .seq (.block (saveRegs 2 ++ keyLoad ++ [.mov .esi (.mem (argOp 1))] ++ (List.range 16).flatMap keyRound))
    (.seq (.frame (.symPush .eax Sse.tableName) (.block []) (.pop .ecx 1))
      (.seq (.block keyTable) (.seq (keyChunk 0) (.seq (keyChunk 1) (.block restoreRegs)))))

/-! ## The function as emitted -/

namespace Fn

/-- The doublewords of the 768 bytes of stack below `esp` that the residue
analysis finds the function may leave different in two runs: where it calls
`G`, the header of its working space's frame, and the frame's last
doublewords, which nothing writes. -/
def expandKeyWords : List Nat := [0, 1, 2, 3, 4, 189, 190, 191]

/-- `vg_seed_expand_key`, as emitted. Its frame is larger than its working
space and header need, so that the working space is at a multiple of 16 when
`esp` is one at the call. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 768 expandKeyWords
    (Impl.StackScratch.X86.withStackScratchWiped 764 2 184 Impl.Seed.X86.expandKey)

end Fn

end VG.Impl.Seed.X86
