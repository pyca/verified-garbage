import VerifiedGarbage.Impl.Seed.X86.Ecb

/-!
# SEED key expansion on x86 (32-bit)

`expandKey(key, schedule, scratch)`, cdecl: `vg_seed_expand_key` with its
working space in the scratch buffer (laid out as ECB's, `Ecb.lean`), which
the artifact allocates on the stack.

As on ARMv7 (`Impl/Seed/Arm/ExpandKey.lean`): all 32 inputs of `G` are
computed first (`keyRound`), into the slots `uSlot i`, and then `G` of eight
at a time is computed by `g8` and stored to the schedule (`keyChunk`), whose
pointer is kept in `esi`, which `g8` does not write.

`Key0`, …, `Key3` are kept in the slots `keySlot w`. The rotation by eight
bits of `Key0 || Key1` (odd rounds) is, with `a` and `b` its words rotated
right by eight bits and `m = 0xFF000000`, `a ⊕ ((a ⊕ b) & m)` and
`b ⊕ ((a ⊕ b) & m)`; that of `Key2 || Key3` left (even rounds) the same with
rotations by 24 bits and `m = 0x000000FF`. Nothing depends on the key but
the data: the code is straight-line.
-/

namespace VG.Impl.Seed.X86

open VG.X86 VG.Impl.Aes.X86

/-- `G`'s input `i` (`i < 32`). -/
def uSlot (i : Nat) : Nat := aSlot + i

/-- The key's word `w`. -/
def keySlot (w : Nat) : Nat := tailSlot + w

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

/-- `G` of the inputs `8c … 8c + 7`, stored to the schedule's words from `8c`
(the schedule at `esi`). -/
def keyChunk (c : Nat) : List Instr :=
  (List.range 8).flatMap (fun w => [movS .eax (uSlot (8 * c + w)), st (tSlot w) .eax]) ++ g8 ++
    (List.range 8).flatMap fun w => [movS .eax (tSlot w), .store (at_ .esi (4 * (8 * c + w))) .eax]

def expandKey : Prog isa :=
  .block (saveRegs 2 ++ keyLoad ++ [.mov .esi (.mem (argOp 1))] ++ (List.range 16).flatMap keyRound ++
    (List.range 4).flatMap keyChunk ++ restoreRegs)

end VG.Impl.Seed.X86
