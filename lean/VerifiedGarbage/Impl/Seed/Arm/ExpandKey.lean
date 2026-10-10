import VerifiedGarbage.Impl.Seed.Arm.Ecb

/-!
# SEED key expansion on ARMv7

`expandKey(key = r0, schedule = r1, scratch = r2)`: `vg_seed_expand_key`
with its working space in the scratch buffer (laid out as ECB's,
`Ecb.lean`), which the artifact allocates on the stack.

As on AArch64 (`Impl/Seed/AArch64/ExpandKey.lean`): RFC 4269 §2.3's round
keys `Ki0 = G(Key0 + Key2 - KCi)` and `Ki1 = G(Key1 - Key3 + KCi)`: the
inputs of `G` do not depend on its outputs, so all 32 are computed first
(`keyRound`), into the slots `uSlot i`, and then `G` of eight at a time is
computed by `g8` and stored to the schedule, whose words are in the same
order (`keyChunk`).

`Key0`, …, `Key3` are kept in `r4`–`r7`; the rotations by eight bits of
`Key0 || Key1` (odd rounds) and `Key2 || Key3` (even rounds) are two shifts
of each word, ORed. The schedule's pointer is kept in `r9`, which `g8` does
not write. Nothing depends on the key but the data: the code is
straight-line.
-/

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Aes.Arm

/-- `G`'s input `i` (`i < 32`). -/
def uSlot (i : Nat) : Nat := aSlot + i

def subR (d n m : Reg) : Instr := .dp .sub d n (.reg m)
def lslOp (r : Reg) (n : Nat) : Op2 := .shifted r .lsl n

/-- `(d, e) := (d, e)` rotated right by eight bits, as one 64-bit word `d || e`. -/
def rotr8 (d e : Reg) : List Instr :=
  [.mov t0 (lsrOp d 8), .dp .orr t0 t0 (lslOp e 24), .mov t1 (lsrOp e 8), .dp .orr e t1 (lslOp d 24), movR d t0]

/-- `(d, e) := (d, e)` rotated left by eight bits, as one 64-bit word `d || e`. -/
def rotl8 (d e : Reg) : List Instr :=
  [.mov t0 (lslOp d 8), .dp .orr t0 t0 (lsrOp e 24), .mov t1 (lslOp e 8), .dp .orr e t1 (lsrOp d 24), movR d t0]

/-- Round `j + 1`'s two inputs of `G` (`KCj+1` built in `t1`), then the
rotation of `Key0 || Key1` (odd rounds) or `Key2 || Key3` (even). -/
def keyRound (j : Nat) : List Instr :=
  [addR t0 .r4 .r6] ++ imm32 t1 (Spec.Seed.kc.getD j 0) ++
  [subR t0 t0 t1, stS (uSlot (2 * j)) t0, subR t0 .r5 .r7, addR t0 t0 t1, stS (uSlot (2 * j + 1)) t0] ++
  (if j % 2 = 0 then rotr8 .r4 .r5 else rotl8 .r6 .r7)

/-- The key's big-endian words into `r4`–`r7`. -/
def keyLoad : List Instr :=
  (List.range 4).flatMap fun w => [.ldr (q (4 + w)) .r0 (4 * w), .rev (q (4 + w)) (q (4 + w))]

/-- `G` of the inputs `8c … 8c + 7`, stored to the schedule's words from `8c`
(the schedule at `kp`). -/
def keyChunk (c : Nat) : List Instr :=
  (List.range 8).flatMap (fun w => [ldS t0 (uSlot (8 * c + w)), stS (tSlot w) t0]) ++ g8 ++
    (List.range 8).flatMap fun w => [ldS t0 (tSlot w), .str t0 kp (4 * (8 * c + w))]

def expandKey : Prog isa :=
  .block (saveRegs .r2 ++ [movR sb .r2, movR kp .r1] ++ keyLoad ++ (List.range 16).flatMap keyRound ++
    (List.range 4).flatMap keyChunk ++ [movR .r12 sb] ++ restoreRegs .r12)

end VG.Impl.Seed.Arm
