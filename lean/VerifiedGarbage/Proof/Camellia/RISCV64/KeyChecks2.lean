module

import VerifiedGarbage.Proof.Camellia.RISCV64.KeyChecks
public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear

/-!
# The key schedule's evaluated facts on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyChecks2.lean`): `spread d`, which
bitslices the word at `[a0 + d]` into all eight lanes as `toBs` bitslices
eight words, keeping the masks and both halves' slots (`spread0_check`,
`spread8_check`). The constants' planes (`sigmaOne`) are stored by
`sigmaOne_ok` (`Proof/Camellia/RISCV64/KeySetup.lean`), as the lane domain
does not follow `movImm64`.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp movR)
open VG.Proof.Camellia (HalfRel pos)

/-- The masks' slots below the saved registers; the running value's two words at `a0`. -/
def kaCfg : Cfg := { base := sb, slots := savedSlot, ext := .a0, exts := 2 }

/-- The halves' slots are input words 2–17, after the running value's two at `a0`. -/
def kaIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 2 + j)

def kaEnv : Env (Nat × Nat) := linEnvG [] kaIns allMasks

/-- Plane `j` of word `d / 8` at `a0`: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def spreadBsG (d j p : Nat) : List Nat := [64 * (d / 8) + 8 * pos (p / 8) + j]

/-- `spread d`: the running value's word at `[a0 + d]` in all lanes,
keeping the masks and both halves' slots. -/
theorem spread0_check :
    check (lanes 64 11) kaCfg (linExt 0) (spread 0) kaEnv
      (linPostG 11 (qOuts (spreadBsG 0)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

theorem spread8_check :
    check (lanes 64 11) kaCfg (linExt 0) (spread 8) kaEnv
      (linPostG 11 (qOuts (spreadBsG 8)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.RISCV64
