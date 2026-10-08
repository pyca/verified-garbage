import VerifiedGarbage.Proof.Camellia.AArch64.KeyChecks
import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey

/-!
# The key schedule's evaluated facts on AArch64

`spread d`, which bitslices the word at `[x0 + d]` into all eight lanes as
`toBs` bitslices eight words, keeping the masks and both halves' slots
(`spread0_check`, `spread8_check`), and `sigmaStores x`, which stores the
planes of a constant `x` to the entry at `kp` (`sigma_check`).
-/

namespace VG.Proof.Camellia.AArch64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR imm)
open VG.Proof.Camellia (HalfRel pos)

/-- The halves' slots are input words 2–17, after the running value's two at `x0`. -/
def kaIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 2 + j)

def kaEnv : Env (Nat × Nat) := linEnvG [] kaIns layerMasks

/-- `spread d`: the running value's word at `[x0 + d]` in all lanes,
keeping the masks and both halves' slots. -/
theorem spread0_check :
    check (lanes 64 11) (keyCfg 2) (linExt 0) (spread 0) kaEnv
      (linPostG 11 (qOuts (keyBsG 0)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

theorem spread8_check :
    check (lanes 64 11) (keyCfg 2) (linExt 0) (spread 8) kaEnv
      (linPostG 11 (qOuts (keyBsG 8)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

/-- The stores of `sigmaOne x`, before `kp` steps on. -/
def sigmaStores (x : BitVec 64) : List Instr :=
  (List.range 8).flatMap fun j => imm t0 (keyPlane x j) ++ [.str .x t0 kp (8 * j)]

theorem sigmaOne_eq (x : BitVec 64) : sigmaOne x = sigmaStores x ++ ([.addImm .x kp kp 64] : List Instr) := rfl

/-- The entry at `kp`, as slots. -/
def sigCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def sigPost (x : BitVec 64) (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((keyPlane x j).toNat, 0)

theorem sigma_checks :
    (sigmas.all fun x => check (lanes 64 1) sigCfg (fun _ => none) (sigmaStores x) (linEnvG [] [] [])
      (sigPost x)) = true := by
  decide +kernel

end VG.Proof.Camellia.AArch64
