module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyChecks
public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey

/-!
# The key schedule's evaluated facts on PPC64LE

`spread d`, which bitslices the word at `[r3 + d]` into all eight lanes as
`toBs` bitslices eight words, keeping the masks and both halves' slots
(`spread0_check`, `spread8_check`), and `sigmaStores x`, which stores the
planes of a constant `x` to the entry at `kp` (`sigma_check`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR imm64)
open VG.Proof.Camellia (HalfRel pos)

/-- The halves' slots are input words 2–17, after the running value's two at `r3`. -/
def kaIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 2 + j)

def kaEnv : Env (Nat × Nat) := linEnvG [] kaIns layerMasks

/-- `spread d`: the running value's word at `[r3 + d]` in all lanes,
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
  (List.range 8).flatMap fun j => imm64 t0 (keyPlane x j) ++ [.store .d t0 kp (8 * j)]

theorem sigmaOne_eq (x : BitVec 64) : sigmaOne x = sigmaStores x ++ ([.addi kp kp 64] : List Instr) := rfl

/-- The entry at `kp`, as slots. -/
def sigCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def sigPost (x : BitVec 64) (e : Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((keyPlane x j).toNat, 0)

theorem sigma_checks :
    (sigmas.all fun x => check (lanes 64 1) sigCfg (fun _ => none) (sigmaStores x) (linEnvG [] [] [])
      (sigPost x)) = true := by
  decide +kernel

end VG.Proof.Camellia.PPC64LE
