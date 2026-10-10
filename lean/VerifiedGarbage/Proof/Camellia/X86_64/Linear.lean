import VerifiedGarbage.Impl.Camellia.X86_64.Layers
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.X86_64.LinearG

/-!
# The linear layers of bitsliced Camellia on x86-64, by evaluation

Each layer is checked by evaluation over the lane domain
(`Framework/X86_64/Linear.lean`): the kernel runs it on the input words as
atoms (the state registers are words 0–7, the subkey's planes at `kp`
words 8–23) and compares every output bit with the XOR of input bits given
here. The masks of the layers are constants in their slots
(`layerMasks`), which `linK_ok` takes as known.

Position `p = 8c + b` of a plane is byte `c` of block `b`, and byte `c`
holds the half's byte `pos c`.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1)
open VG.Proof.Camellia (toBsG fromBsG keyInG outPG)

/-- The slots below the table, the masks among them; the subkey's 16 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 16 }

/-- The state registers hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)


/-- The masks' slots. -/
def maskSlots : List Nat := layerMasks.map (·.1)

/-- The slots of both halves, input words 24–39 (after the subkey's). -/
def halvesIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 24 + j)

def keyInEnv : Env (Nat × Nat) := linEnvG qIns halvesIns layerMasks

theorem keyIn0_check :
    check (lanes 64 12) layerCfg (linExt 8) (keyXor 0 ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG 0)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true := by
  decide +kernel

theorem keyIn8_check :
    check (lanes 64 12) layerCfg (linExt 8) (keyXor 8 ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG 8)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true := by
  decide +kernel

/-- Both halves' planes, in slots 64–79, are input words 8–23. -/
def bothIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 8 + j)

/-- The Feistel XOR into the half at slot `d`: plane `j` of both the state
and that half is the XOR of the two. -/
def feistelG (d j p : Nat) : List Nat := [64 * j + p, 64 * (8 + (d - d1Slot) + j) + p]

def bothEnv : Env (Nat × Nat) := linEnvG qIns bothIns layerMasks

/-- The slots the Feistel XOR into the half at `d` keeps: the masks and the
other half. -/
def feistelKeep (d : Nat) : List Nat :=
  maskSlots ++ (List.range 8).map fun j => (if d = d1Slot then d2Slot else d1Slot) + j

theorem feistel1_check :
    check (lanes 64 12) layerCfg (linExt 24) (feistel d1Slot) bothEnv
      (linPostG 12 (qOuts (feistelG d1Slot)) ((List.range 8).map fun j => (d1Slot + j, feistelG d1Slot j))
        (feistelKeep d1Slot) bothEnv) = true := by
  decide +kernel

theorem feistel2_check :
    check (lanes 64 12) layerCfg (linExt 24) (feistel d2Slot) bothEnv
      (linPostG 12 (qOuts (feistelG d2Slot)) ((List.range 8).map fun j => (d2Slot + j, feistelG d2Slot j))
        (feistelKeep d2Slot) bothEnv) = true := by
  decide +kernel

theorem toBs_check :
    check (lanes 64 12) layerCfg (linExt 24) toBs bothEnv
      (linPostG 12 (qOuts toBsG) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem fromBs_check :
    check (lanes 64 12) layerCfg (linExt 24) fromBs bothEnv
      (linPostG 12 (qOuts fromBsG) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem outP_check :
    check (lanes 64 12) layerCfg (linExt 24) (outSel ++ pLayer) bothEnv
      (linPostG 12 (qOuts outPG) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
