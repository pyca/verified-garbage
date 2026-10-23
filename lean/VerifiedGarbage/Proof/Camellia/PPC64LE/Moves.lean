module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Linear
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
import Mathlib.Tactic.SplitIfs

/-!
# Moving the halves of bitsliced Camellia on PPC64LE, by evaluation

As on x86-64: the loads and stores of the halves (`loadHalf`,
`storeHalf`), and the subkey XORs outside the rounds (the whitening in
`head` and `tail`), checked over the lane domain as the layers are
(`Linear.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp)

/-- Each state register `q b` holds input word `b`. -/
def idG (b p : Nat) : List Nat := [64 * b + p]

/-! ## The halves -/

/-- `loadHalf d`: `q j` is the half's plane `j`, input word `8 + (d - d1Slot) + j`. -/
def loadHalfG (d j p : Nat) : List Nat := [64 * (8 + (d - d1Slot) + j) + p]

theorem loadHalf1_check :
    check (lanes 64 12) layerCfg (linExt 24) (loadHalf d1Slot) bothEnv
      (linPostG 12 (qOuts (loadHalfG d1Slot)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem loadHalf2_check :
    check (lanes 64 12) layerCfg (linExt 24) (loadHalf d2Slot) bothEnv
      (linPostG 12 (qOuts (loadHalfG d2Slot)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

/-- `storeHalf d`: the half's plane `j` is `q j`. -/
def storeHalfOuts (d : Nat) : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (d + j, idG j)

theorem storeHalf1_check :
    check (lanes 64 12) layerCfg (linExt 24) (storeHalf d1Slot) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d1Slot) (feistelKeep d1Slot) bothEnv) = true := by
  decide +kernel

theorem storeHalf2_check :
    check (lanes 64 12) layerCfg (linExt 24) (storeHalf d2Slot) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d2Slot) (feistelKeep d2Slot) bothEnv) = true := by
  decide +kernel

/-! ## The whitening -/

/-- `keyXor off`: `q j` XOR the subkey's plane `j`, at word `off + j` of `kp`
(input word `24 + off + j`). -/
def keyXorG (off j p : Nat) : List Nat := [64 * j + p, 64 * (24 + off + j) + p]

theorem keyXor8_check :
    check (lanes 64 12) layerCfg (linExt 24) (keyXor 8) bothEnv
      (linPostG 12 (qOuts (keyXorG 8)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem keyXor0_check :
    check (lanes 64 12) layerCfg (linExt 24) (keyXor 0) bothEnv
      (linPostG 12 (qOuts (keyXorG 0)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

/-- `D2`'s plane `j` XOR the second subkey's. -/
def whiten2G (j p : Nat) : List Nat := [64 * (16 + j) + p, 64 * (32 + j) + p]

theorem whiten_check :
    check (lanes 64 12) layerCfg (linExt 24) whiten bothEnv
      (linPostG 12 (qOuts (keyXorG 0))
        ((List.range 8).map (fun j => (d1Slot + j, keyXorG 0 j)) ++
          (List.range 8).map (fun j => (d2Slot + j, whiten2G j))) maskSlots bothEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.PPC64LE
