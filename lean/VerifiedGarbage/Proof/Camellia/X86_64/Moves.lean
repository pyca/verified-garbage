import VerifiedGarbage.Proof.Camellia.X86_64.Linear
import VerifiedGarbage.Impl.Camellia.X86_64.Ecb

/-!
# Moving the blocks and halves of bitsliced Camellia on x86-64, by evaluation

The loads and stores of the blocks (`loadWords`, `storeWords`, with the
blocks' 16 words as the slots of `rdx`), of the halves (`loadHalf`,
`storeHalf`), and the subkey XORs outside the rounds (the whitening in
`head` and `tail`), checked over the lane domain as the layers are
(`Linear.lean`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1)

/-! ## The blocks -/

/-- The eight blocks' 16 words at `rdx`, as slots. -/
def dataCfg : Cfg := { base := .rdx, slots := 16, ext := .rdx, exts := 0 }

/-- The blocks' 16 words are input words `0 … 15`. -/
def dataIns : List (Nat × Nat) := (List.range 16).map fun k => (k, k)

def dataEnv : Env (Nat × Nat) := linEnvG [] dataIns []

/-- `loadWords h`: `q b` is word `2 b + h` of the blocks. -/
def loadG (h b p : Nat) : List Nat := [64 * (2 * b + h) + p]

/-- Each state register `q b` holds input word `b`. -/
def idG (b p : Nat) : List Nat := [64 * b + p]

theorem loadWords0_check :
    check (lanes 64 10) dataCfg (linExt 0) (loadWords 0) dataEnv
      (linPostG 10 (qOuts (loadG 0)) [] (dataIns.map (·.1)) dataEnv) = true := by
  decide +kernel

theorem loadWords1_check :
    check (lanes 64 10) dataCfg (linExt 0) (loadWords 1) dataEnv
      (linPostG 10 (qOuts (loadG 1)) [] (dataIns.map (·.1)) dataEnv) = true := by
  decide +kernel

/-- `storeWords h`: word `2 b + h` of the blocks is `q b`. -/
def storeOuts (h : Nat) : List (Nat × (Nat → List Nat)) := (List.range 8).map fun b => (2 * b + h, idG b)

/-- The blocks' words are input words `8 … 23`, after the state's. -/
def storeIns : List (Nat × Nat) := (List.range 16).map fun k => (k, 8 + k)

def storeEnv : Env (Nat × Nat) := linEnvG qIns storeIns []

/-- The other half's words. -/
def otherWords (h : Nat) : List Nat := (List.range 8).map fun b => 2 * b + (1 - h)

theorem storeWords0_check :
    check (lanes 64 11) dataCfg (linExt 0) (storeWords 0) storeEnv
      (linPostG 11 [] (storeOuts 0) (otherWords 0) storeEnv) = true := by
  decide +kernel

theorem storeWords1_check :
    check (lanes 64 11) dataCfg (linExt 0) (storeWords 1) storeEnv
      (linPostG 11 [] (storeOuts 1) (otherWords 1) storeEnv) = true := by
  decide +kernel

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

end VG.Proof.Camellia.X86_64
