import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
import VerifiedGarbage.Proof.Sm4.Bitsliced
import VerifiedGarbage.Proof.Camellia.AArch64.Linear

/-!
# The linear layers of bitsliced SM4 on AArch64, by evaluation

Each linear block is checked by evaluation over the lane domain
(`Framework/AArch64/Linear.lean`, through Camellia's `linG_ok`): the kernel
runs it on its input words as atoms and compares every output bit with the
XOR of input bits given here.

* A round's input (`preX`): the state's planes (slots 64–95) are input
  words `0 … 31`, the round keys' planes at `kp` words `32 …`.
* A round's linear layer (`lin`): the S-box's output in the state
  registers is input words `0 … 7`, the state's planes words `8 … 39`.
* The transposes (`toBs`, `fromBs`): the tail buffer's sixteen blocks
  (slots 96–127) are input words `0 … 31`; the state's planes are.
* A round key's planes (`keyLoad`): the schedule's word at `x0` is input
  word `0`.

Position `p = 16 i + b` of a plane is byte `i` (from the most significant)
of the word of block `b`.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1)
open VG.Proof.Camellia.AArch64 (linEnvG linPostG)
open VG.Proof.Sm4 (rotP)
open VG.Impl.Sm4 (Lin)

/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

def keyMaskSlots : List Nat := keyMasks.map (·.1)

/-! ## A round -/

/-- The slots below the table; the round keys' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 32 }

/-- The state's planes, from input word `x`: plane `j` of word `w` is
input word `x + 8 w + j`. -/
def stateIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (64 + k, x + k)

def stateSlots : List Nat := (List.range 32).map (64 + ·)

def preEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) keyMasks

/-- `preX e b c d`: plane `j` of `X_b ⊕ X_c ⊕ X_d ⊕ rk`, the round key at
entry `e` of `kp`. -/
def preG (e b c d j p : Nat) : List Nat :=
  [64 * (8 * b + j) + p, 64 * (8 * c + j) + p, 64 * (8 * d + j) + p, 64 * (32 + 8 * e + j) + p]

theorem pre0_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 0 1 2 3) preEnv
      (linPostG 12 (qOuts (preG 0 1 2 3)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre1_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 1 2 3 0) preEnv
      (linPostG 12 (qOuts (preG 1 2 3 0)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre2_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 2 3 0 1) preEnv
      (linPostG 12 (qOuts (preG 2 3 0 1)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

theorem pre3_check :
    check (lanes 64 12) layerCfg (linExt 32) (preX 3 0 1 2) preEnv
      (linPostG 12 (qOuts (preG 3 0 1 2)) [] (keyMaskSlots ++ stateSlots) preEnv) = true := by
  decide +kernel

/-- The slots below the table, without the round keys. -/
def linCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 0 }

def linEnv : Env (Nat × Nat) := linEnvG qIns (stateIns 8) keyMasks

/-- Plane `j` of the state's word `a`, XOR the linear layer of the S-box's output. -/
def linG (l : Lin) (a j p : Nat) : List Nat :=
  (64 * (8 + 8 * a + j) + p) :: (l.terms j).map fun sm => 64 * sm.1 + rotP p sm.2

/-- The state's planes but word `a`'s, and the masks. -/
def linKeep (a : Nat) : List Nat :=
  keyMaskSlots ++ ((List.range 32).filter (· / 8 != a)).map (64 + ·)

def linOuts (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (stateSlot a j, linG l a j)

theorem linE0_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 0) linEnv
      (linPostG 12 [] (linOuts .enc 0) (linKeep 0) linEnv) = true := by
  decide +kernel

theorem linE1_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 1) linEnv
      (linPostG 12 [] (linOuts .enc 1) (linKeep 1) linEnv) = true := by
  decide +kernel

theorem linE2_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 2) linEnv
      (linPostG 12 [] (linOuts .enc 2) (linKeep 2) linEnv) = true := by
  decide +kernel

theorem linE3_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .enc 3) linEnv
      (linPostG 12 [] (linOuts .enc 3) (linKeep 3) linEnv) = true := by
  decide +kernel

theorem linK0_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 0) linEnv
      (linPostG 12 [] (linOuts .key 0) (linKeep 0) linEnv) = true := by
  decide +kernel

theorem linK1_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 1) linEnv
      (linPostG 12 [] (linOuts .key 1) (linKeep 1) linEnv) = true := by
  decide +kernel

theorem linK2_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 2) linEnv
      (linPostG 12 [] (linOuts .key 2) (linKeep 2) linEnv) = true := by
  decide +kernel

theorem linK3_check :
    check (lanes 64 12) linCfg (linExt 40) (lin .key 3) linEnv
      (linPostG 12 [] (linOuts .key 3) (linKeep 3) linEnv) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := tableSlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

def toBsEnv : Env (Nat × Nat) := linEnvG [] tailIns keyMasks

/-- Plane `j` of the state's word `w`, at `p = 16 i + b`: bit `j` of byte
`4 (w mod 2) + i` of the tail buffer's word `2 b + ⌊w / 2⌋`. -/
def toBsG (w j p : Nat) : List Nat := [64 * (2 * (p % 16) + w / 2) + 8 * (4 * (w % 2) + p / 16) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (64 + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 64 11) bsCfg (linExt 0) toBs toBsEnv
      (linPostG 11 [] toBsOuts keyMaskSlots toBsEnv) = true := by
  decide +kernel

def fromBsEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) keyMasks

/-- Bit `8 β + j` of the tail buffer's word `t = 2 b + h`, byte `8 h + β`
of block `b`, word `w' = 2 h + ⌊β / 4⌋`: plane `j` of the state's word
`3 - w'` at byte `β mod 4`. -/
def fromBsG (t k : Nat) : List Nat :=
  [64 * (8 * (3 - (2 * (t % 2) + k / 32)) + k % 8) + 16 * (k / 8 % 4) + t / 2]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 64 11) bsCfg (linExt 0) fromBs fromBsEnv
      (linPostG 11 [] fromBsOuts (keyMaskSlots ++ stateSlots) fromBsEnv) = true := by
  decide +kernel

/-! ## The round keys' planes -/

/-- The masks' slots; the schedule's word at `x0`. -/
def keyCfg : Cfg := { base := sb, slots := 64, ext := .x0, exts := 1 }

def keyEnv : Env (Nat × Nat) := linEnvG [] [] keyMasks

/-- Plane `j` of round key `2 m + h`: bit `16 i + b` is bit `j` of its byte
`i` from the most significant, bits `32 h + 8 (3 - i) + j` of the word. -/
def keyBsG (h j p : Nat) : List Nat := [32 * h + 8 * (3 - p / 16) + j]

theorem keyLoad0_check :
    check (lanes 64 7) keyCfg (linExt 0) (keyLoad 0) keyEnv
      (linPostG 7 (qOuts (keyBsG 0)) [] keyMaskSlots keyEnv) = true := by
  decide +kernel

theorem keyLoad1_check :
    check (lanes 64 7) keyCfg (linExt 0) (keyLoad 1) keyEnv
      (linPostG 7 (qOuts (keyBsG 1)) [] keyMaskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Sm4.AArch64
