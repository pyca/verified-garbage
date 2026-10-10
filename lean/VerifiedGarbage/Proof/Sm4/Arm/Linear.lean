import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
import VerifiedGarbage.Proof.Sm4.Bitsliced32
import VerifiedGarbage.Proof.Sm4.Arm.LinG

/-!
# The linear layers of bitsliced SM4 on ARMv7, by evaluation

As on x86-64 (`Proof/Sm4/X86_64/Linear.lean`), on 32-bit words: each
linear block is checked by evaluation over the lane domain, the kernel
running it on its input words as atoms and comparing every output bit
with the XOR of input bits given here.

* A round's input (`preX`): the state's planes (slots 32–63) are input
  words `0 … 31`, the round keys' planes at `kp` words `32 …`.
* A round's linear layer (`lin`): the S-box's output in the state
  registers is input words `0 … 7`, the state's planes words `8 … 39`.
* The transposes (`toBs`, `fromBs`): the tail buffer's eight blocks
  (slots 64–95) are input words `0 … 31`; the state's planes are.
* A round key's planes (`keyPlanes`): its word, byte-reversed, in `q 0` is
  input word `0`; the planes are the entry at `kp`.

Position `p = 8 i + b` of a plane is byte `i` (from the most significant)
of the word of block `b`.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Bitslice VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Arm.Straight (inWord outWord bitOf xorBits assign)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp)
open VG.Proof.Sm4 (W32.rotP)
open VG.Impl.Sm4 (Lin)

/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-! ## A round -/

/-- The slots below the table; the round keys' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 32 }

/-- The state's planes, from input word `x`: plane `j` of word `w` is
input word `x + 8 w + j`. -/
def stateIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (32 + k, x + k)

def stateSlots : List Nat := (List.range 32).map (32 + ·)

def preEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) []

/-- `preX e b c d`: plane `j` of `X_b ⊕ X_c ⊕ X_d ⊕ rk`, the round key at
entry `e` of `kp`. -/
def preG (e b c d j p : Nat) : List Nat :=
  [32 * (8 * b + j) + p, 32 * (8 * c + j) + p, 32 * (8 * d + j) + p, 32 * (32 + 8 * e + j) + p]

theorem pre0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 0 1 2 3) preEnv
      (linPostG 11 (qOuts (preG 0 1 2 3)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre1_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 1 2 3 0) preEnv
      (linPostG 11 (qOuts (preG 1 2 3 0)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre2_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 2 3 0 1) preEnv
      (linPostG 11 (qOuts (preG 2 3 0 1)) [] stateSlots preEnv) = true := by
  decide +kernel

theorem pre3_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 3 0 1 2) preEnv
      (linPostG 11 (qOuts (preG 3 0 1 2)) [] stateSlots preEnv) = true := by
  decide +kernel

/-- The slots below the table, without the round keys. -/
def linCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 0 }

def linEnv : Env (Nat × Nat) := linEnvG qIns (stateIns 8) []

/-- Plane `j` of the state's word `a`, XOR the linear layer of the S-box's output. -/
def linG (l : Lin) (a j p : Nat) : List Nat :=
  (32 * (8 + 8 * a + j) + p) :: (l.terms j).map fun sm => 32 * sm.1 + W32.rotP p sm.2

/-- The state's planes but word `a`'s. -/
def linKeep (a : Nat) : List Nat := ((List.range 32).filter (· / 8 != a)).map (32 + ·)

def linOuts (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (stateSlot a j, linG l a j)

theorem linE0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 0) linEnv
      (linPostG 11 [] (linOuts .enc 0) (linKeep 0) linEnv) = true := by
  decide +kernel

theorem linE1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 1) linEnv
      (linPostG 11 [] (linOuts .enc 1) (linKeep 1) linEnv) = true := by
  decide +kernel

theorem linE2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 2) linEnv
      (linPostG 11 [] (linOuts .enc 2) (linKeep 2) linEnv) = true := by
  decide +kernel

theorem linE3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 3) linEnv
      (linPostG 11 [] (linOuts .enc 3) (linKeep 3) linEnv) = true := by
  decide +kernel

theorem linK0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 0) linEnv
      (linPostG 11 [] (linOuts .key 0) (linKeep 0) linEnv) = true := by
  decide +kernel

theorem linK1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 1) linEnv
      (linPostG 11 [] (linOuts .key 1) (linKeep 1) linEnv) = true := by
  decide +kernel

theorem linK2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 2) linEnv
      (linPostG 11 [] (linOuts .key 2) (linKeep 2) linEnv) = true := by
  decide +kernel

theorem linK3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 3) linEnv
      (linPostG 11 [] (linOuts .key 3) (linKeep 3) linEnv) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := tableSlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

def toBsEnv : Env (Nat × Nat) := linEnvG [] tailIns []

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (32 + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) bsCfg (linExt 0) toBs toBsEnv (linPostG 10 [] toBsOuts [] toBsEnv) = true := by
  decide +kernel

def fromBsEnv : Env (Nat × Nat) := linEnvG [] (stateIns 0) []

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`3 - w` at `8 i + b`. -/
def fromBsG (t k : Nat) : List Nat := [32 * (8 * (3 - t % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 10) bsCfg (linExt 0) fromBs fromBsEnv
      (linPostG 10 [] fromBsOuts stateSlots fromBsEnv) = true := by
  decide +kernel

/-! ## The round keys' planes -/

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def keyEnv : Env (Nat × Nat) := linEnvG [(q 0, 0)] [] []

/-- Plane `j` of a round key's: bit `8 i + b` is bit `8 i + j` of its word,
byte-reversed, in `q 0`. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

theorem keyPlanes_check :
    check (lanes 32 5) entryCfg (linExt 0) keyPlanes keyEnv
      (linPostG 5 [] ((List.range 8).map fun j => (j, keyBsG j)) [] keyEnv) = true := by
  decide +kernel

end VG.Proof.Sm4.Arm
