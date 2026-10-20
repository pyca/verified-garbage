module

public import VerifiedGarbage.Proof.Sm4.Bitsliced32
public import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86.Layers
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# The linear layers of bitsliced SM4 on x86 (32-bit), by evaluation

As on ARMv7 (`Proof/Sm4/Arm/Linear.lean`), with every word in slots: each
linear block is checked by evaluation over the lane domain, the kernel
running it on its input words as atoms and comparing every output slot
with the XOR of input bits given here. The slots a block must keep are
outputs too, each the input word it held.

* A round's input (`preX`): the state's planes (slots 32–63) are input
  words `0 … 31`, the round keys' planes at `kp` words `32 …`.
* A round's linear layer (`lin`): the S-box's output (slots 0–7) is input
  words `0 … 7`, the state's planes words `8 … 39`.
* The transposes (`toBs`, `fromBs`): the tail buffer's eight blocks
  (slots 64–95) or the state's planes are input words `0 … 31`.
* A round key's planes (`keyPlanes`): its word, byte-reversed, in slot 0 of
  the scratch buffer (an external word of the entry at `kp`), is input
  word `0`.

Position `p = 8 i + b` of a plane is byte `i` (from the most significant)
of the word of block `b`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Bitslice VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb)
open VG.Proof.Sm4 (W32.rotP)
open VG.Impl.Sm4 (Lin)

/-! ## A round -/

/-- The slots below the table; the round keys' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 32 }

/-- The state's planes, from input word `x`: plane `j` of word `w` is
input word `x + 8 w + j`. -/
def stateIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (32 + k, x + k)

/-- The state's planes kept, from input word `x`, but word `a`'s (none for
`a ≥ 4`). -/
def stateKeep (x a : Nat) : List (Nat × (Nat → List Nat)) :=
  ((List.range 32).filter (· / 8 != a)).map fun k => (32 + k, fun p => [32 * (x + k) + p])

/-- `preX e b c d`: plane `j` of `X_b ⊕ X_c ⊕ X_d ⊕ rk`, the round key at
entry `e` of `kp`. -/
def preG (e b c d j p : Nat) : List Nat :=
  [32 * (8 * b + j) + p, 32 * (8 * c + j) + p, 32 * (8 * d + j) + p, 32 * (32 + 8 * e + j) + p]

def preOuts (e b c d : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (j, preG e b c d j)) ++ stateKeep 0 4

theorem pre0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 0 1 2 3) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts 0 1 2 3)) = true := by
  decide +kernel

theorem pre1_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 1 2 3 0) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts 1 2 3 0)) = true := by
  decide +kernel

theorem pre2_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 2 3 0 1) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts 2 3 0 1)) = true := by
  decide +kernel

theorem pre3_check :
    check (lanes 32 11) layerCfg (linExt 32) (preX 3 0 1 2) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts 3 0 1 2)) = true := by
  decide +kernel

/-- The slots below the table, without the round keys. -/
def linCfg : Cfg := { base := sb, slots := tableSlot, ext := kp, exts := 0 }

/-- The S-box's output (slots `0 … 7`) and the state's planes. -/
def linIns : List (Nat × Nat) := (List.range 8).map (fun k => (k, k)) ++ stateIns 8

/-- Plane `j` of the state's word `a`, XOR the linear layer of the S-box's output. -/
def linG (l : Lin) (a j p : Nat) : List Nat :=
  (32 * (8 + 8 * a + j) + p) :: (l.terms j).map fun sm => 32 * sm.1 + W32.rotP p sm.2

def linOuts (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (stateSlot a j, linG l a j)) ++ stateKeep 8 a

/-- `linG` written out, without `List.map`, whose evaluation by the kernel
costs most of a check that evaluates `linG` at every bit of every output
(`linOuts_eq_flat`). -/
def linGFlat : Lin → Nat → Nat → Nat → List Nat
  | .enc, a, j, p =>
    if 2 ≤ j then
      [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0, 32 * j + W32.rotP p 3, 32 * (j - 2) + W32.rotP p 0,
        32 * (j - 2) + W32.rotP p 1, 32 * (j - 2) + W32.rotP p 2]
    else
      [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0, 32 * j + W32.rotP p 3, 32 * (j + 6) + W32.rotP p 1,
        32 * (j + 6) + W32.rotP p 2, 32 * (j + 6) + W32.rotP p 3]
  | .key, a, j, p =>
    [32 * (8 + 8 * a + j) + p, 32 * j + W32.rotP p 0,
      if 5 ≤ j then 32 * (j - 5) + W32.rotP p 1 else 32 * (j + 3) + W32.rotP p 2,
      if j = 7 then 32 * 0 + W32.rotP p 2 else 32 * (j + 1) + W32.rotP p 3]

theorem linG_eq_flat : linG = linGFlat := by
  funext l a j p
  cases l <;> simp only [linG, linGFlat, Lin.terms, Proof.Sm4.linTerms, Proof.Sm4.keyTerms]
  · split <;> simp
  · by_cases h5 : 5 ≤ j <;> by_cases h7 : j = 7 <;> simp [h5, h7]

def linOutsFlat (l : Lin) (a : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (stateSlot a j, linGFlat l a j)) ++ stateKeep 8 a

theorem linOuts_eq_flat : linOuts = linOutsFlat := by
  funext l a; simp only [linOuts, linOutsFlat, linG_eq_flat]

theorem linE0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 0) (linEnv linIns) (linPost tableSlot 11 (linOuts .enc 0)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 1) (linEnv linIns) (linPost tableSlot 11 (linOuts .enc 1)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 2) (linEnv linIns) (linPost tableSlot 11 (linOuts .enc 2)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linE3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .enc 3) (linEnv linIns) (linPost tableSlot 11 (linOuts .enc 3)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK0_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 0) (linEnv linIns) (linPost tableSlot 11 (linOuts .key 0)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK1_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 1) (linEnv linIns) (linPost tableSlot 11 (linOuts .key 1)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK2_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 2) (linEnv linIns) (linPost tableSlot 11 (linOuts .key 2)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

theorem linK3_check :
    check (lanes 32 11) linCfg (linExt 40) (lin .key 3) (linEnv linIns) (linPost tableSlot 11 (linOuts .key 3)) = true := by
  rw [linOuts_eq_flat]; decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := tableSlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (32 + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) bsCfg (linExt 0) toBs (linEnv tailIns) (linPost tableSlot 10 toBsOuts) = true := by
  lit_decide

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`3 - w` at `8 i + b`. -/
def fromBsG (t k : Nat) : List Nat := [32 * (8 * (3 - t % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map (fun t => (tailSlot + t, fromBsG t)) ++ stateKeep 0 4

theorem fromBs_check :
    check (lanes 32 10) bsCfg (linExt 0) fromBs (linEnv (stateIns 0)) (linPost tableSlot 10 fromBsOuts) = true := by
  lit_decide

/-! ## The round keys' planes -/

/-- The entry at `kp`; the round key's word in slot 0 of the scratch buffer. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := sb, exts := 1 }

/-- Plane `j` of a round key's: bit `8 i + b` is bit `8 i + j` of its word,
byte-reversed. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

theorem keyPlanes_check :
    check (lanes 32 5) entryCfg (linExt 0) keyPlanes (linEnv [])
      (linPost 8 5 ((List.range 8).map fun j => (j, keyBsG j))) = true := by
  decide +kernel

end VG.Proof.Sm4.X86
