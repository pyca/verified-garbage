module

public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
public import VerifiedGarbage.Proof.Framework.X86.Linear
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# The linear layers of bitsliced Camellia on x86 (32-bit), by evaluation

As on ARMv7 (`Proof/Camellia/Arm/Linear.lean`), with every word in slots
(`Framework/X86/Linear.lean`): the kernel runs each linear block on its
input words as atoms and compares every output slot with the XOR of input
bits given here, bit `t` of input word `i` being `32 i + t`. The slots a
block must keep are outputs too, each the input word it held.

* A round's left word (`preL`): the halves' planes (slots 40–71) are input
  words `0 … 31`, the subkeys' planes at `kp` words `32 …`.
* The middle (`midLR`): the left word's S-box output (slots 0–7) is words
  `0 … 7`, the halves' planes `8 … 39`, the subkeys' planes at `kp` words
  `40 …`.
* The end (`postP`): the right word's S-box output (slots 0–7) is words
  `0 … 7`, the left word's selected output (slots 32–39) words `8 … 15`,
  the halves' planes words `16 … 47`.
* The whitening: the halves' planes are words `0 … 31`, the two entries
  at `kp` words `32 … 63`.
* The transposes (`toBsWord`, `fromBsWord`): the tail buffer's eight
  blocks (slots 72–103), or the halves' planes, are words `0 … 31`.
* A subkey's planes (`keyPlane`): its word, in slot 0 of the scratch
  buffer (an external word of the entry at `kp`), is input word `0`.

Position `p = 8 i + b` of a plane of word `w` is byte `4 w + i` of the half
of block `b`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Bitslice VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb)
open VG.Proof.Camellia (pRow)

/-! ## A round -/

/-- The slots below the tail buffer; the two entries' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := tailSlot, ext := kp, exts := 32 }

/-- The slots below the tail buffer, without the subkeys. -/
def linCfg : Cfg := { base := sb, slots := tailSlot, ext := kp, exts := 0 }

/-- Both halves (slots 40–71), from input word `x`. -/
def halvesIns (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (d1Slot + k, x + k)

/-- Slot `j` keeps its input word `x`. -/
def keepOut (j x : Nat) : Nat × (Nat → List Nat) := (j, fun p => [32 * x + p])

/-- The halves kept, from input word `x`. -/
def halvesKeep (x : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => keepOut (d1Slot + k) (x + k)

/-- The left word's S-box input: plane `j` at `p` is the selected plane of
the source half (at slot `src`) XOR the subkey's, at word `off` of `kp`. -/
def preG (off src j p : Nat) : List Nat :=
  [32 * (src - d1Slot + W32.inSrc (p / 8) j) + p, 32 * (32 + off + W32.inSrc (p / 8) j) + p]

def preOuts (off src : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (j, preG off src j)) ++ halvesKeep 0

theorem preL0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 0 d1Slot) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts 0 d1Slot)) = true := by
  decide +kernel

theorem preL16_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 16 d2Slot) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts 16 d2Slot)) = true := by
  decide +kernel

/-- The S-box's output (slots `0 … 7`), then the halves. -/
def midIns : List (Nat × Nat) := (List.range 8).map (fun k => (k, k)) ++ halvesIns 8

/-- The left word's selected output, to slot `32 + j`. -/
def ylG (j p : Nat) : List Nat := [32 * W32.outSrc (p / 8) j + p]

/-- The right word's S-box input. -/
def midG (off src j p : Nat) : List Nat :=
  [32 * (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j) + p,
   32 * (48 + off + W32.inSrc (4 + p / 8) j) + p]

def midOuts (off src : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (j, midG off src j)) ++
    (List.range 8).map (fun j => (ylSlot + j, ylG j)) ++ halvesKeep 8

theorem mid0_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 0 d1Slot) (linEnv midIns)
      (linPost tailSlot 12 (midOuts 0 d1Slot)) = true := by
  decide +kernel

theorem mid16_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 16 d2Slot) (linEnv midIns)
      (linPost tailSlot 12 (midOuts 16 d2Slot)) = true := by
  decide +kernel

/-- The S-box's output (slots `0 … 7`), the left word's output (slots
32–39) and both halves (slots 40–71). -/
def postIns : List (Nat × Nat) :=
  (List.range 8).map (fun k => (k, k)) ++ (List.range 40).map fun k => (ylSlot + k, 8 + k)

/-- The selected S-box output of byte `c` of plane `j` at position `b`. -/
def selG (j b c : Nat) : Nat :=
  if c < 4 then 32 * (8 + j) + 8 * c + b else 32 * W32.outSrc c j + 8 * (c - 4) + b

/-- Plane `8 w + j` of the half at slot `dst`, XOR the P-function of the
selected outputs. -/
def postG (dst w j p : Nat) : List Nat :=
  (32 * (16 + (dst - d1Slot) + 8 * w + j) + p) :: (pRow (4 * w + p / 8)).map (selG j (p % 8))

/-- The other half's slot. -/
def other (dst : Nat) : Nat := if dst = d1Slot then d2Slot else d1Slot

def postOuts (dst : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 16).map (fun k => (dst + k, postG dst (k / 8) (k % 8))) ++
    (List.range 16).map fun k => keepOut (other dst + k) (16 + (other dst - d1Slot) + k)

theorem post2_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d2Slot) (linEnv postIns)
      (linPost tailSlot 11 (postOuts d2Slot)) = true := by
  decide +kernel

theorem post1_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d1Slot) (linEnv postIns)
      (linPost tailSlot 11 (postOuts d1Slot)) = true := by
  decide +kernel

/-! ## The whitening -/

/-- Plane `i` of the halves (`D1`'s, then `D2`'s), XOR word `i` (or, with
`swap`, word `(i + 16) % 32`) of the entries at `kp`. -/
def whitenG (swap : Bool) (i p : Nat) : List Nat :=
  [32 * i + p, 32 * (32 + (if swap then (i + 16) % 32 else i)) + p]

def whitenOuts (swap : Bool) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun i => (d1Slot + i, whitenG swap i)

theorem whiten0_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten false) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (whitenOuts false)) = true := by
  decide +kernel

theorem whiten1_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten true) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (whitenOuts true)) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The slots below the table, without external words. -/
def bsCfg : Cfg := { base := sb, slots := keySlot, ext := sb, exts := 0 }

/-- The tail buffer's 32 words are input words `0 … 31`. -/
def tailIns : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, k)

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (d1Slot + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) bsCfg (linExt 0) ((List.range 4).flatMap toBsWord) (linEnv tailIns)
      (linPost keySlot 10 toBsOuts) = true := by
  decide +kernel

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`(w + 2) % 4` at `8 i + b`. -/
def fromBsG (t k : Nat) : List Nat := [32 * (8 * ((t % 4 + 2) % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 10) bsCfg (linExt 0) ((List.range 4).flatMap fromBsWord) (linEnv (halvesIns 0))
      (linPost keySlot 10 fromBsOuts) = true := by
  decide +kernel

/-! ## The subkeys' planes -/

/-- The entry at `kp`; the subkey's word in slot 0 of the scratch buffer. -/
def entryCfg : Cfg := { base := kp, slots := 16, ext := sb, exts := 1 }

/-- The other word's planes, input words `1 … 8`. -/
def keyIns (w : Nat) : List (Nat × Nat) := (List.range 8).map fun j => (8 * (1 - w) + j, 1 + j)

/-- Plane `j` of a subkey's word: bit `8 i + b` is bit `8 i + j` of the word
in slot 0. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

def keyOuts (w : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map (fun j => (8 * w + j, keyBsG j)) ++
    (List.range 8).map fun j => keepOut (8 * (1 - w) + j) (1 + j)

theorem keyPlanes0_check :
    check (lanes 32 9) entryCfg (linExt 0) ((List.range 8).flatMap (keyPlane 0)) (linEnv (keyIns 0))
      (linPost 16 9 (keyOuts 0)) = true := by
  decide +kernel

theorem keyPlanes1_check :
    check (lanes 32 9) entryCfg (linExt 0) ((List.range 8).flatMap (keyPlane 1)) (linEnv (keyIns 1))
      (linPost 16 9 (keyOuts 1)) = true := by
  decide +kernel

end VG.Proof.Camellia.X86
