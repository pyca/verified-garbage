module

public import VerifiedGarbage.Impl.Camellia.Arm.Ecb
public import VerifiedGarbage.Proof.Camellia.Bitsliced32
public import VerifiedGarbage.Proof.Sm4.Arm.LinG
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# The linear layers of bitsliced Camellia on ARMv7, by evaluation

Each linear block is checked by evaluation over the lane domain
(`Framework/Arm/Linear.lean`, with words in slots: `Sm4/Arm/LinG.lean`):
the kernel runs it on its input words as atoms and compares every output
bit with the XOR of input bits given here, bit `t` of input word `i`
being `32 i + t`.

* A round's left word (`preL`): the source half's planes (slots `src …`)
  are input words `0 … 15`, the subkeys' planes at `kp` words `16 …`.
* The middle (`midLR`): the left word's S-box output in the state
  registers is words `0 … 7`, the source half's planes `8 … 23`, the
  subkeys' planes at `kp` words `24 …`.
* The end (`postP`): the right word's S-box output in the state registers
  is words `0 … 7`, the left word's selected output (slots 32–39) words
  `8 … 15`, the halves' planes (slots 40–71) words `16 … 47`.
* The whitening: the halves' planes are words `0 … 31`, the two entries
  at `kp` words `32 … 63`.
* The transposes (`toBsWord`, `fromBsWord`): the tail buffer's eight
  blocks (slots 632–663) are words `0 … 31`; the halves' planes are.

Position `p = 8 i + b` of a plane of word `w` is byte `4 w + i` of the half
of block `b`.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Bitslice VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Arm.Straight (inWord outWord bitOf xorBits assign)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp)
open VG.Proof.Sm4.Arm (linEnvG linPostG linG_ok)
open VG.Proof.Camellia (pRow)


/-- The registers `q 0 … q 7` hold input words `0 … 7`. -/
def qIns : List (Reg × Nat) := (List.range 8).map fun k => (q k, k)

/-- The outputs `q j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-! ## A round -/

/-- The slots below the table; the two entries' 32 words at `kp`. -/
def layerCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 32 }

/-- The slots below the table, without the subkeys. -/
def linCfg : Cfg := { base := sb, slots := keySlot, ext := kp, exts := 0 }

/-- The half at slot `src`, from input word `x`. -/
def halfIns (src x : Nat) : List (Nat × Nat) := (List.range 16).map fun k => (src + k, x + k)

/-- The halves' slots. -/
def halvesSlots : List Nat := (List.range 32).map (d1Slot + ·)

/-- Both halves (slots 40–71), from input word `x`. -/
def halvesIns (x : Nat) : List (Nat × Nat) := halfIns d1Slot x ++ halfIns d2Slot (x + 16)

def preEnv : Env (Nat × Nat) := linEnvG [] (halvesIns 0) []

/-- The left word's S-box input: plane `j` at `p` is the selected plane of
the source half (at slot `src`) XOR the subkey's, at word `off` of `kp`. -/
def preG (off src j p : Nat) : List Nat :=
  [32 * (src - d1Slot + W32.inSrc (p / 8) j) + p, 32 * (32 + off + W32.inSrc (p / 8) j) + p]

theorem preL0_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 0 d1Slot) preEnv
      (linPostG 11 (qOuts (preG 0 d1Slot)) [] halvesSlots preEnv) = true := by
  decide +kernel

theorem preL16_check :
    check (lanes 32 11) layerCfg (linExt 32) (preL 16 d2Slot) preEnv
      (linPostG 11 (qOuts (preG 16 d2Slot)) [] halvesSlots preEnv) = true := by
  decide +kernel

def midEnv : Env (Nat × Nat) := linEnvG qIns (halvesIns 8) []

/-- The left word's selected output, to slot `32 + j`. -/
def ylG (j p : Nat) : List Nat := [32 * W32.outSrc (p / 8) j + p]

/-- The right word's S-box input. -/
def midG (off src j p : Nat) : List Nat :=
  [32 * (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j) + p,
   32 * (48 + off + W32.inSrc (4 + p / 8) j) + p]

def ylOuts : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (ylSlot + j, ylG j)

theorem mid0_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 0 d1Slot) midEnv
      (linPostG 12 (qOuts (midG 0 d1Slot)) ylOuts halvesSlots midEnv) = true := by
  decide +kernel

theorem mid16_check :
    check (lanes 32 12) layerCfg (linExt 40) (midLR 16 d2Slot) midEnv
      (linPostG 12 (qOuts (midG 16 d2Slot)) ylOuts halvesSlots midEnv) = true := by
  decide +kernel

/-- The left word's output (slots 32–39) and both halves (slots 40–71). -/
def postIns : List (Nat × Nat) := (List.range 40).map fun k => (ylSlot + k, 8 + k)

def postEnv : Env (Nat × Nat) := linEnvG qIns postIns []

/-- The selected S-box output of byte `c` of plane `j` at position `b`. -/
def selG (j b c : Nat) : Nat :=
  if c < 4 then 32 * (8 + j) + 8 * c + b else 32 * W32.outSrc c j + 8 * (c - 4) + b

/-- Plane `8 w + j` of the half at slot `dst`, XOR the P-function of the
selected outputs. -/
def postG (dst w j p : Nat) : List Nat :=
  (32 * (16 + (dst - d1Slot) + 8 * w + j) + p) :: (pRow (4 * w + p / 8)).map (selG j (p % 8))

def postOuts (dst : Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 16).map fun k => (dst + k, postG dst (k / 8) (k % 8))

/-- The slots of the other half. -/
def otherSlots (dst : Nat) : List Nat :=
  (List.range 16).map ((if dst = d1Slot then d2Slot else d1Slot) + ·)

theorem post2_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d2Slot) postEnv
      (linPostG 11 [] (postOuts d2Slot) (otherSlots d2Slot) postEnv) = true := by
  decide +kernel

theorem post1_check :
    check (lanes 32 11) linCfg (linExt 48) (postP d1Slot) postEnv
      (linPostG 11 [] (postOuts d1Slot) (otherSlots d1Slot) postEnv) = true := by
  decide +kernel

/-! ## The whitening -/

def whitenEnv : Env (Nat × Nat) := linEnvG [] (halvesIns 0) []

/-- Plane `i` of the halves (`D1`'s, then `D2`'s), XOR word `i` (or, with
`swap`, word `(i + 16) % 32`) of the entries at `kp`. -/
def whitenG (swap : Bool) (i p : Nat) : List Nat :=
  [32 * i + p, 32 * (32 + (if swap then (i + 16) % 32 else i)) + p]

def whitenOuts (swap : Bool) : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun i => (d1Slot + i, whitenG swap i)

theorem whiten0_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten false) whitenEnv
      (linPostG 11 [] (whitenOuts false) [] whitenEnv) = true := by
  decide +kernel

theorem whiten1_check :
    check (lanes 32 11) layerCfg (linExt 32) (whiten true) whitenEnv
      (linPostG 11 [] (whitenOuts true) [] whitenEnv) = true := by
  decide +kernel

/-! ## The transposes -/

/-- The working space at `sb`, and the tail buffer's 32 words at `r12`. -/
def toBsCfg : Cfg := { base := sb, slots := keySlot, ext := u7, exts := 32 }

def toBsEnv : Env (Nat × Nat) := linEnvG [] [] []

/-- Plane `j` of the state's word `w`, at `p = 8 i + b`: bit `j` of byte `i`
of word `w` of block `b` (the tail buffer's word `4 b + w`). -/
def toBsG (w j p : Nat) : List Nat := [32 * (4 * (p % 8) + w) + 8 * (p / 8) + j]

def toBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (d1Slot + k, toBsG (k / 8) (k % 8))

theorem toBs_check :
    check (lanes 32 10) toBsCfg (linExt 0) ((List.range 4).flatMap toBsWord) toBsEnv
      (linPostG 10 [] toBsOuts [] toBsEnv) = true := by
  decide +kernel

/-- The working space at `sb`, up to the end of the tail buffer, whose
words the transpose stores. -/
def fromBsCfg : Cfg := { base := sb, slots := tailSlot + 32, ext := sb, exts := 0 }

/-- The halves' planes, input words `d1Slot … d1Slot + 31`. -/
def fromBsIns : List (Nat × Nat) := (List.range 32).map fun k => (d1Slot + k, d1Slot + k)

def fromBsEnv : Env (Nat × Nat) := linEnvG [] fromBsIns []

/-- Bit `8 i + j` of the tail buffer's word `t = 4 b + w`, byte `i` (from the
most significant) of word `w` of block `b`: plane `j` of the state's word
`(w + 2) % 4` at `8 i + b` (the working space's word `40 + 8 ((w + 2) % 4) + j`). -/
def fromBsG (t k : Nat) : List Nat := [32 * (d1Slot + 8 * ((t % 4 + 2) % 4) + k % 8) + 8 * (k / 8) + t / 4]

def fromBsOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun t => (tailSlot + t, fromBsG t)

theorem fromBs_check :
    check (lanes 32 12) fromBsCfg (linExt 0) ((List.range 4).flatMap fromBsWord) fromBsEnv
      (linPostG 12 [] fromBsOuts [] fromBsEnv) = true := by
  decide +kernel

/-! ## The subkeys' planes -/

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 16, ext := kp, exts := 0 }

/-- The word in `q 4` is input word 0, the entry's words `1 … 16`. -/
def keyEnv : Env (Nat × Nat) := linEnvG [(q 4, 0)] ((List.range 16).map fun k => (k, 1 + k)) []

/-- Plane `j` of a subkey's word: bit `8 i + b` is bit `8 i + j` of the word
in `q 4`. -/
def keyBsG (j p : Nat) : List Nat := [8 * (p / 8) + j]

def keyOuts (w : Nat) : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (8 * w + j, keyBsG j)

/-- The other word's planes. -/
def keyKeep (w : Nat) : List Nat := (List.range 8).map fun j => 8 * (1 - w) + j

theorem keyPlanes0_check :
    check (lanes 32 10) entryCfg (linExt 0) (keyPlanes 0) keyEnv
      (linPostG 10 [] (keyOuts 0) (keyKeep 0) keyEnv) = true := by
  decide +kernel

theorem keyPlanes1_check :
    check (lanes 32 10) entryCfg (linExt 0) (keyPlanes 1) keyEnv
      (linPostG 10 [] (keyOuts 1) (keyKeep 1) keyEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.Arm
