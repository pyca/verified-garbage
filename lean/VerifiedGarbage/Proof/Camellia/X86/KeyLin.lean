module

public import VerifiedGarbage.Proof.Camellia.X86.Linear
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
import Mathlib.Tactic.SplitIfs

/-!
# Camellia's key schedule on x86 (32-bit): the transposes of one value

As on ARMv7 (`Proof/Camellia/Arm/KeyLin.lean`): `pairPlain` runs the
bitsliced rounds on eight copies of the running value. `bcast_check`: each
of its four words (at `wSlot`) in all eight lanes, transposed into the
planes of the halves; `unbcast_check`: lane 0's words back from the planes.
The values live in the tail buffer (input words `0 … 31` of `bcast`, `32 …
63` of `unbcast`, after the planes), which both keep but for what they
write.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Bitslice VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb)

/-- The tail buffer's 32 words, from input word `x`. -/
def tailIns' (x : Nat) : List (Nat × Nat) := (List.range 32).map fun k => (tailSlot + k, x + k)

/-- Plane `j` of the state's word `w`, at `8 i + b`: bit `8 i + j` of the
value's word `w` (the tail buffer's word 8 + w). -/
def bcastG (w j p : Nat) : List Nat := [32 * (8 + w) + 8 * (p / 8) + j]

def bcastOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map (fun k => (d1Slot + k, bcastG (k / 8) (k % 8))) ++
    (List.range 32).map fun k => keepOut (tailSlot + k) k

theorem bcast_check :
    check (lanes 32 10) bsCfg (linExt 0) bcast (linEnv (tailIns' 0)) (linPost keySlot 10 bcastOuts) = true := by
  decide +kernel

/-- Bit `8 i + j` of the value's word `w`: plane `j` of the state's word `w`, at `8 i` (lane 0). -/
def unbcastG (w t : Nat) : List Nat := [32 * (8 * w + t % 8) + 8 * (t / 8)]

def unbcastOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 4).map (fun w => (wSlot + w, unbcastG w)) ++
    ((List.range 32).filter fun k => !(8 ≤ k && k < 12)).map fun k => keepOut (tailSlot + k) (32 + k)

theorem unbcast_check :
    check (lanes 32 11) bsCfg (linExt 0) unbcast (linEnv (halvesIns 0 ++ tailIns' 32))
      (linPost keySlot 11 unbcastOuts) = true := by
  decide +kernel

end VG.Proof.Camellia.X86
