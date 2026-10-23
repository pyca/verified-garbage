module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Linear
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
import Mathlib.Tactic.SplitIfs

/-!
# Bitslicing a subkey on PPC64LE, by evaluation

As on x86-64: `keyOne d` loads the subkey at `[r3 + d]` into all eight
state registers, bitslices them as `toBs` does eight blocks' halves
(`keyLoad`), and stores the planes to the entry at `kp` (`keyStore`). Both
are checked over the lane domain: the subkey is input word `d / 8` (words of
`r3`), and the planes are input words `0 … 7` of the stores.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR)
open VG.Proof.Camellia (pos)

/-- The masks' slots below the table; the subkeys at `r3`, of which `n` words are read. -/
def keyCfg (n : Nat) : Cfg := { base := sb, slots := keySlot, ext := .r3, exts := n }

def keyLoad (d : Nat) : List Instr :=
  [.load .d (q 0) .r3 d] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) kp (8 * j)

theorem keyOne_eq (d : Nat) : keyOne d = keyLoad d ++ keyStore ++ ([.addi kp kp 64] : List Instr) := by
  simp only [keyOne, keyLoad, keyStore, List.append_assoc]

def keyEnv : Env (Nat × Nat) := linEnvG [] [] layerMasks

/-- Plane `j` of the subkey: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def keyBsG (d j p : Nat) : List Nat := [64 * (d / 8) + 8 * pos (p / 8) + j]

theorem keyLoad0_check :
    check (lanes 64 7) (keyCfg 1) (linExt 0) (keyLoad 0) keyEnv
      (linPostG 7 (qOuts (keyBsG 0)) [] maskSlots keyEnv) = true := by
  decide +kernel

theorem keyLoad8_check :
    check (lanes 64 7) (keyCfg 2) (linExt 0) (keyLoad 8) keyEnv
      (linPostG 7 (qOuts (keyBsG 8)) [] maskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.PPC64LE
