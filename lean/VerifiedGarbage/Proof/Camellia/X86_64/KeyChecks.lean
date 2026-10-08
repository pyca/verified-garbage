import VerifiedGarbage.Proof.Camellia.X86_64.Linear
import VerifiedGarbage.Impl.Camellia.X86_64.Ecb

/-!
# Bitslicing a subkey on x86-64, by evaluation

`keyOne d` loads the subkey at `[rdi + d]` into all eight state registers,
bitslices them as `toBs` does eight blocks' halves (`keyLoad`), and stores
the planes to the entry at `rsi` (`keyStore`). Both are checked over the
lane domain: the subkey is input word `d / 8` (words of `rdi`), and the
planes are input words `0 … 7` of the stores.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (pos)

/-- The masks' slots below the table; the subkeys at `rdi`, of which `n` words are read. -/
def keyCfg (n : Nat) : Cfg := { base := sb, slots := keySlot, ext := .rdi, exts := n }

def keyLoad (d : Nat) : List Instr :=
  [.mov (q 0) (.mem (at_ .rdi d))] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

def keyStore : List Instr := (List.range 8).map fun j => .store (slotAt .rsi j) (q j)

theorem keyOne_eq (d : Nat) : keyOne d = keyLoad d ++ keyStore ++ [.alu .add .rsi (.imm 64)] := by
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

/-- The entry at `rsi`. -/
def entryCfg : Cfg := { base := .rsi, slots := 8, ext := .rsi, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
