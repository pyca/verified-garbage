module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb

/-!
# Bitslicing a subkey on RISC-V, by evaluation

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyChecks.lean`): `keyOne d` loads
the subkey at `[a0 + d]` (a byte at a time, `Words64.loadLE64_ok`) into
`q 0`, copies it to the other state registers and bitslices them as `toBs`
does eight blocks' halves (`keyRest`), and stores the planes to the entry
at `kp` (`keyStore`). Both are checked over the lane domain: the subkey is
input word 0 (in `q 0`), and the planes are input words `0 … 7` of the
stores.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 kp movR)
open VG.Proof.Camellia (pos)

/-- The masks' slots below the saved registers. -/
def keyCfg : Cfg := { base := sb, slots := savedSlot, ext := sb, exts := 0 }

def keyRest : List Instr := ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) kp (8 * j)

theorem keyOne_eq (d : Nat) :
    keyOne d = Impl.Words64.RISCV64.loadLE64 (q 0) t0 t2 .a0 d ++ keyRest ++ keyStore ++
      ([.addi kp kp 64] : List Instr) := by
  simp only [keyOne, keyRest, keyStore, List.append_assoc]

def keyEnv : Env (Nat × Nat) := linEnvG [(q 0, 0)] [] allMasks

/-- Plane `j` of the subkey: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def keyBsG (j p : Nat) : List Nat := [8 * pos (p / 8) + j]

theorem keyRest_check :
    check (lanes 64 7) keyCfg (linExt 0) keyRest keyEnv
      (linPostG 7 (qOuts keyBsG) [] maskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.RISCV64
