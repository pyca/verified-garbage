module

public import VerifiedGarbage.Proof.Seed.ModeBytes
import Mathlib.Tactic.SplitIfs

/-!
# SEED's cipher for the modes, on any target

What x86's core for the modes (`Proof/Seed/X86/ModeCore.lean`) adds to
`ModeBytes`: the cipher of a direction on the 16 bytes at `p` is
`Spec.Seed.crypt` with the schedule's round keys in that direction's order
(`dirCipher_bytes`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

theorem ofFn_toList (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- The round keys in the order of the direction `d`. -/
def dirKeys : Direction → Spec.Seed.Schedule → Nat → Spec.Seed.Word × Spec.Seed.Word
  | .encrypt, k => Spec.Seed.roundKey k
  | .decrypt, k => fun j => Spec.Seed.roundKey k (15 - j)

/-- The cipher of `d` on the 16 bytes at `p`: the rounds with the round keys
in `d`'s order. -/
theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) = (Spec.Seed.crypt (dirKeys d k) (Spec.Seed.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Seed.cipher, bytesAt_eq, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Seed.invCipher, bytesAt_eq, ofFn_toList]; rfl

end VG.Proof.Seed
