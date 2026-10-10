import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Camellia.Ctr

/-!
# Camellia's cipher for the modes, on any target

What every target's core for the modes
(`Proof/Camellia/<Target>/ModeCore.lean`) uses of `Spec.Camellia.cipher`:
the cipher of the 16 bytes at `p`, under the subkeys of the schedule's
words, is `cryptWords` of the block (`cipher_bytes`).
-/

namespace VG.Proof.Camellia

open VG

theorem bytesAt_eq_blockAt (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = (Spec.Camellia.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 h2
  simp [Spec.Aes.bytesAt, Spec.Camellia.blockAt]

theorem ofFn_toList (v : Spec.Camellia.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- The cipher on a block in memory: the eight-block code's words. -/
theorem cipher_bytes {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : Mem) (p : Addr) :
    Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords R ws) (Spec.Aes.bytesAt m p 16) =
      (Spec.Camellia.encodeBlock (cryptWords (R / 6) (fun i => ws.getD i 0)
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)))).toList := by
  rw [Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Camellia.encryptBlock, encryptWith_eq hR]

end VG.Proof.Camellia
