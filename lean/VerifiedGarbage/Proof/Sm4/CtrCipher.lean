import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Sm4.Ctr

/-!
# SM4's cipher for the modes, on any target

What every target's core for the modes (`Proof/Sm4/<Target>/ModeCore.lean`)
uses of `Spec.Sm4.cipher`: the schedule is read from memory
(`scheduleAt_congr`), and the cipher of the 16 bytes at `p` is the output of
the 32 rounds (`quads`) with the schedule's round keys in encryption order
(`cipher_bytes`).
-/

namespace VG.Proof.Sm4

open VG
open VG.Spec.Aes (bytesAt)

theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (hb : ∀ k < 128, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    Spec.Sm4.scheduleAt m' p = Spec.Sm4.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega), hb (4 * i + 1) (by omega), hb (4 * i + 2) (by omega), hb (4 * i + 3) (by omega)]

theorem bytesAt_eq_blockAt (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Sm4.blockAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 h2
  simp [bytesAt, Spec.Sm4.blockAt]

theorem ofFn_toList (v : Spec.Sm4.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

theorem cipher_bytes (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    Spec.Sm4.cipher k (bytesAt m p 16) =
      (outBlock (quads .enc (fun i => k.getD i 0) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  rw [Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq]

end VG.Proof.Sm4
