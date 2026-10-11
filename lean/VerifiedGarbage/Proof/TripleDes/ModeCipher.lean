import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Spec.TripleDes.Cbc

/-!
# Triple DES's cipher for the modes, on any target

What every target's core for the modes (`Proof/TripleDes/<Target>/ModeCore.lean`)
uses of `Spec.TripleDes.cipher` and `invCipher`: the cipher of each direction
(`dirCipher`) on the 8 bytes at `p` is the block function's output on the
block there (`dirCipher_bytes`), and a copy of a schedule in memory is the
schedule (`scheduleAt_copy`).
-/

namespace VG.Proof.TripleDes

open VG
open VG.Spec.TripleDes (Direction)

/-- The cipher of the direction `d`. -/
def dirCipher : Direction → Spec.TripleDes.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.TripleDes.cipher
  | .decrypt => Spec.TripleDes.invCipher

/-- The block function of the direction `d`. -/
def dirBlock : Direction → Spec.TripleDes.Schedule → Spec.TripleDes.Block → Spec.TripleDes.Block
  | .encrypt => Spec.TripleDes.encryptBlock
  | .decrypt => Spec.TripleDes.decryptBlock

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 8 = (Spec.TripleDes.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, Spec.TripleDes.blockAt]

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (dirBlock d k (Spec.TripleDes.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 8 => (Spec.Aes.bytesAt m p 8).getD i.val 0) = Spec.TripleDes.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.TripleDes.blockAt]
  cases d <;> simp only [dirCipher, dirBlock, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, h]

theorem read_copy {m m' : Mem} : ∀ {n : Nat} {a b : Addr},
    (∀ i < n, m' (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i)) → m'.read a n = m.read b n
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, read_copy fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

/-- A copy of a schedule is the schedule. -/
theorem scheduleAt_copy {m m' : Mem} {p q : Addr} (h : ∀ i < 384, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.TripleDes.scheduleAt m' q = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [scheduleAt_readW _ _ i hi, scheduleAt_readW _ _ i hi]
  simp only [Mem.readW]
  exact congrArg (BitVec.setWidth 64) (read_copy fun j hj => by
    rw [Offset.add_add, Offset.add_add]; exact h _ (by omega))

end VG.Proof.TripleDes
