import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Spec.TripleDes.Cbc

/-!
# Triple DES-CBC's blocks, for every target's core

What each target's core for the modes (`<Target>/ModeCore.lean`) shares:
the cipher of each direction (`dirCipher`), Triple DES's blocks as the
modes' (`bytesAt_eq`, `cbcBlocksAt_eq`), and a copy of the schedule as the
schedule (`scheduleAt_copy`).
-/

namespace VG.Proof.TripleDes

open VG
open VG.Spec.TripleDes (Direction)

/-- The cipher of the direction `d`. -/
def dirCipher : Direction → Spec.TripleDes.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.TripleDes.cipher
  | .decrypt => Spec.TripleDes.invCipher

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 8 = (Spec.TripleDes.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, Spec.TripleDes.blockAt]

theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Modes.blocksOf 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Modes.blocksOf, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-- The 8 bytes at `p` as a block. -/
theorem ofFn_bytesAt (m : Mem) (p : Addr) :
    (Vector.ofFn fun i : Fin 8 => (Spec.Aes.bytesAt m p 8).getD i.val 0) = Spec.TripleDes.blockAt m p := by
  ext i hi; simp [Spec.Aes.bytesAt, Spec.TripleDes.blockAt]

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
