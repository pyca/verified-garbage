module

import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# SEED's blocks and schedule as the modes see them

What every target's core for the modes (`Proof/Seed/<Target>/ModeCore.lean`)
needs: the cipher of each direction on the modes' blocks (`dirCipher`), a
block's bytes as the modes read them (`bytesAt_eq`), and the schedule at an
address, which depends only on its 128 bytes (`scheduleAt_congr_at`,
`scheduleAt_frame`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG.Spec.Seed (Direction)

/-- The cipher of the direction `d`. -/
def dirCipher : Direction → Spec.Seed.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Seed.cipher
  | .decrypt => Spec.Seed.invCipher

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 = (Spec.Seed.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]

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

/-- The schedule at `q` is the one at `p` if their 128 bytes are. -/
theorem scheduleAt_congr_at {m m' : Mem} {p q : Addr}
    (h : ∀ i < 128, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Seed.scheduleAt m' q = Spec.Seed.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [scheduleAt_readW _ _ i hi, scheduleAt_readW _ _ i hi]
  simp only [Mem.readW]
  exact congrArg (BitVec.setWidth 32) (read_copy fun j hj => by
    rw [Offset.add_add, Offset.add_add]; exact h _ (by omega))

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 128⟩ : Region).Disjoint r) :
    Spec.Seed.scheduleAt m' p = Spec.Seed.scheduleAt m p :=
  scheduleAt_congr_at fun _ hi => hf.bytes (R := ⟨p, 128⟩) hd (by show 128 ≤ 2 ^ 64; decide) hi

end VG.Proof.Seed
