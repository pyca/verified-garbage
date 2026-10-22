module

public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry
import VerifiedGarbage.Proof.Framework.Offset

/-! # Restoring the borrowed bytes establishes the shared round's frame

The loop may temporarily use the existing multiplication's larger scratch
range. Only the two saved prefixes need restoring to recover precisely the
already reviewed compact Miller–Rabin preservation contract.
-/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG
open VG.Spec.Rsa.Mont (arrAt)

def workingRanges (w : Nat) : List (Nat × Nat) :=
  [(scratch w, Spec.Rsa.MontMul.scratchBytes w),
   (arrAt w 5, 8 * w), (arrAt w 6, 8 * w), (arrAt w 8, 8 * w),
   (arrAt w 11, 16 * (8 * (w + 2))), (184, 8), (208, 8), (232, 16)]

theorem restored_keeps {ws : Addr} {len w : Nat} {m m' : Mem}
    (keep : Spec.Rsa.MontMul.Keeps ws len (workingRanges w) m m')
    (tail : ∀ i < 32,
      m' (ws + BitVec.ofNat 64 (scratch w + i)) = m (ws + BitVec.ofNat 64 (scratch w + i)))
    (array : ∀ i < 8 * w,
      m' (ws + BitVec.ofNat 64 (arrAt w 4 + i)) = m (ws + BitVec.ofNat 64 (arrAt w 4 + i))) :
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact ws len w m m' := by
  intro i hi heads arrays table
  by_cases ht : scratch w ≤ i ∧ i < scratch w + 32
  · have := tail (i - scratch w) (by omega)
    simpa only [Nat.add_sub_of_le ht.1] using this
  by_cases ha : arrAt w 4 ≤ i ∧ i < arrAt w 4 + 8 * w
  · have := array (i - arrAt w 4) (by omega)
    simpa only [Nat.add_sub_of_le ha.1] using this
  apply keep i hi
  intro r hr
  simp only [workingRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h2 := arrays 2 (by simp [Spec.MillerRabin.compact])
    have h3 := arrays 3 (by simp [Spec.MillerRabin.compact])
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes, scratch, Spec.Rsa.MontMul.scratchBytes] at ht ha h2 h3 ⊢
    omega
  · have h := arrays 5 (by simp [Spec.MillerRabin.compact])
    omega
  · have h := arrays 6 (by simp [Spec.MillerRabin.compact])
    omega
  · have h := arrays 8 (by simp [Spec.MillerRabin.compact])
    omega
  · simp only [Spec.MillerRabin.compact, arrAt, Spec.Rsa.Mont.hdrBytes] at table ⊢
    omega_using [table]
  · have h := heads 23 (by simp [Spec.MillerRabin.compact])
    omega
  · have h := heads 26 (by simp [Spec.MillerRabin.compact])
    omega
  · have h29 := heads 29 (by simp [Spec.MillerRabin.compact])
    have h30 := heads 30 (by simp [Spec.MillerRabin.compact])
    omega

end VG.Proof.MillerRabin.X86
