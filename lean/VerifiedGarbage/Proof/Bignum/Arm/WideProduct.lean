module
public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductState

import VerifiedGarbage.Proof.Bignum.Arm.WideProductBody
import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Exact wide multiplication terminates after the public number of source words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem wideProduct_ok (s : State) {base : BitVec 32} {size o a b m n : Nat}
    (ctx : WideProductCtx s base size o a b m n)
    (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = base + BitVec.ofNat 32 a)
    (bPtr : s.mem.readW (off (State.addr base) 132) 32 = base + BitVec.ofNat 32 b)
    (oPtr : s.mem.readW (off (State.addr base) 136) 32 = base + BitVec.ofNat 32 o)
    (count : s.mem.readW (off (State.addr base) 140) 32 = BitVec.ofNat 32 m)
    (width : s.mem.readW (off (State.addr base) 144) 32 = BitVec.ofNat 32 n)
    (zero : val32 s.mem (State.addr base) o (m + n + 2) = 0) :
    WP isa wideProduct s fun t =>
      val32 t.mem (State.addr base) o (m + n + 2) =
        val32 s.mem (State.addr base) a m * val32 s.mem (State.addr base) b n ∧
      Outs (State.addr base) [(128, 16), (o, 4 * (m + n + 2))] s.mem t.mem ∧
      t.gpr .r0 = base ∧ Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ i, i + k = m ∧ 0 < k ∧ WideProductInv s base o a b m n i t
  unfold wideProduct
  refine WP.loop (M := isa) I ?_ m s ?_
  · intro k t inv
    obtain ⟨i, ik, hk, hi⟩ := inv
    refine WP.mono (wideProductBody_ok t ctx hi (by omega)) ?_
    rintro u ⟨next, zero⟩
    by_cases last : i + 1 = m
    · left
      refine ⟨?_, ?_, next.outside, next.ptr, ctx.frame next.outside, next.rest⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · simpa only [last] using next.value
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, ctx.positiveA, ?_⟩
    refine ⟨by omega, ptr, ?_, bPtr, ?_, ?_, width, Outs.refl _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using aPtr
    · simpa only [Nat.mul_zero, Nat.add_zero] using oPtr
    · simpa only [Nat.sub_zero] using count
    · simp only [val32, Nat.zero_mul]; exact zero

end VG.Proof.Bignum.Arm
