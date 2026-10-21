module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosFixed
import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose a statically bounded scan without advancing the operand pointers. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFixed
open VG VG.Arm VG.Proof.Bignum.Arm

theorem pairs_ok {s0 : State} {x q base : BitVec 32} {size acc b mod n start : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) :
    ∀ k i s, Inv s0 x q base acc b mod n start i s → i+2*k+1≤n →
      4*(i+2*k-start)+8<4096 →
      WP isa (VG.Impl.Bignum.Arm.FiosFixed.pairs (4*(i-start)) k) s
        (Inv s0 x q base acc b mod n start (i+2*k))
  | 0, i, s, h, _, _ => by simpa only [VG.Impl.Bignum.Arm.FiosFixed.pairs,Nat.mul_zero,Nat.add_zero] using WP.block_nil h
  | k+1, i, s, h, bound, offset => by
    rw [VG.Impl.Bignum.Arm.FiosFixed.pairs,WP.seq_iff]
    refine WP.mono (pairAt_inv ctx h (by omega) (by have := h.progress;omega)) ?_
    intro t ht
    have next : 4*(i-start)+8=4*(i+2-start) := by have := h.progress;omega
    rw [next]
    have result := pairs_ok ctx k (i+2) t ht (by omega) (by omega)
    simpa only [show i+2+2*k=i+2*(k+1) by omega] using result

end VG.Proof.Bignum.Arm.FiosFixed
