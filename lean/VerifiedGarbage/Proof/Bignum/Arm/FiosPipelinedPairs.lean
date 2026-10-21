module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! Alternating two product registers keeps one product pending across pairs. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Bignum.Arm

theorem pair_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (h : Inv s0 x q base acc b mod n start i .r6 s)
    (hi : i+4≤n) (offsetFits : 4*(i-start)+12<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.pair (4*(i-start))) s
      (Inv s0 x q base acc b mod n start (i+2) .r6) := by
  rw [VG.Impl.Bignum.Arm.FiosPipelined.pair,WP.seq_iff]
  refine WP.mono (step_ok (Or.inl ⟨rfl,rfl⟩) ctx h (by omega) (by omega)) ?_
  intro t ht
  have next : 4*(i-start)+4=4*(i+1-start) := by have := h.progress;omega
  rw [next]
  exact step_ok (Or.inr ⟨rfl,rfl⟩) ctx ht (by omega) (by have := h.progress;omega)

theorem pairs_ok {s0 : State} {x q base : BitVec 32} {size acc b mod n start : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) :
    ∀ k i s, Inv s0 x q base acc b mod n start i .r6 s → i+2*k+2≤n →
      4*(i+2*k-start)+12<4096 →
      WP isa (VG.Impl.Bignum.Arm.FiosPipelined.pairs (4*(i-start)) k) s
        (Inv s0 x q base acc b mod n start (i+2*k) .r6)
  | 0, i, s, h, _, _ => by
    simpa only [VG.Impl.Bignum.Arm.FiosPipelined.pairs,Nat.mul_zero,Nat.add_zero] using WP.block_nil h
  | k+1, i, s, h, bound, offset => by
    rw [VG.Impl.Bignum.Arm.FiosPipelined.pairs,WP.seq_iff]
    refine WP.mono (pair_ok ctx h (by omega) (by have := h.progress;omega)) ?_
    intro t ht
    have next : 4*(i-start)+8=4*(i+2-start) := by have := h.progress;omega
    rw [next]
    have result := pairs_ok ctx k (i+2) t ht (by omega) (by omega)
    simpa only [show i+2+2*k=i+2*(k+1) by omega] using result

end VG.Proof.Bignum.Arm.FiosPipelined
