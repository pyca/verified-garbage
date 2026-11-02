module

public import VerifiedGarbage.Impl.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact Montgomery preparation for accepted and rejected CRT factors -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure AcceptedPrimeInput (base : BitVec 32) (len w : Nat) (s : State) : Prop
    extends LayoutFrameReady base len w s where
  stackFit : s.sp.toNat + 52 ≤ 2 ^ 32
  flagRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4
  bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1
  valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
    1 < numAt s.mem (State.addr base) w 0 ∧ numAt s.mem (State.addr base) w 0 % 2 = 1

theorem prepareAcceptedPrime_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : AcceptedPrimeInput base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa prepareAcceptedPrime s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr base) w 0)
      DoubleLoopReady base len w 0 t ∧ numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [prepareAcceptedPrime, WP.seq_iff]
  refine WP.mono (crt_primeAcceptance_ready s h.toLayoutFrameReady h.stackFit h.flagRead h.bit h.valid) ?_
  rintro u ⟨ready, number, value, frameU, restU⟩
  refine WP.mono (preparePrime_ok u ready countFits) ?_
  rintro t ⟨done, modulus, r2, frameT, restT⟩
  rw [number, value] at modulus r2
  exact ⟨done, modulus, r2, frameU.trans frameT, (restU.mono (by decide)).trans restT⟩

end VG.Proof.Bignum.Arm
