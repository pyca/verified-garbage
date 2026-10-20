module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByte
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! # The complete exponent-buffer loop computes its big-endian integer power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem bytes_ok {base ep : BitVec 32} {len w M : Nat} {eb : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (s : State)
    (h : Power base len w M 0 s) (hp : P s) (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r)
    (bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i])
    (pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length) :
    WP isa (VG.Impl.Bignum.Arm.TwoExp.bytes K.square K.twice) s fun t =>
      Power base len w M (Spec.Rsa.os2ip eb) t ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧ Power base len w M (pre eb j) t ∧ P t ∧
    t.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j ∧
    t.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 k ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold VG.Impl.Bignum.Arm.TwoExp.bytes
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, state, pt, ptr, counter, frame, rest⟩ := inv
    have hj : j < eb.length := by omega
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [rest.rd, rest.wr, address]
      exact CallLay.inRegions_sub read (by omega) (by omega)
    have currentByte : t.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
      rw [address, frame.bytes (R := ⟨State.addr ep, eb.length⟩)
        separate (by change eb.length ≤ 2 ^ 64; omega) hj]
      exact bytes j hj
    refine WP.mono (byte_ok K t state pt hk (by omega) ptr counter currentRead) ?_
    rintro u ⟨next, pu, ptrU, counterU, zero, frameU, restU⟩
    rw [currentByte] at next
    have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
      rw [pre_succ eb hj, Nat.mul_comm]
    rw [prefixEq] at next
    have ptrNext : u.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 (j + 1) := by
      rw [ptrU]
      change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases last : k = 1
    · left
      refine ⟨?_, ?_, pu, frame.trans frameU, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · simpa only [show j + 1 = eb.length by omega, pre_len] using next
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, next, pu, ptrNext, counterU,
        frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, positive, h, hp, ?_, count, Frame.refl _ _, Rest.refl _ _⟩
    simpa only [BitVec.add_zero] using pointer

end VG.Proof.Bignum.Arm.TwoExp
