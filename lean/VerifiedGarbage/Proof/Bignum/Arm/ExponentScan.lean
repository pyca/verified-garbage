module
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The public-exponent scanner computes the exact low word and saturated high word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

abbrev exponentClobbers : List Reg := [.r1, .r3, .r4, .r5, .r7, .lr]

theorem exponentLoop_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .r1 = ep) (count : s.gpr .lr = BitVec.ofNat 32 eb.length)
    (low : s.gpr .r3 = 0) (high : s.gpr .r4 = 0) :
    WP isa (.loop exponentByte .ne) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .r4 = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Rest exponentClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧
    t.gpr .r3 = BitVec.ofNat 32 (pre eb j % 2 ^ 32) ∧
    t.gpr .r4 = BitVec.ofNat 32 (exponentHigh (pre eb j)) ∧
    t.gpr .r1 = ep + BitVec.ofNat 32 j ∧ t.gpr .lr = BitVec.ofNat 32 k ∧
    t.mem = s.mem ∧ Rest exponentClobbers s t
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, lo, hi, pointer, counter, mem, rest⟩ := inv
    have hj : j < eb.length := by omega
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [rest.rd, rest.wr, address]
      exact CallLay.inRegions_sub read (by omega) (by omega)
    have currentByte : t.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
      rw [mem, address]; exact bytes j hj
    refine WP.mono (exponentByte_ok t hk (by omega) pointer counter currentRead currentByte lo hi) ?_
    rintro u ⟨loU, hiU, ptrU, countU, zero, memU, restU⟩
    have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
      rw [pre_succ eb hj, Nat.mul_comm]
    rw [next] at loU hiU
    have ptrNext : u.gpr .r1 = ep + BitVec.ofNat 32 (j + 1) := by
      rw [ptrU]
      change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases last : k = 1
    · left
      refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, last, decide_true, Bool.not_true]
      · simpa only [show j + 1 = eb.length by omega, pre_len] using loU
      · simpa only [show j + 1 = eb.length by omega, pre_len] using hiU
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, loU, hiU, ptrNext, countU,
        memU.trans mem, rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega, positive, low, by simpa [pre_zero, exponentHigh] using high, by simpa using ptr, count, rfl, Rest.refl _ _⟩

theorem exponentScan_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .r1 = ep) (count : s.gpr .lr = BitVec.ofNat 32 eb.length) :
    WP isa exponentScan s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .r4 = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Rest exponentClobbers s t := by
  rw [exponentScan, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => WP.block_nil ?_
  have rest : Rest [.r3, .r4] s v := (a.rest (by simp)).trans (b.rest (by simp))
  have mem := b.mem.trans a.mem
  refine WP.mono (exponentLoop_ok v positive countFit sourceFit
    (by rw [rest.rd, rest.wr]; exact read) (by rw [mem]; exact bytes)
    ((rest.gpr .r1 (by simp)).trans ptr) ((rest.gpr .lr (by simp)).trans count)
    ((b.other .r3 (by decide)).trans a.gpr) b.gpr) ?_
  rintro t ⟨lo, hi, memT, restT⟩
  exact ⟨lo, hi, memT.trans mem, (rest.mono (by simp [exponentClobbers])).trans restT⟩

end VG.Proof.Bignum.Arm
