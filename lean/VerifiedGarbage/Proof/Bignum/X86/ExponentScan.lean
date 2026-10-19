module
public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes

import VerifiedGarbage.Proof.Bignum.X86.ExponentByte
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The public-exponent scanner computes the exact low word and saturated high word -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

abbrev exponentClobbers : List Reg := [.esi, .ebx, .edx, .ebp, .eax, .ecx]

theorem exponentLoop_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length)
    (low : s.gpr .ebx = 0) (high : s.gpr .edx = 0) :
    WP isa (.loop exponentByte .ne) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧
    t.gpr .ebx = BitVec.ofNat 32 (pre eb j % 2 ^ 32) ∧
    t.gpr .edx = BitVec.ofNat 32 (exponentHigh (pre eb j)) ∧
    t.gpr .esi = ep + BitVec.ofNat 32 j ∧ t.gpr .ecx = BitVec.ofNat 32 k ∧
    t.mem = s.mem ∧ Keeps exponentClobbers s t
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, lo, hi, pointer, counter, mem, rest⟩ := inv
    have hj : j < eb.length := by omega
    have address : byteAddr (ep + BitVec.ofNat 32 j) = byteAddr ep + BitVec.ofNat 64 j :=
      byteAddr_add (by omega)
    have currentRead : InRegions (t.rd ++ t.wr) (byteAddr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [rest.2.1, rest.2.2, address]
      exact CallLay.inRegions_sub read (by omega) (by omega)
    have currentByte : t.mem (byteAddr (ep + BitVec.ofNat 32 j)) = eb[j] := by
      rw [mem, address]; exact bytes j hj
    refine WP.mono (exponentByte_ok t hk (by omega) pointer counter currentRead currentByte lo hi) ?_
    rintro u ⟨loU, hiU, ptrU, countU, zero, memU, restU⟩
    have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
      rw [pre_succ eb hj, Nat.mul_comm]
    rw [next] at loU hiU
    have ptrNext : u.gpr .esi = ep + BitVec.ofNat 32 (j + 1) := by
      rw [ptrU]
      change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases last : k = 1
    · left
      refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
      · change u.zf.map not = some false
        simp only [zero, last, decide_true, Option.map_some, Bool.not_true]
      · simpa only [show j + 1 = eb.length by omega, pre_len] using loU
      · simpa only [show j + 1 = eb.length by omega, pre_len] using hiU
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, loU, hiU, ptrNext, countU,
        memU.trans mem, rest.trans restU⟩
      change u.zf.map not = some true
      simp only [zero, last, decide_false, Option.map_some, Bool.not_false]
  · exact ⟨0, by omega, positive, low, by simpa [pre_zero, exponentHigh] using high, by simpa using ptr, count, rfl, Keeps.refl _ _⟩

theorem exponentScan_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentScan s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentScan, WP.seq_iff]
  refine wp_movS rfl fun u a _ => ?_
  refine wp_movS rfl fun v b _ => WP.block_nil ?_
  have rest : Keeps [.ebx, .edx] s v := (a.keeps.mono (by decide)).trans (b.keeps.mono (by decide))
  have mem := b.mem.trans a.mem
  refine WP.mono (exponentLoop_ok v positive countFit sourceFit
    (by rw [rest.2.1, rest.2.2]; exact read) (by rw [mem]; exact bytes)
    ((rest.1 .esi (by decide)).trans ptr) ((rest.1 .ecx (by decide)).trans count)
    ((b.other .ebx (by decide)).trans a.gpr) b.gpr) ?_
  rintro t ⟨lo, hi, memT, restT⟩
  exact ⟨lo, hi, memT.trans mem, (rest.mono (by decide)).trans restT⟩

end VG.Proof.Bignum.X86
