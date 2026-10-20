module
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.LoadBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Zero-extended RSA integer import, including partial native words -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem loadBE_ok (s : State) {src dst : BitVec 32} {n k : Nat}
    (hk : 0 < k) (fit : k ≤ 4 * n) (countFits : k < 2 ^ 32)
    (srcFit : src.toNat + k ≤ 2 ^ 32) (dstFit : dst.toNat + 4 * n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (write : InRegions s.wr (State.addr dst) (4 * n))
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr dst, 4 * n⟩)
    (p0 : s.gpr .r0 = dst) (p4 : s.gpr .r4 = src) (p5 : s.gpr .r5 = dst)
    (p6 : s.gpr .r6 = BitVec.ofNat 32 k) (count : s.gpr .lr = BitVec.ofNat 32 n)
    (zero : s.gpr .r3 = 0) :
    WP isa loadBE s fun t =>
      val32 t.mem (State.addr dst) 0 n = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr dst, 4 * n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [loadBE, WP.seq_iff]
  refine WP.mono (zero_ok s (base := dst) (o := 0) (n := n)
    ⟨dstFit, by omega, write⟩ (by omega) (by simpa using p0) count zero) ?_
  intro u zi
  rw [WP.seq_iff]
  refine WP.mono (loadBEreverseArgs_ok u hk ((zi.rest.gpr .r6 (by simp)).trans p6)) ?_
  rintro v ⟨dptr, sptr, len, memV, restV⟩
  have keep : Rest [.r0, .r1, .r2, .lr] s v :=
    (zi.rest.mono (by simp)).trans (restV.mono (by simp))
  have frameV : Frame [⟨State.addr dst, 4 * n⟩] s.mem v.mem := by rw [memV]; exact zi.frame
  have vr : InRegions (v.rd ++ v.wr) (State.addr src) k := by rw [keep.rd, keep.wr]; exact read
  have vw : InRegions v.wr (State.addr dst) k := by
    rw [keep.wr]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CallLay.inRegions_sub (off := 0) write (by omega : 0 + k ≤ 4 * n) (by omega)
  have ctx := reverseCtx_of_regions v src dst countFits srcFit (by omega) vr vw
    (sep.sub_right (Region.sub_prefix fit))
  refine WP.mono (reverseBytes_ok v ctx hk
    (sptr.trans (congrArg (fun x => x + BitVec.ofNat 32 (k - 1))
      ((zi.rest.gpr .r4 (by simp)).trans p4)))
    (dptr.trans ((zi.rest.gpr .r5 (by simp)).trans p5)) len) ?_
  intro t ri
  have input : Spec.Rsa.bytesAt v.mem (State.addr src) k = Spec.Rsa.bytesAt s.mem (State.addr src) k := by
    unfold Spec.Rsa.bytesAt
    apply List.map_congr_left
    intro j hj
    have hj' : j < k := List.mem_range.mp hj
    apply frameV
    intro r hr hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact sep _ (Offset.contains_base _ (by omega) (by omega)) hc
  have padding : ∀ j, k ≤ j → j < 4 * n → t.mem (State.addr dst + BitVec.ofNat 64 j) = 0 := by
    intro j hj hjn
    rw [ri.outside _ ?_, memV]
    · have z := byte_zero_of_val32 zi.value hjn
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using z
    · intro l hl he
      rw [addr_add (by omega)] at he
      have e := congrArg (fun a => (a - State.addr dst).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64),
        Mem.sub_ofNat_toNat _ (by omega : l < 2 ^ 64)] at e
      omega
  refine ⟨?_, ?_, keep.trans ri.rest⟩
  · rw [val32_zero_extension _ _ fit padding, ri.os2ip srcFit (by omega), input]
  · apply frameV.trans
    exact (ri.frame (by omega)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact ⟨_, by simp, Region.sub_prefix fit⟩

end VG.Proof.Bignum.Arm
