module
public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Framework.Lit

import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # `vg_rsa_crt_values` on ARMv7: an array written out under the mask (`store_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The low `k` bytes of an array. -/
theorem read_low (m : Mem) (base : Addr) {d n k : Nat} (hk : k ≤ 4 * n) :
    (m.read (off base d) k).toNat = val32 m base d n % 2 ^ (8 * k) := by
  rw [← read_eq_val32 m base n d, show 4 * n = (4 * n - k) + k by omega, VG.Proof.Mont.read_toNat_add]
  have := (m.read (off base d) k).isLt
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]

theorem add_ofNat_sub_one (x : BitVec 32) {k : Nat} (hk : 1 ≤ k) :
    x + BitVec.ofNat 32 k - 1 = x + BitVec.ofNat 32 (k - 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, show k = (k - 1) + 1 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.add_sub_cancel, show k - 1 + 1 - 1 = k - 1 by omega]

theorem mask_slot {m : Nat} (hm : m ≤ 1) :
    (0 - BitVec.ofNat 32 m) = -BitVec.ofNat 32 (decide (m = 1)).toNat := by
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> decide

theorem store_ok {s0 s : State} (h : Done s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {j : Nat}
    (hj : j < nArr) {R : Region} (hR : R = rDp s0 ∨ R = rDq s0 ∨ R = rQi s0) {dst : BitVec 32} {k : Nat}
    (hb : R = ⟨State.addr dst, k⟩) (hk : 0 < k) (hkw : k ≤ 4 * cvW s0) (fit : dst.toNat + k ≤ 2 ^ 32)
    (p10 : s.gpr .r10 = dst) (p11 : s.gpr .r11 = BitVec.ofNat 32 k) (mb : slot s.mem (cvB s0) sMask ≤ 1) :
    WP isa (store j) s fun t => Done s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if slot s.mem (cvB s0) sMask = 1 then
          Spec.Rsa.i2osp (num s.mem (cvB s0) (cvW s0) j % 2 ^ (8 * k)) k else List.replicate k 0) ∧
      Frame [R] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have pre := h.pre
  have fa := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  have w16 := pre.w16
  have eZ : cvZ s0 = (stackArg s0 11).toNat * 8 := rfl
  have eB : (cvB s0).toNat = (stackArg s0 10).toNat := rfl
  have hRS : R.Disjoint (rS s0) := by
    rcases hR with rfl | rfl | rfl
    · exact pre.dpS
    · exact pre.dqS
    · exact pre.qiS
  have hRw : R ∈ s.wr := by rw [h.wr, pre.wr]; rcases hR with rfl | rfl | rfl <;> simp
  unfold store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
  have R5 : Rest [.r0, .r1, .lr] s s5 := (r1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  have M5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have d5 := h.of_rest R5 M5
  have ad : State.addr (cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) = off (State.addr (cvB s0)) (arr (cvW s0) j) :=
    hw.addr (by omega)
  have srcFit : (cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)).toNat + k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (reverseBuffer_ok s5 (src := cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) (dst := dst) (n := k)
    hk srcFit fit (by omega)
    ⟨rS s0, List.mem_append_right _ (by rw [d5.wr, pre.wr]; simp),
      by rw [ad]; exact Offset.contains_base _ (by omega) (by omega)⟩
    ⟨R, by rw [d5.wr]; exact h.wr ▸ hRw, by rw [hb]; exact Region.contains_self _ _⟩
    (fun a ha hb' => hRS a (by rw [hb]; exact hb') (by
      rw [ad] at ha
      exact Region.Contains.byte (r := rS s0) (b := off (State.addr (cvB s0)) (arr (cvW s0) j)) (n := k)
        (Offset.contains_base _ (by omega) (by omega)) (by simp only [Region.Contains] at ha; omega)))
    (by rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide),
      p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, dpVal, p1,
          r1.gpr .r11 (by decide), p11]
        exact add_ofNat_sub_one _ hk)
    (by rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide),
      p11])) ?_
  rintro t6 ⟨by6, f6, _, r6⟩
  rw [← hb] at f6
  have d6 := d5.out hR f6 r6.sp r6.rd r6.wr
  have h6 := (hw.rest R5).rest r6
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_mov (op2_reg _ _) fun s7 u7 => ?_
  refine wp_mov (op2_reg _ _) fun s8 u8 => ?_
  have h8 := (h6.of_upd u7 (by decide) (by decide) (by decide)).of_upd u8 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h8 (by decide) fun s9 u9 => ?_
  refine wp_mov (op2_imm (by decide)) fun s10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun s11 u11 => WP.block_nil ?_
  have R11 : Rest [.r0, .r1, .r2, .lr] t6 s11 := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans
    ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans (u11.rest (by simp)))))
  have M11 : s11.mem = t6.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]
  have sm : t6.mem.readW (off (State.addr (cvB s0)) sMask) 32 = BitVec.ofNat 32 (slot s.mem (cvB s0) sMask) := by
    have hz : 136 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) pre.fits
    rw [f6.readW (r := rS s0) (Offset.contains_base _ (by simp only [sMask]; omega) (by simp only [sMask]; omega))
      (by simpa using hRS.symm) (by decide), M5]
    simp
  have r2v : s11.gpr .r2 = -BitVec.ofNat 32 (decide (slot s.mem (cvB s0) sMask = 1)).toNat := by
    rw [u11.gpr, dpVal, u10.gpr, u10.other _ (by decide), u9.gpr, u8.mem, u7.mem, sm, mask_slot mb]
  refine WP.mono (maskBuffer_ok s11 hk (by omega) fit ⟨R, by rw [R11.wr, d6.wr, pre.wr]; rcases hR with rfl | rfl | rfl <;> simp,
      by rw [hb]; exact Region.contains_self _ _⟩
    (by rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide),
      u7.gpr, r6.gpr _ (by decide), R5.gpr _ (by decide), p10])
    (by rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr,
      u7.other _ (by decide), r6.gpr _ (by decide), R5.gpr _ (by decide), p11])) ?_
  rintro t ⟨bt, ft, rt⟩
  rw [← hb] at ft
  refine ⟨(d6.of_rest R11 M11).out hR ft rt.sp rt.rd rt.wr, (h8.rest ((u9.rest (ws := [.r1, .r2]) (by simp)).trans
    ((u10.rest (by simp)).trans (u11.rest (by simp))))).rest rt, ?_, ?_, ?_⟩
  · rw [bt, r2v, acceptance_bytes_mask, M11, by6, ad, read_low _ _ (n := cvW s0) hkw, M5]
    by_cases e : slot s.mem (cvB s0) sMask = 1 <;> simp [e, VG.Proof.Rsa.i2osp_length]
  · exact (f6.trans (M11 ▸ ft) : Frame [R] s5.mem t.mem) |> fun f => M5 ▸ f
  · exact R5.mono (by simp) |>.trans (r6.trans (R11.trans (rt.mono (by simp))))

end VG.Proof.Rsa.Arm.CrtValues
