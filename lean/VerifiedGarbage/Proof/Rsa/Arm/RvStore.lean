module
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # An array of the key working space written out under the mask (`store_ok'`)

`CrtValues.store j` for any output region `R` apart from the working space
(`CvStore.lean`'s `store_ok`, without `vg_rsa_crt_values`'s state).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (read_low add_ofNat_sub_one mask_slot)

theorem store_ok' {s : State} {B : BitVec 32} {Z w N : Nat} (hw : Ws s B Z w N) (hN : N ≤ 256) {j : Nat}
    (hj : j < N) {R : Region} (hRS : R.Disjoint ⟨State.addr B, Z⟩) (hRw : R ∈ s.wr)
    {dst : BitVec 32} {k : Nat} (hb : R = ⟨State.addr dst, k⟩) (hk : 0 < k) (hkw : k ≤ 4 * w)
    (fit : dst.toNat + k ≤ 2 ^ 32) (p10 : s.gpr .r10 = dst) (p11 : s.gpr .r11 = BitVec.ofNat 32 k)
    (mb : slot s.mem B sMask ≤ 1) (hZ : sMask + 4 ≤ Z) :
    WP isa (store j) s fun t => Ws t B Z w N ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if slot s.mem B sMask = 1 then
          Spec.Rsa.i2osp (num s.mem B w j % 2 ^ (8 * k)) k else List.replicate k 0) ∧
      Frame [R] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have fa := hw.arr_fit hj
  have nw := hw.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have hwS : ⟨State.addr B, Z⟩ ∈ s.wr := hw.writable
  unfold store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine ptr_ok hw (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
  have R5 : Rest [.r0, .r1, .lr] s s5 := (r1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  have M5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have ad : State.addr (B + BitVec.ofNat 32 (arr w j)) = off (State.addr B) (arr w j) := hw.addr (by omega)
  have srcFit : (B + BitVec.ofNat 32 (arr w j)).toNat + k ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (reverseBuffer_ok s5 (src := B + BitVec.ofNat 32 (arr w j)) (dst := dst) (n := k)
    hk srcFit fit (by omega)
    ⟨⟨State.addr B, Z⟩, List.mem_append_right _ (by rw [R5.wr]; exact hwS),
      by rw [ad]; exact Offset.contains_base _ (by omega) (by omega)⟩
    ⟨R, by rw [R5.wr]; exact hRw, by rw [hb]; exact Region.contains_self _ _⟩
    (fun a ha hb' => hRS a (by rw [hb]; exact hb') (by
      rw [ad] at ha
      exact Region.Contains.byte (r := ⟨State.addr B, Z⟩) (b := off (State.addr B) (arr w j)) (n := k)
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
  have sm : t6.mem.readW (off (State.addr B) sMask) 32 = BitVec.ofNat 32 (slot s.mem B sMask) := by
    rw [f6.readW (r := ⟨State.addr B, Z⟩) (Offset.contains_base _ hZ (by omega))
      (by simpa using hRS.symm) (by decide), M5]
    simp
  have r2v : s11.gpr .r2 = -BitVec.ofNat 32 (decide (slot s.mem B sMask = 1)).toNat := by
    rw [u11.gpr, dpVal, u10.gpr, u10.other _ (by decide), u9.gpr, u8.mem, u7.mem, sm, mask_slot mb]
  refine WP.mono (maskBuffer_ok s11 hk (by omega) fit ⟨R, by rw [R11.wr, r6.wr, R5.wr]; exact hRw,
      by rw [hb]; exact Region.contains_self _ _⟩
    (by rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide),
      u7.gpr, r6.gpr _ (by decide), R5.gpr _ (by decide), p10])
    (by rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr,
      u7.other _ (by decide), r6.gpr _ (by decide), R5.gpr _ (by decide), p11])) ?_
  rintro t ⟨bt, ft, rt⟩
  rw [← hb] at ft
  refine ⟨(h8.rest ((u9.rest (ws := [.r1, .r2]) (by simp)).trans
    ((u10.rest (by simp)).trans (u11.rest (by simp))))).rest rt, ?_, ?_, ?_⟩
  · rw [bt, r2v, acceptance_bytes_mask, M11, by6, ad, read_low _ _ (n := w) hkw, M5]
    by_cases e : slot s.mem B sMask = 1 <;> simp [e, VG.Proof.Rsa.i2osp_length]
  · exact (f6.trans (M11 ▸ ft) : Frame [R] s5.mem t.mem) |> fun f => M5 ▸ f
  · exact R5.mono (by simp) |>.trans (r6.trans (R11.trans (rt.mono (by simp))))

end VG.Proof.Rsa.Arm.Keys
