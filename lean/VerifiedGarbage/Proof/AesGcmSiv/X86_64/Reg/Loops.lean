module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Interleave

/-!
# AES-GCM-SIV in registers on x86-64: the loops on the data's 256-byte groups

Untrusted: everything here is checked by Lean. `sealL` and `openL`
(`Impl/AesGcmSiv/X86_64Reg.lean`) run the loops of
`Impl/AesGcmSiv/X86_64Stitch.lean` on the data's groups of sixteen blocks,
for any loops that meet their contracts (`Stitch.LoopsOk`), which take `H`,
`Y` and the counter block in memory: the code before a loop stores them
(`putYH_ok`, `ctrArgs`), and the code after it takes POLYVAL's and counter
mode's registers up again from where the loop left them (`back_ok`,
`ctrBack`), for the rest of the data.
-/

-- separate module: the loops on the groups, apart from the pieces they run between

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO bO hO yO cmO tagO skO roundsO dataO lenO aadO alenO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ghashFrom blockAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc)
open VG.Proof.Gcm.X86_64.Pclmul (Only constImm_ok)
open VG.Proof.AesGcmSiv.X86_64 (Stitch.LoopsOk Stitch.HPre Stitch.HPost Stitch.SPre Stitch.CPost Stitch.DPost
  Stitch.nb Stitch.xR Stitch.yR Stitch.pR Stitch.xp Stitch.yp Stitch.hp Stitch.pp Stitch.hk Stitch.y₀ Stitch.xel)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt)
open VG.Proof.AesGcmSiv.X86_64 (le16 le16_readW bytesAt_writeW128 ctrX frame_outside)
open VG.Proof.Cmac (le4)
open VG.Proof.AesGcmSiv.X86_64 (Stitch.nr Stitch.ciph Stitch.icb Stitch.bAddr Stitch.ctb Stitch.cR Stitch.dR Stitch.kR
  Stitch.cp Stitch.dp Stitch.kp)
open VG.Proof.AesGcmSiv.X86_64 (eval_ne eval_e eval_b)

/-! ## Arithmetic -/

theorem shr8shl4 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 4 = BitVec.ofNat 64 (16 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem shr8shl8 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 8 <<< 8 = BitVec.ofNat 64 (256 * (a / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem and255 (x : BitVec 64) : x &&& (BitVec.ofNat 32 255).signExtend 64 = BitVec.ofNat 64 (x.toNat % 256) := by
  rw [Proof.AesGcm.X86_64.imm_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 255) (by decide),
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem pad16_append {a b : List Byte} (ha : a.length % 16 = 0) :
    Spec.GcmSiv.pad16 (a ++ b) = a ++ Spec.GcmSiv.pad16 b := by
  simp only [Spec.GcmSiv.pad16, List.length_append, List.append_assoc]
  congr 3; omega_arith

/-! ## `Y` and `H`, to and from memory -/

/-- `putYH`: `Y` and `H` at `W + 80` and `W + 64`, in GHASH's order. -/
theorem putYH_ok (F : MulFacts) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) :
    WP isa (.block putYH) t fun t' =>
      blockAt t'.mem (W + BitVec.ofNat 64 80) = t.xmm .xmm2 ∧
      blockAt t'.mem (W + BitVec.ofNat 64 64) = hOf t.mem W ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := by
  have h15 := E.r15
  simp only [putYH, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 Impl.Gcm.X86_64.Pclmul.revMask t (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  have h15₁ : s₁.gpr .r15 = W := by rw [o₁.gpr _ (by decide)]; exact h15
  have w₁ : InRegions s₁.wr (W + BitVec.ofNat 64 80) 16 := by rw [o₁.wr]; exact E.perm.wW (by decide)
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ : ∃ s₂ : State, runBlock isa
      [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .r15 yO) .xmm2] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 80)
        (XBinOp.eval .pshufb (s₁.xmm .xmm2) Proof.Gcm.X86_64.revMask) ∧
      s₂.gpr = s₁.gpr ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [h15₁, w₁], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setXmm, xmm_setXmm_self, c₁]
      rfl
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    rw [g₂, o₁.gpr r (by rintro rfl; simp at hr)]) (rd₂.trans o₁.rd) (wr₂.trans o₁.wr)
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok7 (F := F) E₂) fun s₃ ⟨_, _, m₃, rd₃, wr₃, sv₃, x7₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 Impl.Gcm.X86_64.Pclmul.revMask s₃ (by decide)) fun s₄ ⟨c₄, o₄⟩ => ?_
  have h15₄ : s₄.gpr .r15 = W := by rw [o₄.gpr _ (by decide), sv₃ _ (by decide)]; exact E₂.r15
  have w₄ : InRegions s₄.wr (W + BitVec.ofNat 64 64) 16 := by
    rw [o₄.wr, wr₃]; exact E₂.perm.wW (by decide)
  obtain ⟨s₅, run₅, m₅, g₅, rd₅, wr₅⟩ : ∃ s₅ : State, runBlock isa
      [.xop (.bin .pshufb .xmm7 .xmm0), .movdquStore (at_ .r15 hO) .xmm7] s₄ = some s₅ ∧
      s₅.mem = s₄.mem.writeW (W + BitVec.ofNat 64 64)
        (XBinOp.eval .pshufb (s₄.xmm .xmm7) Proof.Gcm.X86_64.revMask) ∧
      s₅.gpr = s₄.gpr ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [h15₄, w₄], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setXmm, xmm_setXmm_self, c₄]
      rfl
    all_goals rfl
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have hw := L.ww
  have f₂ : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem s₂.mem := by
    rw [m₂, o₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  have f₅ : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem s₅.mem := by
    rw [m₅, o₄.mem, m₃]
    exact f₂.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  have hH : hOf s₂.mem W = hOf t.mem W := by
    show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₂.mem _ 16)) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₂ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
  refine ⟨?_, ?_, f₅, by rw [rd₅, o₄.rd, rd₃, rd₂, o₁.rd], by rw [wr₅, o₄.wr, wr₃, wr₂, o₁.wr], fun r hr => ?_⟩
  · rw [m₅, Proof.Gcm.X86_64.blockAt_eq, Mem.readW_writeW_sep
      (Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide), o₄.mem, m₃, m₂,
      ← Proof.Gcm.X86_64.blockAt_eq, Proof.Gcm.X86_64.blockAt_store, o₁.xmm _ (by decide)]
  · rw [m₅, Proof.Gcm.X86_64.blockAt_store, o₄.xmm _ (by decide), x7₃, hH]
  · have hne : r ≠ .rax := by rintro rfl; exact absurd hr (by decide)
    rw [g₅, o₄.gpr r hne, sv₃ r hr, g₂, o₁.gpr r hne]

/-- The rest of the data, after its 256-byte groups. -/
theorem restLoad_run {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa restLoad t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 256) ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.xmm = t.xmm ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain rD := E.perm.wR (show 232 + 8 ≤ 744 by decide)
  obtain rL := E.perm.wR (show 240 + 8 ≤ 744 by decide)
  have sD := S.data
  have sL := S.len
  obtain hand := and255 (BitVec.ofNat 64 n)
  rw [Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [restLoad, h15, rD, rL], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
      ite_false, reduceCtorEq, h15, sD, sL, shr8shl8 hn, dataO, lenO]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
      ite_false, reduceCtorEq, h15, sL, hand, lenO]
  · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

/-- `back`: GHASH's registers again, `Y` from `W + 80`, and the rest of the
data. -/
theorem back_ok (F : MulFacts) {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    WP isa (.block back) t fun t' =>
      GReg F (hOf t.mem W) t' ∧ t'.xmm .xmm2 = blockAt t.mem (W + BitVec.ofNat 64 80) ∧
      t'.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t'.gpr .rbp = BitVec.ofNat 64 (n % 256) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r := by
  simp only [back, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok (F := F) E) fun s₁ ⟨g₁, _, m₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP s₁ := E.of_saved sv₁ rd₁ wr₁
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 Impl.Gcm.X86_64.Pclmul.revMask s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  have h15₂ : s₂.gpr .r15 = W := by rw [o₂.gpr _ (by decide)]; exact E₁.r15
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 80) 16 := by
    rw [o₂.rd, o₂.wr]; exact E₁.perm.wR (by decide)
  obtain ⟨s₃, run₃, x2₃, x1₃, x3₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃ : State, runBlock isa
      [.movdquLoad .xmm2 (at_ .r15 yO), .xop (.bin .pshufb .xmm2 .xmm0)] s₂ = some s₃ ∧
      s₃.xmm .xmm2 = XBinOp.eval .pshufb (s₂.mem.readW (W + BitVec.ofNat 64 80) 128) Proof.Gcm.X86_64.revMask ∧
      s₃.xmm .xmm1 = s₂.xmm .xmm1 ∧ s₃.xmm .xmm3 = s₂.xmm .xmm3 ∧
      s₃.gpr = s₂.gpr ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [h15₂, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, ne_eq, reduceCtorEq, not_false_eq_true, c₂]
      rfl
    · simp only [xmm_setXmm_of_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [xmm_setXmm_of_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    all_goals rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have rd₃' : s₃.rd = t.rd := by rw [rd₃, o₂.rd, rd₁]
  have wr₃' : s₃.wr = t.wr := by rw [wr₃, o₂.wr, wr₁]
  have m₃' : s₃.mem = t.mem := by rw [m₃, o₂.mem, m₁]
  have E₃ : Env K W SP s₃ := E.keep (fun r hr => by
    rw [g₃, o₂.gpr r (by rintro rfl; simp at hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sv₁ _ (by decide)) rd₃' wr₃'
  obtain ⟨s₄, run₄, m₄, r12₄, rbp₄, g₄, x₄, rd₄, wr₄⟩ := restLoad_run E₃ (m₃' ▸ S) hn
  refine WP.of_runBlock ⟨s₄, run₄, ⟨?_, ?_⟩, ?_, r12₄, rbp₄, m₄.trans m₃', rd₄.trans rd₃', wr₄.trans wr₃', fun r hr => ?_⟩
  · rw [x₄, x1₃, o₂.xmm _ (by decide)]; exact g₁.c
  · rw [x₄, x3₃, o₂.xmm _ (by decide)]; exact g₁.h
  · rw [x₄, x2₃, o₂.mem, m₁, ← Proof.Gcm.X86_64.blockAt_eq]
  · have h := E₃.keep (s' := s₄) (fun r hr => g₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₄ wr₄
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.r13, E.r13]
    · rw [h.r15, E.r15]
    · rw [h.rsp, E.rsp]

/-! ## POLYVAL's loop -/

/-- `hash`'s pointers and count. -/
theorem hashPtrs_run {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa hashPtrs t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t₁.gpr .r8 = W + BitVec.ofNat 64 64 ∧
      t₁.gpr .r11 = W + BitVec.ofNat 64 488 ∧ t₁.gpr .rdx = D ∧
      t₁.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256)) ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain rD := E.perm.wR (show 232 + 8 ≤ 744 by decide)
  obtain rL := E.perm.wR (show 240 + 8 ≤ 744 by decide)
  have sD := S.data
  have sL := S.len
  obtain i80 := Proof.AesGcm.X86_64.imm_eq (show 80 < 2 ^ 31 by decide)
  obtain i64 := Proof.AesGcm.X86_64.imm_eq (show 64 < 2 ^ 31 by decide)
  obtain i488 := Proof.AesGcm.X86_64.imm_eq (show 488 < 2 ^ 31 by decide)
  refine ⟨_, by srun [hashPtrs, groups, pO, ptr, h15, rD, rL],
    by simp only [mem_setReg, mem_arithFlags, mem_setFlags], ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [rd_setReg, rd_arithFlags, rd_setFlags], by simp only [wr_setReg, wr_arithFlags, wr_setFlags]⟩
  iterate 4 simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
    ite_false, reduceCtorEq, h15, sD, i80, i64, i488]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
      ite_false, reduceCtorEq, h15, sL, shr8shl4 hn]
  · intro r hr
    obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := Proof.AesGcmSiv.X86_64.ne_of_calleeSaved hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]

/-- What `hash` needs, from its arguments. -/
theorem hpre_of {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {D : Addr} {n : Nat} (hD : Buf K W SP t D n) (h256 : 256 ≤ n)
    (hcx : t.gpr .rcx = W + BitVec.ofNat 64 80) (h8 : t.gpr .r8 = W + BitVec.ofNat 64 64)
    (h11 : t.gpr .r11 = W + BitVec.ofNat 64 488) (hdx : t.gpr .rdx = D)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))) : Stitch.HPre t := by
  have hn := hD.lt
  obtain hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [h9, toNat_ofNat_of_lt (by omega_arith)]
  constructor
  all_goals simp only [Stitch.xR, Stitch.yR, Stitch.pR, Stitch.xp, Stitch.yp, Stitch.hp, Stitch.pp, hnb, hdx, hcx, h8,
    h11]
  · omega_arith
  · omega_arith
  · exact E.perm.wR (by decide)
  · exact E.perm.wW (by decide)
  · simpa using Proof.AesGcm.X86_64.in_off (d := 0) (n := 16 * (16 * (n / 256))) hD.rd (by omega_arith) hn
  · exact E.perm.wW (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact ((hD.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))).symm
  · have := hD.wrap; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith

/-- The parts of `W` the loops and their arguments write, with the block
`absorb` and `crypt` pad at `W + 128`: `[64, 144)` and the powers. -/
abbrev lR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 64, 80⟩, ⟨W + BitVec.ofNat 64 488, 256⟩]

theorem slots_lR {K W SP : Addr} (L : Lay K W SP) :
    ∀ q ∈ lR W, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- The data's 256-byte groups absorbed by `hash`. -/
theorem hash_ok (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) {K W SP : Addr}
    (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (h256 : 256 ≤ n) :
    WP isa (.seq (.block hashArgs) (.seq lp.hash (.block back))) t fun t' =>
      Env K W SP t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ GReg F (hOf t.mem W) t' ∧
      t'.xmm .xmm2 = ghashFrom (hOf t.mem W) (t.xmm .xmm2) ((List.range (16 * (n / 256))).map (xel t.mem D)) ∧
      t'.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t'.gpr .rbp = BitVec.ofNat 64 (n % 256) ∧
      Frame (lR W) t.mem t'.mem := by
  have hn := hD.lt
  refine WP.seq ?_
  rw [show hashArgs = putYH ++ hashPtrs from rfl, WP.block_append_iff]
  refine WP.mono (putYH_ok F L E) fun s₁ ⟨y₁, h₁, f₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP s₁ := E.of_saved sv₁ rd₁ wr₁
  have f₁' : Frame (lR W) t.mem s₁.mem := f₁.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  have S₁ := S.of_frame f₁' (slots_lR L)
  obtain ⟨s₂, run₂, m₂, rcx₂, r8₂, r11₂, rdx₂, r9₂, sv₂, rd₂, wr₂⟩ := hashPtrs_run E₁ S₁ hn
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : Env K W SP s₂ := E₁.of_saved sv₂ rd₂ wr₂
  have rd₂' : s₂.rd = t.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = t.wr := wr₂.trans wr₁
  have hp₂ : Stitch.HPre s₂ := hpre_of L E₂ (hD.of_eq rd₂' wr₂') h256 rcx₂ r8₂ r11₂ rdx₂ r9₂
  obtain hnb : Stitch.nb s₂ = 16 * (n / 256) := by
    show (s₂.gpr .r9).toNat = _; rw [r9₂, toNat_ofNat_of_lt (by omega_arith)]
  refine WP.seq (WP.mono (hlp.hash hp₂) fun s₃ Hp => ?_)
  have E₃ : Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Hp.gpr _ (by decide) (by decide) (by decide)) Hp.rd Hp.wr
  have f₃ : Frame (lR W) s₁.mem s₃.mem := by
    have h := Hp.frame
    simp only [Stitch.yR, Stitch.pR, Stitch.yp, Stitch.pp, rcx₂, r11₂, m₂] at h
    exact h.sub fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have fT : Frame (lR W) t.mem s₃.mem := f₁'.trans f₃
  have S₃ := S.of_frame fT (slots_lR L)
  refine WP.mono (back_ok F E₃ S₃ hn) fun s₄ ⟨g₄, x2₄, r12₄, rbp₄, m₄, rd₄, wr₄, gp₄⟩ => ?_
  have hH₃ : hOf s₃.mem W = hOf t.mem W := by
    show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem _ 16)) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
  refine ⟨E₃.keep gp₄ rd₄ wr₄, by rw [rd₄, Hp.rd, rd₂'], by rw [wr₄, Hp.wr, wr₂'], hH₃ ▸ g₄, ?_, r12₄, rbp₄,
    m₄ ▸ fT⟩
  have h := Hp.y
  rw [show Stitch.yp s₂ = W + BitVec.ofNat 64 80 from rcx₂,
    show Stitch.hk s₂ = hOf t.mem W by
      show blockAt s₂.mem (s₂.gpr .r8) = _; rw [r8₂, m₂, h₁],
    show Stitch.y₀ s₂ = t.xmm .xmm2 by
      show blockAt s₂.mem (s₂.gpr .rcx) = _; rw [rcx₂, m₂, y₁], hnb] at h
  rw [x2₄, h]
  refine congrArg _ (List.map_congr_left fun k hk => ?_)
  simp only [List.mem_range] at hk
  show Spec.GcmSiv.ofBytes (bytesAt s₂.mem (s₂.gpr .rdx + _) 16) = _
  rw [rdx₂, m₂, Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact (hD.w.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub (by decide))) (by decide)]

/-- The data's length compared with 256. -/
theorem lenCmp_run {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa lenCmp t = some t₁ ∧ t₁.cf = some (decide (n < 256)) ∧
      (∀ r, r ≠ .rax → t₁.gpr r = t.gpr r) ∧ t₁.xmm = t.xmm ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain rL := E.perm.wR (show 240 + 8 ≤ 744 by decide)
  have sL := S.len
  have e : BitVec.signExtend 64 (BitVec.ofNat 32 256) = BitVec.ofNat 64 256 := by decide
  refine ⟨_, by srun [lenCmp, h15, rL], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, cf_setReg, gpr_setReg, mem_setReg, ite_true, h15, sL, lenO, e, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn]
  · intro r h₁; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, ite_false]
  all_goals rfl

/-! ## POLYVAL -/

/-- A pointer and a length from the slots at `W + o`, into `r12` and `rbp`. -/
theorem ld2_run {K W SP : Addr} {u : State} (Eu : Env K W SP u) {o : Nat} {P : Addr} {k : Nat} (h₁ : 200 ≤ o)
    (h₂ : o + 16 ≤ 248) (hP : u.mem.readW (W + BitVec.ofNat 64 o) 64 = P)
    (hk : u.mem.readW (W + BitVec.ofNat 64 (o + 8)) 64 = BitVec.ofNat 64 k) :
    ∃ u' : State, runBlock isa [.mov .r12 (.mem (at_ .r15 o)), .mov .rbp (.mem (at_ .r15 (o + 8)))] u = some u' ∧
      u'.gpr .r12 = P ∧ u'.gpr .rbp = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → u'.gpr r = u.gpr r) ∧
      u'.xmm = u.xmm ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have h15 := Eu.r15
  obtain r₁ := Eu.perm.wR (show o + 8 ≤ 744 by omega_arith)
  obtain r₂ := Eu.perm.wR (show o + 8 + 8 ≤ 744 by omega_arith)
  refine ⟨_, by srun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, hP]
  · simp only [gpr_setReg, mem_setReg, ite_true, ite_false, reduceCtorEq, h15, hk]
  · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
  all_goals rfl

/-- The elements of the data: those of its 256-byte groups' blocks, then the
rest's. -/
theorem elems_split (m : Mem) (D : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m D n)) =
      (List.range (16 * (n / 256))).map (xel m D) ++
        Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))) := by
  obtain hs : bytesAt m D n = bytesAt m D (256 * (n / 256)) ++
      bytesAt m (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) := by
    rw [← Proof.Cmac.bytesAt_add]; congr 1; omega_arith
  rw [hs, pad16_append (by simp [Proof.Cmac.bytesAt_length]; omega_arith),
    GcmSiv.elems_append (by simp [Proof.Cmac.bytesAt_length]; omega_arith),
    show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega_arith, GcmSiv.elems_bytesAt]

/-- What POLYVAL leaves, with the loop: as `PolyPost`, the loop's parts of
`W` written too. -/
structure PolyPostL (K W SP : Addr) (A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (lR W) t.mem t'.mem
  out : t'.xmm .xmm2 = ghashFrom (hOf t.mem W) 0
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n)) ++
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))])

theorem toL {W : Addr} {m m' : Mem} (h : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] m m') : Frame (lR W) m m' :=
  h.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩

/-- A buffer apart from `W` is apart from what the loops write. -/
theorem buf_lR {K W SP : Addr} {s : State} {P : Addr} {k : Nat} (hP : Buf K W SP s P k) :
    ∀ q ∈ lR W, (⟨P, k⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hP.w.sub_right (Lay.wSub (by decide))
  · exact hP.w.sub_right (Lay.wSub (by decide))

theorem hOf_lR {K W SP : Addr} (L : Lay K W SP) {m m' : Mem} (h : Frame (lR W) m m') : hOf m' W = hOf m W := by
  show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt m' _ 16)) = _
  rw [Proof.AesGcm.X86_64.bytesAt_frame h (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]

theorem polyvalL_ok (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp)
    {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n) :
    WP isa (polyvalL lp) t (PolyPostL K W SP A D al n t) := by
  have hw := L.ww
  have hn := hD.lt
  simp only [polyvalL]
  rw [show (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)) =
    hkey ++ ([.mov .r12 (.mem (at_ .r15 216)), .mov .rbp (.mem (at_ .r15 (216 + 8)))] : List Instr) from rfl,
    show ([.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] : List Instr) =
    [.mov .r12 (.mem (at_ .r15 232)), .mov .rbp (.mem (at_ .r15 (232 + 8)))] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok (F := F) E) fun t₁ ⟨g₁, y₁, m₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP t₁ := E.of_saved sv₁ rd₁ wr₁
  obtain ⟨t₂, run₂, r12₂, rbp₂, g₂, x₂, m₂, rd₂, wr₂⟩ := ld2_run (o := 216) (P := A) (k := al) E₁ (by decide)
    (by decide) (by rw [m₁]; exact S.aad) (by rw [m₁]; exact S.alen)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
  have mem₂ : t₂.mem = t.mem := m₂.trans m₁
  refine WP.seq (WP.mono (absorb_ok false L E₂ ⟨by rw [x₂]; exact g₁.c, by rw [x₂]; exact g₁.h⟩
    (hA.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) r12₂ rbp₂) fun t₃ P₃ => ?_)
  have fr₃ : Frame (lR W) t.mem t₃.mem := toL (mem₂ ▸ P₃.frame)
  have S₃ := S.of_frame fr₃ (slots_lR L)
  obtain ⟨t₄, run₄, r12₄, rbp₄, g₄, x₄, m₄, rd₄, wr₄⟩ := ld2_run (o := 232) (P := D) (k := n) P₃.env (by decide)
    (by decide) S₃.data S₃.len
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  have E₄ : Env K W SP t₄ := P₃.env.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₄ wr₄
  have rd₄' : t₄.rd = t.rd := by rw [rd₄, P₃.rd, rd₂, rd₁]
  have wr₄' : t₄.wr = t.wr := by rw [wr₄, P₃.wr, wr₂, wr₁]
  obtain ⟨t₅, run₅, cf₅, g₅, x₅, m₅, rd₅, wr₅⟩ := lenCmp_run E₄ (m₄ ▸ S₃) hn
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  have E₅ : Env K W SP t₅ := E₄.keep (fun r hr => g₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₅ wr₅
  have rd₅' : t₅.rd = t.rd := rd₅.trans rd₄'
  have wr₅' : t₅.wr = t.wr := wr₅.trans wr₄'
  have m₅' : t₅.mem = t₃.mem := m₅.trans m₄
  have G₅ : GReg F (hOf t.mem W) t₅ := ⟨by rw [x₅, x₄]; exact P₃.g.c, by rw [x₅, x₄]; exact P₃.g.h⟩
  have xD : ∀ k, k < 16 * (n / 256) → xel t₃.mem D k = xel t.mem D k := fun k hk => by
    show Spec.GcmSiv.ofBytes (bytesAt t₃.mem _ 16) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fr₃ (fun q hq => (buf_lR hD q hq).sub_left
      (Offset.sub_base _ (by omega_arith))) (by decide)]
  -- The groups, if any.
  have mid : WP isa (.ite .b (.block []) (.seq (.block hashArgs) (.seq lp.hash (.block back)))) t₅ fun u =>
      Env K W SP u ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ GReg F (hOf t.mem W) u ∧
      u.xmm .xmm2 = ghashFrom (hOf t.mem W) (t₃.xmm .xmm2) ((List.range (16 * (n / 256))).map (xel t.mem D)) ∧
      u.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ u.gpr .rbp = BitVec.ofNat 64 (n % 256) ∧
      Frame (lR W) t.mem u.mem := by
    refine WP.ite (decide (n < 256)) (eval_b cf₅) (fun h => WP.block_nil ?_) (fun h => ?_)
    · have h' : n < 256 := by simpa using h
      have e0 : n / 256 = 0 := Nat.div_eq_of_lt h'
      refine ⟨E₅, rd₅', wr₅', G₅, ?_, ?_, ?_, m₅' ▸ fr₃⟩
      · rw [e0, x₅, x₄]; rfl
      · rw [e0, g₅ _ (by decide), r12₄]; simp
      · rw [Nat.mod_eq_of_lt h', g₅ _ (by decide), rbp₄]
    · have h' : 256 ≤ n := by simpa using h
      have hH₅ : hOf t₅.mem W = hOf t.mem W := by rw [m₅']; exact hOf_lR L fr₃
      refine WP.mono (hash_ok F hlp L E₅ (m₅' ▸ S₃) (hD.of_eq rd₅' wr₅') h') fun u ⟨Eu, rdu, wru, gu, yu, r12u, rbpu, fu⟩ => ?_
      refine ⟨Eu, rdu.trans rd₅', wru.trans wr₅', hH₅ ▸ gu, ?_, r12u, rbpu, fr₃.trans (m₅' ▸ fu)⟩
      rw [yu, hH₅, x₅, x₄, m₅']
      exact congrArg _ (List.map_congr_left fun k hk => xD k (List.mem_range.mp hk))
  refine WP.seq (WP.mono mid fun u ⟨Eu, rdu, wru, gu, yu, r12u, rbpu, fu⟩ => ?_)
  have Su := S.of_frame fu (slots_lR L)
  refine WP.seq (WP.mono (absorb_ok true L Eu gu
    ((hD.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)).of_eq rdu wru) r12u rbpu) fun t₆ P₆ => ?_)
  have fr₆ : Frame (lR W) t.mem t₆.mem := fu.trans (toL P₆.frame)
  have S₆ := S.of_frame fr₆ (slots_lR L)
  refine WP.mono (lens_ok P₆.env P₆.g (al := al) (n := n) S₆.alen S₆.len hA.lt hD.lt)
    fun t₇ ⟨y₇, m₇, rd₇, wr₇, g₇⟩ => ?_
  have eR : bytesAt u.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) =
      bytesAt t.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) :=
    Proof.AesGcm.X86_64.bytesAt_frame fu (fun q hq => (buf_lR hD q hq).sub_left
      (Offset.sub_base _ (by omega_arith))) (by omega_arith)
  refine ⟨P₆.env.keep g₇ rd₇ wr₇, by rw [rd₇, P₆.rd, rdu], by rw [wr₇, P₆.wr, wru], m₇ ▸ fr₆, ?_⟩
  rw [y₇, P₆.y, yu, P₃.y, x₂, y₁, eR, mem₂, elems_split t.mem D n, ← ghashFrom_snoc, ← Proof.Gcm.ghashFrom_append,
    ← Proof.Gcm.ghashFrom_append]
  simp only [List.append_assoc]

/-! ## Counter mode's loop -/

theorem le16_inj {v w : BitVec 128} (h : le16 v = le16 w) : v = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun l : List Byte => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  have h16 : i / 8 < 16 := by omega_arith
  have h8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have e : 8 * (i / 8) + i % 8 = i := by omega_arith
  simpa [le16, h16, h8, e] using hb

/-- The loops' count, counter block and pointers. -/
theorem ctrPtrs_run {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa ctrPtrs t = some t₁ ∧
      t₁.mem = t.mem.writeW (W + BitVec.ofNat 64 96) (t.xmm .xmm9) ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 96 ∧ t₁.gpr .rcx = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 64 ∧ t₁.gpr .r11 = W + BitVec.ofNat 64 488 ∧
      t₁.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256)) ∧
      (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → r ≠ .r9 → t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain rL := E.perm.wR (show 240 + 8 ≤ 744 by decide)
  obtain wC := E.perm.wW (show 96 + 16 ≤ 744 by decide)
  have sL := S.len
  obtain i96 := Proof.AesGcm.X86_64.imm_eq (show 96 < 2 ^ 31 by decide)
  obtain i80 := Proof.AesGcm.X86_64.imm_eq (show 80 < 2 ^ 31 by decide)
  obtain i64 := Proof.AesGcm.X86_64.imm_eq (show 64 < 2 ^ 31 by decide)
  obtain i488 := Proof.AesGcm.X86_64.imm_eq (show 488 < 2 ^ 31 by decide)
  refine ⟨_, by xrun [ctrPtrs, groups, pO, ptr, h15, rL, wC], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, xmm_setReg, xmm_arithFlags, xmm_setFlags, gpr_setReg,
      gpr_arithFlags, gpr_setFlags, ite_false, reduceCtorEq, h15]
  iterate 4 simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
    ite_false, reduceCtorEq, h15, i96, i80, i64, i488]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, ite_true,
      ite_false, reduceCtorEq, h15, sL, shr8shl4 hn]
  · intro r n₁ n₂ n₃ n₄ n₅
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, n₁, n₂, n₃, n₄, n₅, ite_false]
  all_goals rfl

/-- What `ctr` and `dec` need, from their arguments. -/
theorem spre_of {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {D : Addr} {n : Nat} (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 248) (hsi : t.gpr .rsi = BitVec.ofNat 64 R)
    (hdx : t.gpr .rdx = W + BitVec.ofNat 64 96) (hcx : t.gpr .rcx = W + BitVec.ofNat 64 80)
    (h8 : t.gpr .r8 = W + BitVec.ofNat 64 64) (h11 : t.gpr .r11 = W + BitVec.ofNat 64 488) (h12 : t.gpr .r12 = D)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))) : Stitch.SPre t := by
  have hn := hD.lt
  obtain hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [h9, toNat_ofNat_of_lt (by omega_arith)]
  obtain hnr : Stitch.nr t = R := by
    show (t.gpr .rsi).toNat = _; rw [hsi, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  obtain hpD : ∀ {d k : Nat}, d + k ≤ 744 →
      (⟨D, 16 * (16 * (n / 256))⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => (hD.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub h)
  constructor
  all_goals simp only [Stitch.dR, Stitch.kR, Stitch.cR, Stitch.yR, Stitch.pR, Stitch.dp, Stitch.kp, Stitch.cp,
    Stitch.yp, Stitch.hp, Stitch.pp, hnb, hnr, h12, hdi, hdx, hcx, h8, h11]
  · rcases hR with h | h <;> simp [h]
  · omega_arith
  · exact E.perm.wR (by decide)
  · exact E.perm.wR (by decide)
  · exact E.perm.wW (by decide)
  · exact E.perm.wW (by decide)
  · simpa using Proof.AesGcm.X86_64.in_off (d := 0) (n := 16 * (16 * (n / 256))) hDw (by omega_arith) hn
  · exact E.perm.wW (by decide)
  · exact hpD (d := 248) (k := 240) (by decide)
  · exact hpD (d := 96) (k := 16) (by decide)
  · exact hpD (d := 80) (k := 16) (by decide)
  · exact hpD (d := 488) (k := 256) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · have := hD.wrap; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith

/-- The counter block from `W + 96`, its increment and `aes`'s arguments. -/
theorem ctrLoad_run {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) :
    ∃ t₁ : State, runBlock isa ctrLoad t = some t₁ ∧
      t₁.xmm .xmm9 = t.mem.readW (W + BitVec.ofNat 64 96) 128 ∧
      t₁.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .r10 = W + BitVec.ofNat 64 248 + BitVec.ofNat 64 (16 * R) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 744 by decide)
  have rC := E.perm.wR (show 96 + 16 ≤ 744 by decide)
  refine ⟨_, by xrun [ctrLoad, aesArgs, lastKey, skO, roundsO, cmO, h15, rR, rr, rC], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      mem_setReg, mem_arithFlags, mem_setXmm, mem_setFlags, h15, cmO, ne_eq, not_false_eq_true]
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags,
      xmm_setFlags, gpr_setXmm, gpr_setReg, ite_true, ite_false, reduceCtorEq, ne_eq, not_false_eq_true]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, skO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO, skO, execShift]
    rw [BitVec.add_comm]; congr 1; rcases hR with rfl | rfl <;> decide
  · rfl
  · rfl
  · rfl
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]

/-- `split16`: the whole blocks and the last bytes of `m` bytes. -/
theorem split16_run {t : State} {m : Nat} (hm : m < 2 ^ 64) (hbp : t.gpr .rbp = BitVec.ofNat 64 m) :
    ∃ t₁ : State, runBlock isa split16 t = some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (m / 16) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (m % 16) ∧
      t₁.zf = some (decide (m / 16 = 0)) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.xmm = t.xmm ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  obtain hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 m)
  rw [toNat_ofNat_of_lt hm, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [split16], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
      Proof.AesGcm.X86_64.shr4 _ hm]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp, hand]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hm]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
  · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
  all_goals rfl

/-- `ctrBack`: counter mode's registers, for the rest of the data. -/
theorem ctrBack_run {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa ctrBack t = some t₁ ∧
      t₁.xmm .xmm9 = t.mem.readW (W + BitVec.ofNat 64 96) 128 ∧
      t₁.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .r10 = W + BitVec.ofNat 64 248 + BitVec.ofNat 64 (16 * R) ∧
      t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 256 % 16) ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (n % 256 / 16) ∧ t₁.zf = some (decide (n % 256 / 16 = 0)) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r := by
  obtain ⟨a, runa, x9, x10, rdi, rsi, r10, ma, rda, wra, ga⟩ := ctrLoad_run hR E S
  have Ea : Env K W SP a := E.keep ga rda wra
  obtain ⟨b, runb, mb, r12, rbp, gb, xb, rdb, wrb⟩ := restLoad_run Ea (ma ▸ S) hn
  obtain ⟨c, runc, rbx, rbp', zf, gc, xc, mc, rdc, wrc⟩ := split16_run (m := n % 256) (by omega_arith) rbp
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rbp', rbx, zf, by rw [mc, mb, ma], by rw [rdc, rdb, rda],
    by rw [wrc, wrb, wra], fun r hr => ?_⟩
  · rw [ctrBack, VG.Interleave.runBlock_append, runa, Option.bind_some, VG.Interleave.runBlock_append, runb,
      Option.bind_some, runc]
  · rw [xc, xb, x9]
  · rw [xc, xb, x10]
  · rw [gc _ (by decide) (by decide), gb _ (by decide) (by decide) (by decide), rdi]
  · rw [gc _ (by decide) (by decide), gb _ (by decide) (by decide) (by decide), rsi]
  · rw [gc _ (by decide) (by decide), gb _ (by decide) (by decide) (by decide), r10]
  · rw [gc _ (by decide) (by decide), r12]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [gc _ (by decide) (by decide), gb _ (by decide) (by decide) (by decide), ga _ (by simp)]

/-- After a loop on the groups: the rest of the data in counter mode. -/
theorem afterLoop_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {s : State}
    (E : Env K W SP s) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n s.mem) (hD : Buf K W SP s D n)
    (hDw : Covers [⟨D, n⟩] s.wr) {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128}
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4)
    (hc : bytesAt s.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb (16 * (n / 256)))
    (hx : bytesAt s.mem D n =
      GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph s.mem (W + BitVec.ofNat 64 248) R) icb x (16 * (16 * (n / 256)))) :
    WP isa (.seq (.block ctrBack) cryptRest) s fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨D, n⟩] s.mem t'.mem ∧
      bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph s.mem (W + BitVec.ofNat 64 248) R) icb x := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, x9, x10, rdi, rsi, r10, r12, rbp, rbx, zf, m₁, rd₁, wr₁, g₁⟩ := ctrBack_run hR E S hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have e9 : t₁.xmm .xmm9 = ctrX icb d (16 * (n / 256)) :=
    le16_inj (by rw [x9, le16_readW, hc, le16_ctrX hrest])
  have I : CInv K W SP R D n (Spec.GcmSiv.ctxCiph s.mem (W + BitVec.ofNat 64 248) R) icb x d s
      (16 * (n / 256)) t₁ :=
    ⟨E.keep g₁ rd₁ wr₁, rd₁, wr₁, rdi, rsi, r10, by rw [m₁], e9, x10,
      by rw [r12, show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega_arith],
      by rw [rbx, show n % 256 / 16 = n / 16 - 16 * (n / 256) by omega_arith],
      by rw [rbp, show n % 256 % 16 = n % 16 by omega_arith], by rw [m₁]; exact hx,
      by rw [m₁]; exact Frame.refl _ _⟩
  exact cryptRest_ok L hR hxl hD hDw hrest (fun y => GcmSiv.ctxCiph_length _ _ _ _) (by omega_arith) I
    (by rw [zf, show n % 256 / 16 = n / 16 - 16 * (n / 256) by omega_arith])

/-- What counter mode leaves, with the loop: as `CryptPost`, the loop's
parts of `W` written too. -/
structure CryptPostL (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (lR W ++ [⟨D, n⟩]) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)

/-- The encryption key's schedule is apart from what the loops and counter
mode write. -/
theorem key_lR {K W SP : Addr} (L : Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : Buf K W SP s D n) :
    ∀ q ∈ lR W ++ [⟨D, n⟩], (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

theorem slots_lRD {K W SP : Addr} (L : Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : Buf K W SP s D n) :
    ∀ q ∈ lR W ++ [⟨D, n⟩], (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

/-- The data's 256-byte groups in counter mode by `ctr`, and the rest. -/
theorem ctrLoop_ok {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) {K W SP : Addr}
    (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n) :
    WP isa (.seq (.block ctrArgs) (.seq lp.ctr (.seq (.block ctrBack) cryptRest))) t
      (CryptPostL K W SP R D n t) := by
  have hn := hD.lt
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    fun y => GcmSiv.ctxCiph_length _ _ _ _
  obtain ⟨t₁, run₁, h9, _, rdi₁, rsi₁, _, r12₁, _, _, _, m₁, rd₁, wr₁, g₁⟩ := ctrInit_run hR E S hn
  obtain ⟨hrest, _⟩ := ctr_of_le16 h9
  have E₁ : Env K W SP t₁ := E.keep g₁ rd₁ wr₁
  obtain ⟨t₂, run₂, m₂, rdx₂, rcx₂, r8₂, r11₂, r9₂, g₂, rd₂, wr₂⟩ := ctrPtrs_run E₁ (m₁ ▸ S) hn
  refine WP.seq ?_
  rw [show ctrArgs = ctrInit ++ ctrPtrs from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, WP.of_runBlock ⟨t₂, run₂, ?_⟩⟩
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  have rd₂' : t₂.rd = t.rd := rd₂.trans rd₁
  have wr₂' : t₂.wr = t.wr := wr₂.trans wr₁
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t₂.mem := by
    rw [m₂, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have F₂ : Frame (lR W ++ [⟨D, n⟩]) t.mem t₂.mem := f₂.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  have hicb : bytesAt t₂.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [m₂, bytesAt_writeW128, h9]
  have x₂ : bytesAt t₂.mem D n = bytesAt t.mem D n :=
    Proof.AesGcm.X86_64.bytesAt_frame f₂ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide)))
      (Nat.le_of_lt hn)
  have rdi₂ : t₂.gpr .rdi = W + BitVec.ofNat 64 248 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), rdi₁]
  have rsi₂ : t₂.gpr .rsi = BitVec.ofNat 64 R := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsi₁]
  have r12₂ : t₂.gpr .r12 = D := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), r12₁]
  have hp₂ : Stitch.SPre t₂ := spre_of L hR E₂ (hD.of_eq rd₂' wr₂') (by rw [wr₂']; exact hDw) h256 rdi₂ rsi₂ rdx₂
    rcx₂ r8₂ r11₂ r12₂ r9₂
  obtain hnb : Stitch.nb t₂ = 16 * (n / 256) := by
    show (t₂.gpr .r9).toNat = _; rw [r9₂, toNat_ofNat_of_lt (by omega_arith)]
  refine WP.seq (WP.mono (hlp.ctr hp₂ (by rw [hnb]; omega_arith)) fun t₃ Cp => ?_)
  obtain hnr : Stitch.nr t₂ = R := by
    show (t₂.gpr .rsi).toNat = _; rw [rsi₂, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  obtain hci : Stitch.ciph t₂ = Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
    show Spec.GcmSiv.aesWith (Stitch.nr t₂) (bytesAt t₂.mem (t₂.gpr .rdi) (16 * (Stitch.nr t₂ + 1))) = _
    rw [hnr, rdi₂]
    exact ctxCiph_frame F₂ (key_lR L hD) hRb
  obtain hicb₂ : Stitch.icb t₂ = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    show bytesAt t₂.mem (t₂.gpr .rdx) 16 = _; rw [rdx₂, hicb]
  obtain hbA : ∀ k, Stitch.bAddr t₂ k = D + BitVec.ofNat 64 (16 * k) := fun k => by
    show t₂.gpr .r12 + _ = _; rw [r12₂]
  obtain hctb : ∀ k, Stitch.ctb t₂ k = Spec.Cmac.xor (bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * k)) 16)
      (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R
        (Spec.GcmSiv.counterBlock (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) k)) := fun k => by
    show Spec.Cmac.xor (bytesAt t₂.mem (Stitch.bAddr t₂ k) 16) (Stitch.ciph t₂ _) = _
    rw [hbA, hci, hicb₂]
  obtain Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 488, 256⟩] t₂.mem t₃.mem := by
    have h := Cp.frame
    simp only [Stitch.cR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.dp, Stitch.pp, hnb, rdx₂, r12₂, r11₂] at h
    exact h
  obtain F₃ : Frame (lR W ++ [⟨D, n⟩]) t.mem t₃.mem := F₂.trans (Fd.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 488, 256⟩, by simp, fun _ h => h⟩)
  obtain hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  obtain hx₃ : bytesAt t₃.mem D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (16 * (16 * (n / 256))) := by
    obtain h := GcmSiv.ctrPart_stepN (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (m := t₂.mem) (m' := t₃.mem) D
      (i := 0) (k := 16 * (n / 256)) (fun l _ => hcl _)
      (by rw [hxl, x₂, Nat.mul_zero, GcmSiv.ctrPart_zero])
      (fun p hp ho => frame_outside Fd (P := D) (len := n) (a := 0) (n := 16 * (16 * (n / 256))) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inl (by rw [BitVec.add_zero])
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))) hn (by omega_arith) p (by rw [hxl] at hp; exact hp)
        (by omega_arith))
      (fun l hl => by
        obtain h := Cp.data l (by rw [hnb]; exact hl)
        rw [hbA, hctb] at h
        simpa only [Nat.zero_add] using h)
    rwa [hxl, Nat.zero_add] at h
  obtain E₃ : Env K W SP t₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Cp.gpr _ (by decide) (by decide) (by decide) (by decide)) Cp.rd Cp.wr
  obtain S₃ := S.of_frame F₃ (slots_lRD L hD)
  obtain rd₃ : t₃.rd = t.rd := by rw [Cp.rd, rd₂']
  obtain wr₃ : t₃.wr = t.wr := by rw [Cp.wr, wr₂']
  obtain hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame F₃ (key_lR L hD) hRb
  refine WP.mono (afterLoop_ok L hR E₃ S₃ (hD.of_eq rd₃ wr₃) (by rw [wr₃]; exact hDw) hxl hrest
    (by have h := Cp.ctr
        rw [show Stitch.cp t₂ = W + BitVec.ofNat 64 96 from rdx₂, hicb₂, hnb] at h
        exact h)
    (by rw [hc₃]; exact hx₃)) fun t' ⟨E', rd', wr', f', d'⟩ => ?_
  refine ⟨E', rd'.trans rd₃, wr'.trans wr₃, F₃.trans (f'.sub fun r hr => ?_), by rw [d', hc₃]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩

/-- Counter mode, with the loop from 256 bytes. -/
theorem cryptL_ok {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) {K W SP : Addr}
    (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) :
    WP isa (cryptL lp) t (CryptPostL K W SP R D n t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, cf₁, g₁, x₁, m₁, rd₁, wr₁⟩ := lenCmp_run E S hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
  refine WP.ite (decide (n < 256)) (eval_b cf₁) (fun _ => ?_) (fun h => ?_)
  · refine WP.mono (crypt_ok L hR E₁ (m₁ ▸ S) (hD.of_eq rd₁ wr₁) (by rw [wr₁]; exact hDw)) fun t' P => ?_
    refine ⟨P.env, P.rd.trans rd₁, P.wr.trans wr₁, m₁ ▸ (P.frame.sub fun r hr => ?_), by rw [P.data, m₁]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  · have h' : 256 ≤ n := by simpa using h
    refine WP.mono (ctrLoop_ok hlp L hR E₁ (m₁ ▸ S) (hD.of_eq rd₁ wr₁) (by rw [wr₁]; exact hDw) h') fun t' P => ?_
    exact ⟨P.env, P.rd.trans rd₁, P.wr.trans wr₁, m₁ ▸ P.frame, by rw [P.data, m₁]⟩

/-! ## `open`: counter mode and POLYVAL of the plaintext -/

/-- What `open` leaves of the data: it deciphered, in counter mode from the
tag at `W`, and POLYVAL of the additional data, the plaintext and the
lengths. -/
structure DecPost (K W SP : Addr) (R : Nat) (A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (lR W ++ [⟨D, n⟩]) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)
  out : t'.xmm .xmm2 = ghashFrom (hOf t.mem W) 0
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t'.mem D n)) ++
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))])

theorem bytesAt_ext {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- Counter mode on more of the data keeps what it had enciphered. -/
theorem prefix_keep {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} {m m' : Mem} {D : Addr} {n k : Nat}
    (hxl : x.length = n) (hk : k ≤ n) (h : bytesAt m D n = GcmSiv.ctrPart ciph icb x k)
    (h' : bytesAt m' D n = GcmSiv.ctrPart ciph icb x n) :
    ∀ p < k, m' (D + BitVec.ofNat 64 p) = m (D + BitVec.ofNat 64 p) := by
  intro p hp
  have hpn : p < n := by omega_arith
  rw [← Proof.Cmac.getD_bytesAt m' D hpn, ← Proof.Cmac.getD_bytesAt m D hpn, h, h',
    GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; exact hpn), GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; exact hpn)]
  simp only [hp, hpn, ↓reduceIte]

/-- With less than 256 bytes of data: counter mode, then POLYVAL. -/
theorem decS_ok (F : MulFacts) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al)
    (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (.seq crypt polyval) t (DecPost K W SP R A D al n t) := by
  refine WP.seq (WP.mono (crypt_ok L hR E S hD hDw) fun t₁ Cr => ?_)
  have f₁ : Frame (lR W ++ [⟨D, n⟩]) t.mem t₁.mem := Cr.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
  have S₁ := S.of_frame f₁ (slots_lRD L hD)
  refine WP.mono (polyval_ok F L Cr.env S₁ (hA.of_eq Cr.rd Cr.wr) (hD.of_eq Cr.rd Cr.wr)) fun t₂ Po => ?_
  have eD : bytesAt t₂.mem D n = bytesAt t₁.mem D n :=
    Proof.AesGcm.X86_64.bytesAt_frame Po.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide)))
      (Nat.le_of_lt hD.lt)
  have eA : bytesAt t₁.mem A al = bytesAt t.mem A al :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hA.w.sub_right (Lay.wSub (by decide))
      · exact hAD) (Nat.le_of_lt hA.lt)
  have eH : hOf t₁.mem W = hOf t.mem W := by
    show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t₁.mem _ 16)) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide)]
  refine ⟨Po.env, Po.rd.trans Cr.rd, Po.wr.trans Cr.wr, f₁.trans ((toL Po.frame).sub fun r hr =>
    ⟨r, List.mem_append_left _ hr, fun _ h => h⟩), by rw [eD, Cr.data], ?_⟩
  rw [Po.out, eH, eA, eD]

/-- With 256 bytes of data or more: the groups deciphered and absorbed by
`dec`, then the rest. -/
theorem decL_ok (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) {K W SP : Addr}
    (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n) :
    WP isa (decL lp) t (DecPost K W SP R A D al n t) := by
  have hn := hD.lt
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    fun y => GcmSiv.ctxCiph_length _ _ _ _
  simp only [decL]
  rw [show (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)) =
    hkey ++ ([.mov .r12 (.mem (at_ .r15 216)), .mov .rbp (.mem (at_ .r15 (216 + 8)))] : List Instr) from rfl]
  -- The additional data.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok (F := F) E) fun t₁ ⟨g₁, y₁, m₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP t₁ := E.of_saved sv₁ rd₁ wr₁
  obtain ⟨t₂, run₂, r12₂, rbp₂, g₂, x₂, m₂, rd₂, wr₂⟩ := ld2_run (o := 216) (P := A) (k := al) E₁ (by decide)
    (by decide) (by rw [m₁]; exact S.aad) (by rw [m₁]; exact S.alen)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
  have mem₂ : t₂.mem = t.mem := m₂.trans m₁
  refine WP.seq (WP.mono (absorb_ok false L E₂ ⟨by rw [x₂]; exact g₁.c, by rw [x₂]; exact g₁.h⟩
    (hA.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) r12₂ rbp₂) fun t₃ P₃ => ?_)
  have fr₃ : Frame (lR W) t.mem t₃.mem := toL (mem₂ ▸ P₃.frame)
  have rd₃ : t₃.rd = t.rd := by rw [P₃.rd, rd₂, rd₁]
  have wr₃ : t₃.wr = t.wr := by rw [P₃.wr, wr₂, wr₁]
  have Y₃ : t₃.xmm .xmm2 = ghashFrom (hOf t.mem W) 0 (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al))) := by
    rw [P₃.y, x₂, y₁, mem₂]
  -- `Y`, `H`, the counter block and the loop's arguments.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (putYH_ok F L P₃.env) fun s₄ ⟨y₄, h₄, f₄, rd₄, wr₄, sv₄⟩ => ?_
  have E₄ : Env K W SP s₄ := P₃.env.of_saved sv₄ rd₄ wr₄
  have fr₄ : Frame (lR W) t.mem s₄.mem := fr₃.trans (f₄.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩)
  have S₄ := S.of_frame fr₄ (slots_lR L)
  have tag₄ : bytesAt s₄.mem W 16 = bytesAt t.mem W 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame fr₄ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)) (by decide)
  obtain ⟨s₅, run₅, h9, _, rdi₅, rsi₅, _, r12₅, _, _, _, m₅, rd₅, wr₅, g₅⟩ := ctrInit_run hR E₄ S₄ hn
  rw [tag₄] at h9
  obtain ⟨hrest, _⟩ := ctr_of_le16 h9
  have E₅ : Env K W SP s₅ := E₄.keep g₅ rd₅ wr₅
  obtain ⟨s₆, run₆, m₆, rdx₆, rcx₆, r8₆, r11₆, r9₆, g₆, rd₆, wr₆⟩ := ctrPtrs_run E₅ (m₅ ▸ S₄) hn
  rw [show ctrArgs = ctrInit ++ ctrPtrs from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₅, run₅, WP.of_runBlock ⟨s₆, run₆, ?_⟩⟩
  have E₆ : Env K W SP s₆ := E₅.keep (fun r hr => g₆ r
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₆ wr₆
  have rd₆' : s₆.rd = t.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = t.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have f₆ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₆ : Frame (lR W) t.mem s₆.mem := fr₄.trans (f₆.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩)
  have F₆ : Frame (lR W ++ [⟨D, n⟩]) t.mem s₆.mem :=
    fr₆.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  have hicb : bytesAt s₆.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [m₆, bytesAt_writeW128, h9]
  have x₆ : bytesAt s₆.mem D n = bytesAt t.mem D n :=
    Proof.AesGcm.X86_64.bytesAt_frame fr₆ (buf_lR hD) (Nat.le_of_lt hn)
  have yy₆ : blockAt s₆.mem (W + BitVec.ofNat 64 80) = t₃.xmm .xmm2 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.w_w (.inl (by decide)) (by decide) (by decide)), y₄]
  have hh₆ : blockAt s₆.mem (W + BitVec.ofNat 64 64) = hOf t.mem W := by
    rw [Proof.AesGcm.X86_64.blockAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.w_w (.inl (by decide)) (by decide) (by decide)), h₄, hOf_lR L fr₃]
  have rdi₆ : s₆.gpr .rdi = W + BitVec.ofNat 64 248 := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), rdi₅]
  have rsi₆ : s₆.gpr .rsi = BitVec.ofNat 64 R := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsi₅]
  have r12₆ : s₆.gpr .r12 = D := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), r12₅]
  have hp₆ : Stitch.SPre s₆ := spre_of L hR E₆ (hD.of_eq rd₆' wr₆') (by rw [wr₆']; exact hDw) h256 rdi₆ rsi₆ rdx₆
    rcx₆ r8₆ r11₆ r12₆ r9₆
  obtain hnb : Stitch.nb s₆ = 16 * (n / 256) := by
    show (s₆.gpr .r9).toNat = _; rw [r9₆, toNat_ofNat_of_lt (by omega_arith)]
  -- The groups.
  refine WP.seq (WP.mono (hlp.dec hp₆ (by rw [hnb]; omega_arith)) fun s₇ Dp => ?_)
  obtain hnr : Stitch.nr s₆ = R := by
    show (s₆.gpr .rsi).toNat = _; rw [rsi₆, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  obtain hci : Stitch.ciph s₆ = Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
    show Spec.GcmSiv.aesWith (Stitch.nr s₆) (bytesAt s₆.mem (s₆.gpr .rdi) (16 * (Stitch.nr s₆ + 1))) = _
    rw [hnr, rdi₆]
    exact ctxCiph_frame F₆ (key_lR L hD) hRb
  obtain hicb₆ : Stitch.icb s₆ = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    show bytesAt s₆.mem (s₆.gpr .rdx) 16 = _; rw [rdx₆, hicb]
  obtain hbA : ∀ k, Stitch.bAddr s₆ k = D + BitVec.ofNat 64 (16 * k) := fun k => by
    show s₆.gpr .r12 + _ = _; rw [r12₆]
  obtain hctb : ∀ k, Stitch.ctb s₆ k = Spec.Cmac.xor (bytesAt s₆.mem (D + BitVec.ofNat 64 (16 * k)) 16)
      (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R
        (Spec.GcmSiv.counterBlock (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) k)) := fun k => by
    show Spec.Cmac.xor (bytesAt s₆.mem (Stitch.bAddr s₆ k) 16) (Stitch.ciph s₆ _) = _
    rw [hbA, hci, hicb₆]
  obtain Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 488, 256⟩] s₆.mem s₇.mem := by
    have h := Dp.frame
    simp only [Stitch.cR, Stitch.yR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.yp, Stitch.dp, Stitch.pp, hnb, rdx₆,
      rcx₆, r12₆, r11₆] at h
    exact h
  obtain F₇ : Frame (lR W ++ [⟨D, n⟩]) t.mem s₇.mem := F₆.trans (Fd.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 488, 256⟩, by simp, fun _ h => h⟩)
  obtain hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  obtain hx₇ : bytesAt s₇.mem D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (16 * (16 * (n / 256))) := by
    obtain h := GcmSiv.ctrPart_stepN (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (m := s₆.mem) (m' := s₇.mem) D
      (i := 0) (k := 16 * (n / 256)) (fun l _ => hcl _)
      (by rw [hxl, x₆, Nat.mul_zero, GcmSiv.ctrPart_zero])
      (fun p hp ho => frame_outside Fd (P := D) (len := n) (a := 0) (n := 16 * (16 * (n / 256))) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inl (by rw [BitVec.add_zero])
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))) hn (by omega_arith) p (by rw [hxl] at hp; exact hp)
        (by omega_arith))
      (fun l hl => by
        obtain h := Dp.data l (by rw [hnb]; exact hl)
        rw [hbA, hctb] at h
        simpa only [Nat.zero_add] using h)
    rwa [hxl, Nat.zero_add] at h
  obtain Y₇ : blockAt s₇.mem (W + BitVec.ofNat 64 80) =
      ghashFrom (hOf t.mem W) (t₃.xmm .xmm2) ((List.range (16 * (n / 256))).map (xel s₇.mem D)) := by
    have h := Dp.y
    rw [show Stitch.yp s₆ = W + BitVec.ofNat 64 80 from rcx₆,
      show Stitch.hk s₆ = hOf t.mem W by show blockAt s₆.mem (s₆.gpr .r8) = _; rw [r8₆, hh₆],
      show Stitch.y₀ s₆ = t₃.xmm .xmm2 by show blockAt s₆.mem (s₆.gpr .rcx) = _; rw [rcx₆, yy₆], hnb] at h
    rw [h]
    refine congrArg _ (List.map_congr_left fun k hk => ?_)
    simp only [List.mem_range] at hk
    have hd := Dp.data k (by rw [hnb]; exact hk)
    rw [hbA] at hd
    show _ = Spec.GcmSiv.ofBytes (bytesAt s₇.mem _ 16)
    rw [hd]
  obtain E₇ : Env K W SP s₇ := E₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Dp.gpr _ (by decide) (by decide) (by decide) (by decide)) Dp.rd Dp.wr
  obtain S₇ := S.of_frame F₇ (slots_lRD L hD)
  obtain rd₇ : s₇.rd = t.rd := by rw [Dp.rd, rd₆']
  obtain wr₇ : s₇.wr = t.wr := by rw [Dp.wr, wr₆']
  obtain hc₇ : Spec.GcmSiv.ctxCiph s₇.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame F₇ (key_lR L hD) hRb
  -- The rest of the data, deciphered.
  refine Proof.AesGcmSiv.X86_64.seq_assoc (WP.seq (WP.mono (afterLoop_ok L hR E₇ S₇ (hD.of_eq rd₇ wr₇)
    (by rw [wr₇]; exact hDw) hxl hrest
    (by have h := Dp.ctr
        rw [show Stitch.cp s₆ = W + BitVec.ofNat 64 96 from rdx₆, hicb₆, hnb] at h
        exact h)
    (by rw [hc₇]; exact hx₇)) fun s₈ ⟨E₈, rd₈, wr₈, f₈, d₈⟩ => ?_))
  rw [hc₇] at d₈
  have F₈ : Frame (lR W ++ [⟨D, n⟩]) t.mem s₈.mem := F₇.trans (f₈.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 80⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩)
  have S₈ := S.of_frame F₈ (slots_lRD L hD)
  have rd₈' : s₈.rd = t.rd := rd₈.trans rd₇
  have wr₈' : s₈.wr = t.wr := wr₈.trans wr₇
  have pk := prefix_keep hxl (show 16 * (16 * (n / 256)) ≤ n by omega_arith) hx₇
    (by rw [d₈, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])])
  have xe₈ : ∀ k, k < 16 * (n / 256) → xel s₈.mem D k = xel s₇.mem D k := fun k hk => by
    show Spec.GcmSiv.ofBytes (bytesAt s₈.mem _ 16) = Spec.GcmSiv.ofBytes (bytesAt s₇.mem _ 16)
    exact congrArg _ (bytesAt_ext (m := s₇.mem) (m' := s₈.mem) (p := D + BitVec.ofNat 64 (16 * k)) (n := 16)
      fun i hi => by rw [add_ofNat_assoc]; exact pk _ (by omega_arith))
  have yy₈ : blockAt s₈.mem (W + BitVec.ofNat 64 80) = blockAt s₇.mem (W + BitVec.ofNat 64 80) :=
    Proof.AesGcm.X86_64.blockAt_frame f₈ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (hD.w.sub_right (Lay.wSub (by decide))).symm)
  have hH₈ : hOf s₈.mem W = hOf t.mem W := by
    show GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₈.mem _ 16)) = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame F₈ (fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide)]
  -- POLYVAL's registers, and the rest of the plaintext.
  refine WP.seq (WP.mono (back_ok F E₈ S₈ hn) fun s₉ ⟨g₉, x2₉, r12₉, rbp₉, m₉, rd₉, wr₉, gp₉⟩ => ?_)
  have E₉ : Env K W SP s₉ := E₈.keep gp₉ rd₉ wr₉
  refine WP.seq (WP.mono (absorb_ok true L E₉ (hH₈ ▸ g₉)
    ((hD.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)).of_eq (rd₉.trans rd₈') (wr₉.trans wr₈'))
    r12₉ rbp₉) fun s₁₀ P₁₀ => ?_)
  have f₁₀ : Frame (lR W ++ [⟨D, n⟩]) t.mem s₁₀.mem := F₈.trans ((toL (m₉ ▸ P₁₀.frame)).sub fun r hr =>
    ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
  have S₁₀ := S.of_frame f₁₀ (slots_lRD L hD)
  refine WP.mono (lens_ok P₁₀.env P₁₀.g (al := al) (n := n) S₁₀.alen S₁₀.len hA.lt hD.lt)
    fun s₁₁ ⟨y₁₁, m₁₁, rd₁₁, wr₁₁, g₁₁⟩ => ?_
  have eD : bytesAt s₁₁.mem D n = bytesAt s₈.mem D n := by
    rw [m₁₁]
    exact Proof.AesGcm.X86_64.bytesAt_frame (m₉ ▸ P₁₀.frame) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide)))
      (Nat.le_of_lt hn)
  have eX : ∀ k, k < 16 * (n / 256) → xel s₁₁.mem D k = xel s₇.mem D k := fun k hk => by
    rw [← xe₈ k hk]
    show Spec.GcmSiv.ofBytes (bytesAt s₁₁.mem _ 16) = Spec.GcmSiv.ofBytes (bytesAt s₈.mem _ 16)
    rw [m₁₁, Proof.AesGcm.X86_64.bytesAt_frame (m₉ ▸ P₁₀.frame) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hD.w.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub (by decide))) (by decide)]
  have eR : bytesAt s₁₁.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) =
      bytesAt s₉.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) := by
    rw [m₁₁]
    exact Proof.AesGcm.X86_64.bytesAt_frame P₁₀.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hD.w.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  refine ⟨P₁₀.env.keep g₁₁ rd₁₁ wr₁₁, by rw [rd₁₁, P₁₀.rd, rd₉, rd₈'], by rw [wr₁₁, P₁₀.wr, wr₉, wr₈'],
    m₁₁ ▸ f₁₀, by rw [eD, d₈], ?_⟩
  rw [y₁₁, P₁₀.y, x2₉, yy₈, Y₇, Y₃, elems_split s₁₁.mem D n, eR,
    List.map_congr_left (fun k hk => eX k (List.mem_range.mp hk)), ← ghashFrom_snoc,
    ← Proof.Gcm.ghashFrom_append, ← Proof.Gcm.ghashFrom_append]
  simp only [List.append_assoc]

/-- `open`'s counter mode and POLYVAL, by the data's length. -/
theorem decMid_ok (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops} (hlp : Stitch.LoopsOk lp) {K W SP : Addr}
    (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (.seq (.block lenCmp) (.ite .b (.seq crypt polyval) (decL lp))) t (DecPost K W SP R A D al n t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, cf₁, g₁, x₁, m₁, rd₁, wr₁⟩ := lenCmp_run E S hn
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
  have cast : ∀ t', DecPost K W SP R A D al n t₁ t' → DecPost K W SP R A D al n t t' := fun t' P =>
    ⟨P.env, P.rd.trans rd₁, P.wr.trans wr₁, m₁ ▸ P.frame, by rw [P.data, m₁], by rw [P.out, m₁]⟩
  refine WP.ite (decide (n < 256)) (eval_b cf₁) (fun _ => ?_) (fun h => ?_)
  · exact WP.mono (decS_ok F L hR E₁ (m₁ ▸ S) (hA.of_eq rd₁ wr₁) (hD.of_eq rd₁ wr₁) (by rw [wr₁]; exact hDw) hAD) cast
  · have h' : 256 ≤ n := by simpa using h
    exact WP.mono (decL_ok F hlp L hR E₁ (m₁ ▸ S) (hA.of_eq rd₁ wr₁) (hD.of_eq rd₁ wr₁) (by rw [wr₁]; exact hDw) h')
      cast

end VG.Proof.AesGcmSivReg.X86_64
