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

end VG.Proof.AesGcmSivReg.X86_64
