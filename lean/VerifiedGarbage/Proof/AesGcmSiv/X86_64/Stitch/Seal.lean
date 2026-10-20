module
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` with the loops

Untrusted: everything here is checked by Lean. From 256 bytes of data on,
`seal` computes the tag input with `hashS` (`hashS_ok`): POLYVAL of the
additional data, then of the data's 256-byte groups (`Stitch.hash_ok`),
then of the rest, the lengths and the tag input, as `polyval` does; and
enciphers the data with `cryptS` (`cryptS_ok`): the counter block from the
tag, counter mode on the groups (`Stitch.ctr_ok`), then on the rest as
`crypt` does. They leave what `polyval` and `crypt` leave (`PolyPost`,
`CryptPost`), from which `seal` is proven as before (`sealS_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl toNat_ofNat_of_lt)

/-! ## Counter mode -/

theorem cryptS_ok (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP)
    {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t
      (CryptPost K W SP R D n t) := by
  have hn := hD.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  -- The head: the counter block from the tag.
  obtain ⟨t₁, run₁, hm₁, _, _, hg₁, hrd₁, hwr₁⟩ := sHead_ok E S
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have F₁ : Frame (cryR W SP D n) t.mem t₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩
  have dD₁ : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hicb : bytesAt t₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
      ← Proof.Cmac.bytesAt_split]
  have x₁ : bytesAt t₁.mem D n = bytesAt t.mem D n := Proof.AesGcm.X86_64.bytesAt_frame f₁ dD₁ (Nat.le_of_lt hn)
  -- The loop's arguments.
  have S₁ := S.of_frame F₁ (slots_cryR L hD)
  obtain ⟨t₃, run₃, hm₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r11₃, r12₃, r9₃, hg₃, hrd₃, hwr₃⟩ := sArgs_ok E₁ S₁ hn
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have rd₃ : t₃.rd = t.rd := by rw [hrd₃, hrd₁]
  have wr₃ : t₃.wr = t.wr := by rw [hwr₃, hwr₁]
  have hp₃ : Stitch.SPre t₃ := spre_of L hR E₃ (hD.of_eq rd₃ wr₃) (by rw [wr₃]; exact hDw) h256 rdi₃ rsi₃ rdx₃ rcx₃
    r8₃ r11₃ r12₃ r9₃
  have hnb : Stitch.nb t₃ = 16 * (n / 256) := by
    show (t₃.gpr .r9).toNat = _; rw [r9₃, toNat_ofNat_of_lt (by omega_arith)]
  -- The groups.
  refine WP.seq (WP.mono (Stitch.ctr_ok hp₃ (by rw [hnb]; omega_arith)) fun t₄ Cp => ?_)
  have hnr : Stitch.nr t₃ = R := by
    show (t₃.gpr .rsi).toNat = _; rw [rsi₃, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  have hci : Stitch.ciph t₃ = Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
    show Spec.GcmSiv.aesWith (Stitch.nr t₃) (bytesAt t₃.mem (t₃.gpr .rdi) (16 * (Stitch.nr t₃ + 1))) = _
    rw [hnr, rdi₃, hm₃]
    exact ctxCiph_frame F₁ (key_cryR L hD) hRb
  have hicb₃ : Stitch.icb t₃ = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    show bytesAt t₃.mem (t₃.gpr .rdx) 16 = _; rw [rdx₃, hm₃, hicb]
  have hbA : ∀ k, Stitch.bAddr t₃ k = D + BitVec.ofNat 64 (16 * k) := fun k => by
    show t₃.gpr .r12 + _ = _; rw [r12₃]
  have hctb : ∀ k, Stitch.ctb t₃ k = Spec.Cmac.xor (bytesAt t₁.mem (D + BitVec.ofNat 64 (16 * k)) 16)
      (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R
        (Spec.GcmSiv.counterBlock (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) k)) := fun k => by
    show Spec.Cmac.xor (bytesAt t₃.mem (Stitch.bAddr t₃ k) 16) (Stitch.ciph t₃ _) = _
    rw [hbA, hm₃, hci, hicb₃]
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 1768, 256⟩] t₁.mem t₄.mem := by
    have h := Cp.frame
    simp only [Stitch.cR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.dp, Stitch.pp, hnb, rdx₃, r12₃, r11₃, hm₃] at h
    exact h
  have F₄ : Frame (cryR W SP D n) t.mem t₄.mem := F₁.trans (Fd.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by mem_lit, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 1768, 2048⟩, by mem_lit, Offset.sub W (by decide) (by decide)⟩)
  have hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hx₄ : bytesAt t₄.mem D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (16 * (16 * (n / 256))) := by
    have h := GcmSiv.ctrPart_stepN (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (m := t₁.mem) (m' := t₄.mem) D
      (i := 0) (k := 16 * (n / 256)) (fun l _ => hcl _)
      (by rw [hxl, x₁, Nat.mul_zero, GcmSiv.ctrPart_zero])
      (fun p hp ho => frame_outside Fd (P := D) (len := n) (a := 0) (n := 16 * (16 * (n / 256))) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inl (by rw [BitVec.add_zero])
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))) hn (by omega_arith) p (by rw [hxl] at hp; exact hp)
        (by omega_arith))
      (fun l hl => by
        have h := Cp.data l (by rw [hnb]; exact hl)
        rw [hbA, hctb] at h
        simpa only [Nat.zero_add] using h)
    rwa [hxl, Nat.zero_add] at h
  have C₄ : CtrSt W (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (16 * (n / 256)) t₄.mem := by
    refine CtrSt.of_bytes ?_
    have h := Cp.ctr
    rw [show Stitch.cp t₃ = W + BitVec.ofNat 64 96 from rdx₃, hicb₃, hnb] at h
    exact h
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Cp.gpr _ (by decide) (by decide) (by decide) (by decide)) Cp.rd Cp.wr
  have S₄ := S.of_frame F₄ (slots_cryR L hD)
  have rd₄ : t₄.rd = t.rd := by rw [Cp.rd, rd₃]
  have wr₄ : t₄.wr = t.wr := by rw [Cp.wr, wr₃]
  -- The data after the groups.
  obtain ⟨t₅, run₅, hm₅, h12₅, hbp₅, hg₅, hrd₅, hwr₅⟩ := rest_ok E₄ S₄ hn
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  have E₅ : Env K W SP t₅ := E₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have rd₅ : t₅.rd = t.rd := by rw [hrd₅, rd₄]
  have wr₅ : t₅.wr = t.wr := by rw [hwr₅, wr₄]
  have F₅ : Frame (cryR W SP D n) t.mem t₅.mem := by rw [hm₅]; exact F₄
  have hc₅ : Spec.GcmSiv.ctxCiph t₅.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    ctxCiph_frame F₅ (key_cryR L hD) hRb
  refine WP.mono (cryptRest_ok v eb wide L hR E₅ (S.of_frame F₅ (slots_cryR L hD))
    (hD.of_eq rd₅ wr₅) (by rw [wr₅]; exact hDw) hxl (j₀ := 16 * (n / 256)) (by omega_arith)
    (by rw [h12₅, show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega_arith])
    (by rw [hbp₅, show n % 256 = n - 16 * (16 * (n / 256)) by omega_arith]) (by rw [hm₅]; exact C₄)
    (by rw [hm₅]; exact hx₄) hc₅) fun t₆ Rp => ?_
  exact ⟨Rp.env, by rw [Rp.rd, rd₅], by rw [Rp.wr, wr₅], F₅.trans Rp.frame, Rp.data⟩

/-! ## POLYVAL -/

/-- `hash`'s arguments, from `W`. -/
abbrev hArgs : List Instr :=
  ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 ghO ++ Impl.AesGcmSiv.X86_64Stitch.groups .rdx

theorem hArgs_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa hArgs t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t₁.gpr .r8 = W + BitVec.ofNat 64 64 ∧
      t₁.gpr .r11 = W + BitVec.ofNat 64 1512 ∧ t₁.gpr .rdx = D ∧
      t₁.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256)) ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have i80 := Proof.AesGcm.X86_64.imm_eq (show 80 < 2 ^ 31 by decide)
  have i64 := Proof.AesGcm.X86_64.imm_eq (show 64 < 2 ^ 31 by decide)
  have i1512 := Proof.AesGcm.X86_64.imm_eq (show 1512 < 2 ^ 31 by decide)
  refine ⟨_, by srun [hArgs, Impl.AesGcmSiv.X86_64Stitch.groups, ptr, h15, rD, rL],
    by simp only [mem_setReg, mem_arithFlags, mem_setFlags], ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [rd_setReg, rd_arithFlags, rd_setFlags], by simp only [wr_setReg, wr_arithFlags, wr_setFlags]⟩
  iterate 4 simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, sD, i80, i64,
    i1512]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL, shr8 _ hn]
    exact dbl16 n
  · intro r hr; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]

theorem hpre_of {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {D : Addr} {n : Nat} (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n)
    (hcx : t.gpr .rcx = W + BitVec.ofNat 64 80) (h8 : t.gpr .r8 = W + BitVec.ofNat 64 64)
    (h11 : t.gpr .r11 = W + BitVec.ofNat 64 1512) (hdx : t.gpr .rdx = D)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))) : Stitch.HPre t := by
  have hn := hD.lt
  have hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [h9, toNat_ofNat_of_lt (by omega_arith)]
  constructor
  all_goals simp only [Stitch.xR, Stitch.yR, Stitch.pR, Stitch.xp, Stitch.yp, Stitch.hp, Stitch.pp, hnb, hdx, hcx, h8,
    h11]
  · omega_arith
  · omega_arith
  · exact E.perm.wR (by decide)
  · exact E.perm.wW (by decide)
  · exact Proof.Gcm.X86_64.Stitch.in_rdwr
      (by simpa using Proof.AesGcm.X86_64.in_off (d := 0) (n := 16 * (16 * (n / 256))) hDw (by omega_arith) hn)
  · exact E.perm.wW (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact ((hD.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))).symm
  · have := hD.wrap; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith

/-- POLYVAL of the additional data, the groups, the rest, the lengths, and the
tag input. -/
theorem hashS_ok (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n)
    (hN : Buf K W SP t N 12) (hDw : Covers [⟨D, n⟩] t.wr)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) (h256 : 256 ≤ n) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide) t (PolyPost K W SP N A D al n t) := by
  have hn := hD.lt
  have h15 := E.r15
  have rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have sA := S.aad
  have sL := S.alen
  obtain ⟨t₁, run₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] t = some t₁ ∧
      t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rA, rL], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sA]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sL]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  -- The additional data.
  refine WP.seq (WP.mono (absorb_ok v wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_)
  have P₂' := P₂.of_eq hm₁ hrd₁ hwr₁
  rw [hm₁] at P₂'
  have S₂ := S.absR L P₂'.frame
  have x₂ : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Sub ⟨D, n⟩ → bytesAt t₂.mem p 16 = bytesAt t.mem p 16 :=
    fun hs => Proof.AesGcm.X86_64.bytesAt_frame P₂'.frame (fun q hq => (buf_absR hD q hq).sub_left hs) (by decide)
  -- The groups.
  obtain ⟨t₃, run₃, hm₃, rcx₃, r8₃, r11₃, rdx₃, r9₃, hg₃, hrd₃, hwr₃⟩ := hArgs_ok P₂'.env S₂ hn
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have rd₃ : t₃.rd = t.rd := by rw [hrd₃, P₂'.rd]
  have wr₃ : t₃.wr = t.wr := by rw [hwr₃, P₂'.wr]
  have E₃ : Env K W SP t₃ := P₂'.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hp₃ : Stitch.HPre t₃ := hpre_of L E₃ (hD.of_eq rd₃ wr₃) (by rw [wr₃]; exact hDw) h256 rcx₃ r8₃ r11₃ rdx₃ r9₃
  have hnb : Stitch.nb t₃ = 16 * (n / 256) := by
    show (t₃.gpr .r9).toNat = _; rw [r9₃, toNat_ofNat_of_lt (by omega_arith)]
  refine WP.seq (WP.mono (Stitch.hash_ok hp₃) fun t₄ Hp => ?_)
  have Ph : AbsPost K W SP (Spec.GcmSiv.elems (bytesAt t.mem D (16 * (16 * (n / 256))))) t₂ t₄ := by
    refine ⟨E₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Hp.gpr _ (by decide) (by decide) (by decide)) Hp.rd Hp.wr,
      by rw [Hp.rd, hrd₃], by rw [Hp.wr, hwr₃], ?_, ?_⟩
    · have h := Hp.frame
      simp only [Stitch.yR, Stitch.pR, Stitch.yp, Stitch.pp, rcx₃, r11₃, hm₃] at h
      exact h.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by mem_lit, fun _ h => h⟩
        · exact ⟨_, by mem_lit, fun _ h => h⟩
    · have h := Hp.y
      rw [show Stitch.yp t₃ = W + BitVec.ofNat 64 80 from rcx₃,
        show Stitch.hk t₃ = Spec.Gcm.blockAt t₂.mem (W + BitVec.ofNat 64 64) by
          show Spec.Gcm.blockAt t₃.mem (t₃.gpr .r8) = _; rw [r8₃, hm₃],
        show Stitch.y₀ t₃ = Spec.Gcm.blockAt t₂.mem (W + BitVec.ofNat 64 80) by
          show Spec.Gcm.blockAt t₃.mem (t₃.gpr .rcx) = _; rw [rcx₃, hm₃], hnb] at h
      rw [h, GcmSiv.elems_bytesAt]
      refine congrArg _ (List.map_congr_left fun k hk => ?_)
      simp only [List.mem_range] at hk
      show Spec.GcmSiv.ofBytes (bytesAt t₃.mem (t₃.gpr .rdx + _) 16) = _
      rw [rdx₃, hm₃, x₂ (Offset.sub_base _ (by omega_arith))]
  have P₄ := P₂'.trans L Ph
  have S₄ := S.absR L P₄.frame
  -- The rest of the data.
  obtain ⟨t₅, run₅, hm₅, h12₅, hbp₅, hg₅, hrd₅, hwr₅⟩ := rest_ok P₄.env S₄ hn
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  have E₅ : Env K W SP t₅ := P₄.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have rd₅ : t₅.rd = t.rd := by rw [hrd₅, P₄.rd]
  have wr₅ : t₅.wr = t.wr := by rw [hwr₅, P₄.wr]
  refine WP.seq (WP.mono (absorb_ok v wide L E₅ ((hD.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)).of_eq
    rd₅ wr₅) h12₅ hbp₅) fun t₆ P₆ => ?_)
  have P₆' := P₆.of_eq hm₅ hrd₅ hwr₅
  rw [hm₅, Proof.AesGcm.X86_64.bytesAt_frame P₄.frame (fun q hq => (buf_absR hD q hq).sub_left
    (Offset.sub_base _ (by omega_arith))) (by omega_arith)] at P₆'
  have P₆'' := P₄.trans L P₆'
  have S₆ := S.absR L P₆''.frame
  -- The lengths, and the tag input.
  refine WP.seq (WP.mono (lens_ok v L P₆''.env S₆.alen S₆.len hA.lt hn) fun t₇ P₇ => ?_)
  refine polyPost_ok L S hN hG hY ?_
  have e : Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n)) =
      Spec.GcmSiv.elems (bytesAt t.mem D (16 * (16 * (n / 256)))) ++
        Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256))) := by
    have hs : bytesAt t.mem D n = bytesAt t.mem D (256 * (n / 256)) ++
        bytesAt t.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) := by
      rw [← Proof.Cmac.bytesAt_add]; congr 1; omega_arith
    rw [hs, pad16_append (by simp [Proof.Cmac.bytesAt_length]; omega_arith),
      GcmSiv.elems_append (by simp [Proof.Cmac.bytesAt_length]; omega_arith), show 16 * (16 * (n / 256)) = 256 * (n / 256) by omega_arith]
  rw [e, ← List.append_assoc]
  exact P₆''.trans L P₇


/-! ## `vg_aes_gcm_siv_seal` -/

theorem PolyPost.of_pre {K W SP N A D : Addr} {al n : Nat} {t t₁ t' : State} (h : PolyPost K W SP N A D al n t₁ t')
    (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) : PolyPost K W SP N A D al n t t' :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, fun hpv => by rw [← hm]; exact h.out hpv⟩

theorem CryptPost.of_pre {K W SP : Addr} {R : Nat} {D : Addr} {n : Nat} {t t₁ t' : State}
    (h : CryptPost K W SP R D n t₁ t') (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    CryptPost K W SP R D n t t' :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [← hm]; exact h.data⟩

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem sealS_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v eb L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- POLYVAL and the tag input, with the loop from 256 bytes of data on.
  obtain ⟨s₂', run₂', hcf₂', hg₂', hm₂', hrd₂', hwr₂'⟩ := lenCmp_ok Ky.env S₂ Ar.data.lt
  refine WP.seq (WP.of_runBlock ⟨s₂', run₂', ?_⟩)
  have E₂' : Env K W SP s₂' := Ky.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂' _ (by decide)) hrd₂' hwr₂'
  have S₂' : Slots W R N A D al n s₂'.mem := hm₂' ▸ S₂
  have hpo : WP isa (.ite .b (polyval v.callees wide) (Impl.AesGcmSiv.X86_64Stitch.hashS v.callees wide)) s₂'
      (PolyPost K W SP N A D al n s₂) := by
    have bA₂ := bA₁.of_eq (by rw [hrd₂', Ky.rd]) (by rw [hwr₂', Ky.wr])
    have bD₂ := bD₁.of_eq (by rw [hrd₂', Ky.rd]) (by rw [hwr₂', Ky.wr])
    have bN₂ := bN₁.of_eq (by rw [hrd₂', Ky.rd]) (by rw [hwr₂', Ky.wr])
    have hG₂ := Ky.hkey
    have hY₂ := Ky.acc
    rw [← hm₂'] at hG₂ hY₂
    refine WP.ite (decide (n < 256)) (eval_b hcf₂') (fun _ => ?_) (fun hf => ?_)
    · exact WP.mono (polyval_ok v wide L E₂' S₂' bA₂ bD₂ bN₂ hG₂ hY₂) fun _ P => P.of_pre hm₂' hrd₂' hwr₂'
    · exact WP.mono (hashS_ok v wide L E₂' S₂' bA₂ bD₂ bN₂ (by rw [hwr₂', Ky.wr, wr₁]; exact Ar.dw) hG₂ hY₂
        (by simpa using hf)) fun _ P => P.of_pre hm₂' hrd₂' hwr₂'
  refine WP.seq (WP.mono hpo fun s₃ Po => ?_)
  have f₃ : Frame (mutW W SP) s₂.mem s₃.mem := Po.frame.sub (polyR_mutW W SP)
  have S₃ := slots_mut L Ar.data.w (f₃.sub (mutW_mut W SP D n)) S₂
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₃ (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ : Frame (mutW W SP) s₃.mem s₄.mem := Tg.frame.sub (tagR_mutW W SP (by decide))
  have S₄ := slots_mut L Ar.data.w (f₄.sub (mutW_mut W SP D n)) S₃
  have f₁₄ : Frame (mutW W SP) s₁.mem s₄.mem := (fK.trans f₃).trans f₄
  -- Counter mode.
  have bD₄ : Buf K W SP s₄ D n := bD₁.of_eq (by rw [Tg.rd, Po.rd, Ky.rd]) (by rw [Tg.wr, Po.wr, Ky.wr])
  obtain ⟨s₄', run₄', hcf₄', hg₄', hm₄', hrd₄', hwr₄'⟩ := lenCmp_ok Tg.env S₄ Ar.data.lt
  refine WP.seq (WP.of_runBlock ⟨s₄', run₄', ?_⟩)
  have E₄' : Env K W SP s₄' := Tg.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄' _ (by decide)) hrd₄' hwr₄'
  have hcr : WP isa (.ite .b (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      (Impl.AesGcmSiv.X86_64Stitch.cryptS v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) s₄'
      (CryptPost K W SP R D n s₄) := by
    have S₄' : Slots W R N A D al n s₄'.mem := hm₄' ▸ S₄
    have bD₄' := bD₄.of_eq hrd₄' hwr₄'
    have hDw : Covers [⟨D, n⟩] s₄'.wr := by rw [hwr₄', Tg.wr, Po.wr, Ky.wr, wr₁]; exact Ar.dw
    refine WP.ite (decide (n < 256)) (eval_b hcf₄') (fun _ => ?_) (fun hf => ?_)
    · exact WP.mono (crypt_ok v eb wide L Ar.rounds E₄' S₄' bD₄' hDw) fun _ C => C.of_pre hm₄' hrd₄' hwr₄'
    · exact WP.mono (cryptS_ok v eb wide L Ar.rounds E₄' S₄' bD₄' hDw (by simpa using hf))
        fun _ C => C.of_pre hm₄' hrd₄' hwr₄'
  refine WP.seq (WP.mono hcr fun s₅ Cr => ?_)
  have f₁₅ : Frame (mutR W SP D n) s₁.mem s₅.mem := (f₁₄.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))
  have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₅.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have r₅ : s₅.rd = s.rd := by rw [Cr.rd, Tg.rd, Po.rd, Ky.rd, rd₁]
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, wr₁]
  -- The copy of the tag, and `restore`.
  have hTa : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [r₅, w₅]; exact h
  obtain ⟨s₆, run₆, fT, hT₆, hg₆, rd₆, wr₆⟩ := tagOut_ok Cr.env (by rw [argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₅]; exact hTw) Tb.w
  have E₆ : Env K W SP s₆ := Cr.env.of_saved hg₆ rd₆ wr₆
  have dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega_arith))).symm
  have sv₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₅ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ sv₆
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆]; exact run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, 144) (by decide)
    · exact hg₇ (.rbp, 152) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, 160) (by decide)
    · exact hg₇ (.r13, 168) (by decide)
    · exact hg₇ (.r14, 176) (by decide)
    · exact hg₇ (.r15, 184) (by decide)
  · rw [hm₇, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Po.frame (key_polyR L) hRb
    have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Tg.frame (key_tagR L (by decide)) hRb
    have n₂ : bytesAt s₂.mem N 12 = bytesAt s.mem N 12 := by rw [buf_mutW bN₁ fK, hent Ar.nonce]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_mutW bA₁ fK, hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have d₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ f₁₄, hent Ar.data]
    have t₅ : bytesAt s₅.mem W 16 = bytesAt s₄.mem W 16 := Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
    have d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [hm₇]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (by have := Ar.data.lt; omega_arith)
    have tg := Tg.out
    rw [BitVec.add_zero] at tg
    have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have po := Po.out hpv
    rw [n₂, a₂, d₂] at po
    rw [d₇, hm₇, hT₆, Cr.data, t₅, d₄, key₄, key₃, ci, tg, key₃, ci, po, ← au]
    unfold Spec.GcmSiv.encryptWith
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
    obtain ⟨a, e⟩ := dk
    rfl


/-- `vg_aes_gcm_siv_seal`. -/
theorem sealS_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : sealPre s) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.«seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' =>
      gprPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact sealS_wp' v eb wide hpv Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
