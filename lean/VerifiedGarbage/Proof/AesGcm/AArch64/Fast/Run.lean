module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64, the path for TLS records: `run`

Untrusted: everything here is checked by Lean. After the entry of `seal`, for
a 12-byte nonce and at most 16 bytes of additional data, `run` does what
`sealRest` does (`run_ok`): `front` (`front_ok`), the text encrypted as
`sealRest` encrypts it (`cryptAl_ok`), its whole blocks absorbed by one call
of `vg_ghash` (`absSeg2_ok`, `absCall2_ok`), its last bytes and the lengths
block absorbed in registers (`padMul_ok`, `mulT_ok`), and the tag
(`tagSeg_ok`, `tagCall_ok`, `tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

theorem run_ok (v : GcmImpl) {s s₁ : State} (hs : sealAArch64.pre s) (h₁ : SealEntry s s₁)
    (h12 : (s.gpr .x3).toNat = 12) (h16 : (s.gpr .x5).toNat ≤ 16) :
    WP isa (Impl.AesGcm.AArch64.Fast.run v.callees) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, _, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have h3 := ofNat_toNat' (s.gpr .x3)
  have h5 := ofNat_toNat' (s.gpr .x5)
  have h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s 1 = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  subst h12
  have hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  have hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  unfold Impl.AesGcm.AArch64.Fast.run
  rw [← h5] at sl₂
  rw [← h7] at sl₄
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  have hnon : DataOk (W + BitVec.ofNat 64 16) W s₁ Np 12 :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  have haad : DataOk (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩
  have iv₁ : bytesAt s₁.mem Np 12 = bytesAt s.mem Np 12 :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega)
  have a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega)
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr (ctxH s.mem Ctx) Np 12 s₁ :=
    ⟨he₁, fun _ _ => rfl, x23₁, by rw [x24₁, ← h3], by rw [x26₁, ← h3], x27₁, hnon, hH₁⟩
  refine WP.seq (WP.mono (front_ok L hJ haad h16 sl₁ sl₂) fun s₂ h₂ => ?_)
  rw [iv₁, a₁] at h₂
  have slot₂ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept h₂.frame (slots_frontFrame' L) h₁ h₂'
  have he₂ := h₂.env
  -- The text, from the first counter block.
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ : ∃ s₃, runBlock isa [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO,
      imm .x25 0] s₂ = some s₃ ∧ s₃.gpr .x23 = D ∧ s₃.gpr .x24 = BitVec.ofNat 64 n ∧
      s₃.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧ Regs [.x23, .x24, .x25] s₂ s₃ := by
    have q₁ := he₂.perm.wR (show 232 + 8 ≤ 2560 by decide)
    have q₂ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
    refine ⟨_, by arun [he₂.x19, q₁, q₂], ?_⟩
    refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s₂.mem.read (W + 232#64) 8 = s₂.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl,
        slot₂ 232 (by decide) (by decide), sl₃, BitVec.setWidth_eq]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s₂.mem.read (W + 240#64) 8 = s₂.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl,
        slot₂ 240 (by decide) (by decide), sl₄, BitVec.setWidth_eq]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.of_regs r₃
  have hk₃ : Kept s₁.gpr s₃ := h₂.kept.of_others r₃.others
  have x22₃ : s₃.gpr .x22 = BitVec.ofNat 64 R := by
    rw [hk₃ .x22 (by decide), x22₁, ← hRR, ofNat_toNat']
  have hdat₃ : DataW Ctx (W + BitVec.ofNat 64 16) W s₃ D n :=
    ⟨⟨covers_left (by rw [r₃.wr, h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [r₃.wr, h₂.wr, wr₁]; exact dW, dcd⟩
  have hCr : CrIn Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr R 0 D n s₃ :=
    ⟨he₃, hk₃, x22₃, hRb, x23₃, x24₃, x25₃, hdat₃⟩
  have cb₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12)) := by rw [r₃.mem]; exact h₂.cb
  generalize hJ0 : Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12) = J0 at cb₃
  refine WP.seq (WP.mono (WP.with_rdwr (cryptAl_ok L v (icb := inc32 J0) hCr (by decide)))
    fun s₄ ⟨h₄, rd₄, wr₄⟩ => ?_)
  have hctr₃ : Ctr s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₃.mem Ctx R) (inc32 J0) 0 := Proof.Gcm.ctr_zero _ _ _ _ cb₃
  have out₄ := h₄.out hctr₃
  have he₄ := h₄.env
  have dWK : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D n, (keyR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have dWS : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (ddW.sub_right (Lay.wSub (by decide))).symm
    · exact (L.st_w (a := 48) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have slot₄ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept h₄.frame dWS h₁ h₂', r₃.mem, slot₂ d h₁ h₂']
  -- The whole blocks of the ciphertext, by `vg_ghash`.
  rw [WP.seq_iff, WP.block_append_iff]
  obtain ⟨s₅, run₅, x23₅, x24₅, r₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO] s₄ =
      some s₅ ∧ s₅.gpr .x23 = D ∧ s₅.gpr .x24 = BitVec.ofNat 64 n ∧ Regs [.x23, .x24] s₄ s₅ := by
    have q₁ := he₄.perm.wR (show 232 + 8 ≤ 2560 by decide)
    have q₂ := he₄.perm.wR (show 240 + 8 ≤ 2560 by decide)
    refine ⟨_, by arun [he₄.x19, q₁, q₂], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s₄.mem.read (W + 232#64) 8 = s₄.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl,
        slot₄ 232 (by decide) (by decide), sl₃, BitVec.setWidth_eq]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
      rw [show s₄.mem.read (W + 240#64) 8 = s₄.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl,
        slot₄ 240 (by decide) (by decide), sl₄, BitVec.setWidth_eq]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ := he₄.of_regs r₅
  have hk₅ : Kept s₁.gpr s₅ := h₄.kept.of_others r₅.others
  have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [r₅.mem, hH_crFrame L hdat₃ h₄.frame, r₃.mem, h₂.hH]
  have hdat₅ : DataOk (W + BitVec.ofNat 64 16) W s₅ D n :=
    hdat₃.ok.of_eq (by rw [r₅.rd, rd₄]) (by rw [r₅.wr, wr₄])
  generalize hx₁ : bytesAt s.mem A al ++ zeros (padLen (bytesAt s.mem A al).length) = x₁ at h₂
  have hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W s.sp s₁.gpr 16 (ctxH s.mem Ctx) x₁ D n 0 s₅.mem 0 s₅ :=
    ⟨he₅, hk₅, Nat.zero_le _, by rw [x23₅]; simp, by rw [x24₅, Nat.sub_zero],
      by rw [r₅.others _ (by decide), h₄.x25], hdat₅, hH₅, fun ha => by simpa [bytesAt] using ha,
      .inr (by omega), Frame.refl _ _⟩
  refine WP.mono (absSeg2_ok L (.inr rfl) hM) fun s₆ h₆ => ?_
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2_ok L (.inr rfl) v h₆)) fun s₇ ⟨⟨h₇, hlt₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * (n / 16) = j at h₇ hlt₇
  have hjn : j ≤ n := by omega
  have he₇ := h₇.env
  have hab₅ : Absorbed s₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      (ctxH s.mem Ctx) x₁ := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁0, List.take_length, ← hx₁, ← h₂.y, r₅.mem,
        blockAt_frame h₄.frame (fun r hr => (acc_crFrame L hdat₃ r hr).sub_left (Region.sub_prefix (by decide))),
        r₃.mem]
    · rw [hx₁0, Proof.Gcm.whole_of_mod hx₁0, List.drop_length]; rfl
  have hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghash (ctxH s.mem Ctx) (blocks (x₁ ++ bytesAt s₅.mem D j)) :=
    (h₇.abs hab₅).whole_eq (by rw [List.length_append, length_bytesAt]; omega)
  have key₇ : KeyAt (ctxH s.mem Ctx) s₇.mem W := by
    refine ((h₂.key.frame (rs := []) (by rw [← r₃.mem]; exact Frame.refl _ _) (by simp)).frame h₄.frame dWK).frame
      (by rw [← r₅.mem]; exact h₇.frame) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  -- `H'` again, `Y`, and the last bytes.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := ctxH s.mem Ctx) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact key₇.2)
    key₇.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (ldrev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W s.sp s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ s₁₀.gpr .x12 = D + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), h₇.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), h₇.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  sorry

end VG.Proof.AesGcm.AArch64.Fast
