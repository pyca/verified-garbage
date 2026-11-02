module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignExpand
public import VerifiedGarbage.Proof.Ed25519.RISCV64.BaseContract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignSetup

/-!
# `vg_ed25519_sign_cached` on RISCV64: the nonce, and `R`

The prefix at `32(F)` and the message hashed into `128(F)`, the digest
reduced into the nonce at `64(F)` by a call of `vg_ed25519_scalar_reduce`,
and `R = [r]B` encoded into `out` by a call of `vg_ed25519_scalar_base`
(`signNonce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym)

/-- The message's bytes. -/
abbrev msgB (s : State) : List Byte := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat

theorem msgB_length (s : State) : (msgB s).length = (s.gpr .a4).toNat := by simp [bytesAt]

theorem sign_msg {s t : State} (hp : SignPre s) (h : SignInv s t) :
    bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat = msgB s :=
  sign_input h (s.gpr .a4).isLt hp.oM.symm hp.mC hp.mF hp.bM.symm

theorem sign_msg_cov {s t : State} (hp : SignPre s) (h : SignInv s t) : Covers [msgR s] (t.rd ++ t.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := hi
    rw [h.rd, hp.rd]
    exact ⟨r, List.mem_append_left _ (by rw [List.mem_singleton.mp hr]; simp), hc⟩

/-- The message fits beside the scratch space. -/
theorem sign_len {s : State} (hp : SignPre s) : (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 :=
  len_add_le (Nat.le_of_lt (s.gpr .a4).isLt) (by decide) hp.mC

theorem signNonce_ok (C : ShaOK) (B : BaseOk) {s t : State} (hp : SignPre s) (h : SignInv s t) {P : List Byte}
    (hP : bytesAt t.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = P) (hsy : t.syms combSym = s.syms combSym) :
    WP isa signNonce t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
        t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s)) ∧
      bytesAt t'.mem (s.gpr .a0) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (P ++ msgB s))) := by
  have hPl : P.length = 32 := by rw [← hP]; simp [bytesAt]
  have hlen := sign_len hp
  -- The hashes write the scratch space and the callees' frames.
  have toL : ∀ {m m' : Mem} {sp : Addr}, sp = s.sp → Frame [⟨s.gpr .a5, 8192⟩, below sp 208] m m' →
      Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩] m m' :=
    fun e hf => by subst e; exact hf.mono (by simp)
  have scW : ∀ {t : State}, SignInv s t → ∀ r ∈ [(⟨s.gpr .a5, 8192⟩ : Region), below t.sp 208], SignWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  have F32 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 32, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  have F64 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  have F128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  unfold signNonce
  refine WP.seq (WP.of_syms <| hashInit_ok C (sr := .s10) (h.regs _ (by decide)) (sign_env hp h)
    fun t₂ a b c f₂ g hr₂ sy₂ => ?_)
  have h₂ := signStep hp h a b c g f₂ (scW h)
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .s10) (src := .s11) (off := 32) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (sign_env hp h₂)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (sign_Fw hp h₂), 32, rfl, show 32 + 32 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F32) (by rw [h₂.sp]; exact hp.bF.sub_right F32) fun t₃ a b c f₃ g hr₃ sy₃ => ?_)
  have h₃ := signStep hp h₂ a b c g f₃ (scW h₂)
  have P₂ : bytesAt t₂.mem (s.gpr .a6 + BitVec.ofNat 64 32) 32 = P := by
    rw [← hP]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.cF.symm.sub_left F32
      · rw [h.sp]; exact hp.bF.symm.sub_left F32
  have r₃ : Repr t₃.mem (s.gpr .a5) P := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, P₂] at this
  refine WP.seq (WP.of_syms <| hashUpdate_ok C (sr := .s10) (src := .s8) (off := 0) (len := (s.gpr .a4).toNat) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide))
    (by rw [h₃.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.mov (d := .a3) (n := .s9))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s9 (by decide) (by decide) (by decide)])
    (by rw [h₃.regs _ (by decide)]; rfl) (sign_env hp h₃) (sign_msg_cov hp h₃)
    hp.mC (by rw [h₃.sp]; exact hp.bM) fun t₄ a b c f₄ g hr₄ sy₄ => ?_)
  have h₄ := signStep hp h₃ a b c g f₄ (scW h₃)
  have r₄ : Repr t₄.mem (s.gpr .a5) (P ++ msgB s) := by
    have := hr₄ P r₃ (by rw [hPl])
    rwa [sign_msg hp h₃] at this
  refine WP.seq (WP.of_syms <| hashFinalize_ok C (sr := .s10) (f := .s11) (o := 128) (out := s.gpr .a6 + BitVec.ofNat 64 128)
    (vc := fun g => g .s9 + BitVec.ofNat 64 32)
    (by decide) (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide)]; rfl)
    (Sets.addi (d := .a1) (n := .s9) (k := 32) (by decide)) (fun g g' hg => by rw [hg .s9 (by decide)])
    (sign_env hp h₄)
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, sign_Fw hp h₄, 128, rfl, show 128 + 64 ≤ 288 by decide⟩)
    (hp.cF.symm.sub_left F128) (by rw [h₄.sp]; exact hp.bF.sub_right F128) fun t₅ a b c f₅ g hd₅ sy₅ => ?_)
  have h₅ := signStep hp h₄ a b c g f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr (.inr (.inr ⟨128, 64, by decide, rfl⟩))))
    · exact .inr (.inl (by rw [h₄.sp])))
  have dg : bytesAt t₅.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 (P ++ msgB s) :=
    hd₅ _ r₄ (by rw [List.length_append, hPl, msgB_length]; omega)
      (by rw [h₄.regs _ (by decide), List.length_append, hPl, msgB_length, cnt_eq]; rfl)
  -- The nonce: `scalar_reduce`.
  have sF : Region.Disjoint ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have hFw := sign_Fw hp h₅
  have hCw : (⟨s.gpr .a5, 8192⟩ : Region) ∈ t₅.wr := (sign_env hp h₅).w
  have hOw : (⟨s.gpr .a0, 64⟩ : Region) ∈ t₅.wr := by rw [h₅.wr, hp.wr]; simp
  unfold mov
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₆ k₆ c3 c4 c5 sy₆ => ?_)
  rw [h₅.regs _ (by decide), signV_s11] at c3 c4
  rw [h₅.regs _ (by decide), BitVec.add_zero, signV_s10] at c5
  have ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine WP.seq (WP.of_syms <| WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩])
    (wr := [⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩, ⟨s.gpr .a5, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce _ _ (by decide), c4],
      by rw [State.withRegions_wr, ce _ _ (by decide), ce _ _ (by decide), c3, c5],
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c4]; exact sF,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c3, c5]; exact hp.cF.symm.sub_left F64,
      by rw [ce _ _ (by decide), ce _ _ (by decide), c4, c5]; exact hp.cF.symm.sub_left F128⟩
    (Covers.of_sub fun r hr => by
      rw [k₆.rd, k₆.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ hFw, 128, rfl, show 128 + 64 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, List.mem_append_right _ hCw, 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₆.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hFw, 64, rfl, show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨_, hCw, 0, by simp, by simp⟩) (fun t₇ a b c f₇ g _ hpost sy₇ => ?_) (by decide +kernel))
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    c3, c4, k₆.mem, dg] at hpost
  have h₇ := signStep hp h₅ (a.trans k₆.rd) (b.trans k₆.wr) (c.trans k₆.sp)
    (fun r hr => (g r hr).trans (k₆.pres r hr)) (k₆.mem ▸ f₇) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inr ⟨64, 32, by decide, rfl⟩))))
      · exact .inl rfl
  -- `R`: `scalar_base`.
  refine WP.seq (WP.of_syms <| args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) fun t₈ k₈ d3 d4 d5 sy₈ => ?_)
  rw [h₇.regs _ (by decide), BitVec.add_zero] at d3 d5
  rw [signV_s7] at d3
  rw [signV_s10] at d5
  rw [h₇.regs _ (by decide), signV_s11] at d4
  have sy : t₈.syms combSym = s.syms combSym := by rw [sy₈, sy₇, sy₆, sy₅, sy₄, sy₃, sy₂, hsy]
  have wd₈ : ∀ q < 64 * 96, t₈.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * q)) 64 =
      Impl.Ed25519.RISCV64.combWord q := fun q hq => by
    rw [← hp.words q hq, k₈.mem]
    exact h₇.frame.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega)) hp.tW
      (by decide)
  refine WP.call (k := baseRV) B (rd := [⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩, TBL (s.syms combSym)])
    (wr := [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a5, 8192⟩])
    (basePre_call d3 d4 d5 sy hp.alC (hp.oC.sub_left (Region.sub_prefix (by decide))) (hp.cF.symm.sub_left F64)
      hp.tal hp.tfit wd₈ (hp.tW _ (by simp)))
    (Covers.of_sub fun r hr => by
      rw [k₈.rd, k₈.wr, h₇.wr, h₇.rd]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨s.gpr .a6, 288⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 64, rfl,
          show 64 + 32 ≤ 288 by decide⟩
      · exact ⟨TBL (s.syms combSym), List.mem_append_left _ (by rw [hp.rd]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a0, 64⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a5, 8192⟩, List.mem_append_right _ (by rw [hp.wr]; simp), 0, by simp, by simp⟩)
    (Covers.of_sub fun r hr => by
      rw [k₈.wr, h₇.wr, hp.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s.gpr .a0, 64⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨s.gpr .a5, 8192⟩, by simp, 0, by simp, by simp⟩) (fun t₉ a b c f₉ g _ hpost' => ?_) (by decide +kernel)
  simp only [baseRV, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    d3, d4, k₈.mem] at hpost'
  have h₉ := signStep hp h₇ (a.trans k₈.rd) (b.trans k₈.wr) (c.trans k₈.sp)
    (fun r hr => (g r hr).trans (k₈.pres r hr)) (k₈.mem ▸ f₉) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inl rfl
  have keepN : bytesAt t₉.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 = bytesAt t₇.mem (s.gpr .a6 + BitVec.ofNat 64 64) 32 := by
    rw [← k₈.mem]
    exact bytes_keep f₉ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.oF.symm.sub_left F64 |>.sub_right (Region.sub_prefix (by decide))
      · exact hp.cF.symm.sub_left F64
  refine ⟨h₉, ?_, by rw [keepN, hpost], by rw [hpost', hpost]⟩
  -- The writes.
  have L64 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 64, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩ :=
    Region.sub_prefix (by decide)
  have L128 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩ := by
    have := Offset.sub (s.gpr .a6) (d := 128) (n := 64) (e := 64) (k := 128) (by decide) (by decide)
    exact this
  have g₅ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₄.mem t₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, L128⟩
    · exact ⟨below s.sp 208, by simp, by rw [h₄.sp]; exact fun _ h => h⟩
  have g₇ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₅.mem t₇.mem := by
    rw [← k₆.mem]
    exact f₇.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, L64⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  have g₉ : Frame [⟨s.gpr .a5, 8192⟩, ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩, below s.sp 208, ⟨s.gpr .a0, 32⟩]
      t₇.mem t₉.mem := by
    rw [← k₈.mem]
    exact f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  exact (toL h.sp f₂).trans <| (toL h₂.sp f₃).trans <| (toL h₃.sp f₄).trans <| g₅.trans <| g₇.trans g₉

end VG.Proof.Ed25519.RISCV64.Whole
