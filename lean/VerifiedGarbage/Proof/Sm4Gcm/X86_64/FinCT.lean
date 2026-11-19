module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.Gcm.Be64

/-! ### `Sm4Gcm.X86_64.StreamVerify`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86_64.StreamFinish`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86_64.FinTag`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86-64: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text if there is)
and writes the tag to `W + o`, from the lengths kept at `W + 184` and
`W + 192` (`finTag_ok`), as AES-GCM's (`Proof/AesGcm/X86_64/FinTag.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm tlenO alenO)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env tFrame flush_ok blockAt_frame and15 imm_eq and_self_beq eval_e
  WP.run)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

/-- `finTag o`, for buffered input `x` (of the length the lengths give modulo 16). -/
theorem finTag_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env Ctx St W SP s 768)
    {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (finTag v.callees o) s fun s' => Env Ctx St W SP s' 768 ∧
      Frame (tagFrame St W SP o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
            (ghash (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
            [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ ciphOf s.mem Ctx (blockAt s.mem St))) := by
  have h15 := he.r15
  have r₁ := he.perm.wR (show 192 + 8 ≤ 768 by decide)
  have r₂ := he.perm.wR (show 184 + 8 ≤ 768 by decide)
  generalize hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  obtain ⟨s₁, run₁, hbx₁, hax₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)), .alu .test .rbx (.reg .rbx)] s =
        some s₁ ∧
      s₁.gpr .rbx = tL ∧ s₁.gpr .rax = aL ∧ s₁.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hT]
    · simp [gpr_setReg, hA]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hT]
      have := and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ 768 := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  -- `rbx`: the length of the buffered input, modulo 16.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => Env Ctx St W SP s₂ 768 ∧ s₂.gpr .rbx = (if tL = 0 then aL else tL) ∧
      s₂.mem = s.mem) (WP.ite (decide (tL.toNat = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)) fun s₂ h₂ => ?_)
  · have h0 : tL = 0 := by
      have : tL.toNat = 0 := by simpa using ht
      exact BitVec.eq_of_toNat_eq (by simpa using this)
    refine WP.run (Q := fun s₂ => s₂ = s₁.setReg .rbx (s₁.gpr .rax)) ⟨_, by xrun [], rfl⟩ fun s₂ e => ?_
    subst e
    exact ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl,
      by simp [gpr_setReg, hax₁, h0], by rw [mem_setReg, hm₁]⟩
  · have h0 : tL ≠ 0 := fun e => by subst e; simp at hf
    exact WP.block_nil ⟨he₁, by simp only [hbx₁, h0, ↓reduceIte], hm₁⟩
  obtain ⟨he₂, hbx₂, hm₂⟩ := h₂
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := and15 (if tL = 0 then aL else tL)
    rw [imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbx₂, hand, hx]
      split <;> rfl
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ 768 := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hm₃' : s₃.mem = s.mem := hm₃.trans hm₂
  refine WP.seq (WP.mono (flush_ok v L.lay (yo := 16) (.inr rfl) (H := H) ⟨he₃, by rw [hm₃', hH]⟩ hbx₃) fun s₄ hf => ?_)
  rw [hm₃'] at hf
  have he₄ := hf.env
  have dT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.lay.st_w (by decide) (.inr ⟨by omega_using [h₁], by omega_using [h₂]⟩)).symm
    · exact L.lay.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
    · exact L.lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact (L.lay.stk_w (by omega_using [h₂])).symm
  have hA₄ : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = aL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _) (dT 184 (by decide) (by decide))
      (by decide), hA]
  have hT₄ : s₄.mem.readW (W + BitVec.ofNat 64 192) 64 = tL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (dT 192 (by decide) (by decide))
      (by decide), hT]
  have r₃ := he₄.perm.wR (show 184 + 8 ≤ 768 by decide)
  have r₄ := he₄.perm.wR (show 192 + 8 ≤ 768 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧
      s₅.gpr .rbx = aL ∧ s₅.gpr .rbp = tL ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧
      s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hA₄]
    · simp [gpr_setReg, hT₄]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx St W SP s₅ 768 := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have f₅ : Frame (tFrame St W SP 16) s.mem s₅.mem := hm₅ ▸ hf.frame
  have hJ₅ : blockAt s₅.mem St = blockAt s.mem St := blockAt_frame f₅ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.lay.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.lay.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.lay.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.lay.stk_st (a := 0) (n := 16) (by decide)).symm
  have hc₅ : ciphOf s₅.mem Ctx = ciphOf s.mem Ctx := ciph_frame f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.lay.cs.sub_right (Lay.stSub (by decide))
    · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
    · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
    · exact L.lay.kc.symm)
  refine WP.mono (tag_ok v L ho he₅ (by rw [hm₅, hf.hH]) hJ₅) fun s₆ ht => ?_
  refine ⟨ht.env, ?_, fun ha => ?_⟩
  · refine (f₅.sub fun r hr => ?_).trans ht.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, below_stk _ (by have := stkN_eq; omega_using [])⟩
  · rw [ht.out, hc₅, hbx₅, hbp₅]
    have hw := (hf.abs ha).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [hm₅, hw]

end

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry of `finish` and
`verify` takes `W` from a register and keeps the lengths in it
(`finEntry_ok`); `finish` keeps the address of `tag` there too, computes the
tag (`finTag 0`) for any message the state represents and copies it to `tag`
(AES-GCM's `tagOut_ok`, `streamFinish_wp`), as AES-GCM's
(`Proof/AesGcm/X86_64/StreamFinish.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm save restore saved alenO tlenO tagPO tagOut)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm save_ok exit_ok SavedAt savedR slotsR ret_kept covers_left
  covers_of_mem in_off blockAt_frame bytesAt_frame ctxH_eq ofNat_lit tagOut_ok ghashInput_lens lensBlock_mod_left
  WP.forall_det WP.with_rdwr)

/-- After `finEntry w`: the registers, the kept values, and what changed. -/
structure FinEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : Env Ctx St W SP s 768
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rdx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .rcx
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W, slotsR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `finEntry w`, with `W` in `w`, from `s₀`, whose registers but `rax` are
those of `s`. -/
theorem finEntry_ok {s₀ s : State} {w : Reg} {Ctx St W SP : Addr}
    (hg : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rsi = St)
    (hSP : s.gpr .rsp = SP) (hW : s.gpr w = W) (hperm : Perm Ctx St W s 768) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsv : ∀ p ∈ saved, s.gpr p.1 = s₀.gpr p.1) :
    WP isa (.block (finEntry w)) s (FinEntry s₀ Ctx St W SP) := by
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s w hW hperm.w
  obtain hsv₁' : SavedAt s₁.mem W s₀ := by
    intro p hp; rw [hsv₁ p hp, hsv p hp]
  rw [hm] at f₁
  obtain w₂ := in_off hperm.w (show 184 + 8 ≤ 768 by decide) (by decide)
  obtain w₃ := in_off hperm.w (show 192 + 8 ≤ 768 by decide) (by decide)
  rw [← hwr₁] at w₂ w₃
  obtain hw₁ : s₁.gpr w = W := by rw [hg₁, hW]
  obtain ⟨s₂, run₂, h15, h14, h13, hsp, h8, h9, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg w), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
        .store (at_ .r15 alenO) .rdx, .store (at_ .r15 tlenO) .rcx] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.gpr .r8 = s₀.gpr .r8 ∧
      s₂.gpr .r9 = s₀.gpr .r9 ∧
      s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 184) (s₀.gpr .rdx)).writeW (W + BitVec.ofNat 64 192)
        (s₀.gpr .rcx) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [hw₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hw₁]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hSP]
    · simp [gpr_setReg, hg₁, hg .r8 (by decide)]
    · simp [gpr_setReg, hg₁, hg .r9 (by decide)]
    · simp [mem_setReg, gpr_setReg, hg₁, hg .rdx (by decide), hg .rcx (by decide)]
    all_goals rfl
  obtain sep : Mem.Sep (W + BitVec.ofNat 64 184) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    Offset.sep W (.inl (by decide)) (by decide) (by decide)
  obtain f₂ : Frame [slotsR W] s₁.mem s₂.mem := by
    rw [hm₂]
    obtain c : ∀ d, 176 ≤ d → d + 8 ≤ 208 → (slotsR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  obtain hrd' : s₂.rd = s₀.rd := hrd₂.trans (hrd₁.trans hrd)
  obtain hwr' : s₂.wr = s₀.wr := hwr₂.trans (hwr₁.trans hwr)
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq (hrd₂.trans hrd₁) (hwr₂.trans hwr₁)⟩, ?_, ?_, h8, h9, ?_, ?_, hrd', hwr'⟩
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · refine hsv₁'.frame f₂ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by omega_using []) (by omega_using [])
  · exact (f₁.mono fun r hr => by simp at hr; subst hr; simp).trans (f₂.mono fun r hr => by simp at hr; subst hr; simp)

/-- The entry of `finish`, and the address `T` of `tag` kept at `W + 200`. -/
theorem finishEntry_ok {s : State} {Ctx St W SP T : Addr} (L : Lay4 Ctx St W SP 768) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rsi = St) (hSP : s.gpr .rsp = SP) (hT : s.gpr .r8 = T) (hW : s.gpr .r9 = W)
    (hperm : Perm Ctx St W s 768) :
    WP isa (.block (finEntry .r9 ++ ([.store (at_ .r15 tagPO) .r8] : List Instr))) s fun s₂ =>
      FinEntry s Ctx St W SP s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T := by
  refine WP.block_append (WP.mono (finEntry_ok (fun _ _ => rfl) hCtx hSt hSP hW hperm rfl rfl rfl
    fun _ _ => rfl) fun s₁ he => ?_)
  obtain w₁ := he.env.perm.wW (show 200 + 8 ≤ 768 by decide)
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.store (at_ .r15 tagPO) .r8] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 200) T ∧ (∀ r, s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.r15, w₁], ?_, ?_, ?_, ?_⟩
    · simp [he.r8, hT]
    all_goals intros; rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 200, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain rd₂ : ∀ d, (d + 8 ≤ 200 ∨ 208 ≤ d) → d + 8 ≤ 768 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega_using [h]) h' (by decide)) (by decide)
  refine ⟨⟨he.env.keep (fun r _ => hg₂ r) hrd₂ hwr₂,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen, by rw [hg₂]; exact he.r8,
    by rw [hg₂]; exact he.r9,
    he.saved.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.lay.w_w (.inl (by decide)) (by decide) (by decide),
    he.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨slotsR W, by simp, Offset.sub _ (by decide) (by decide)⟩), hrd₂.trans he.rd, hwr₂.trans he.wr⟩,
    by rw [hm₂, Mem.readW_writeW_self64]⟩

/-- One run of `vg_sm4_gcm_stream_finish`, for the input `x` GHASH has. -/
theorem streamFinish_run (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamFinishX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .rcx = 0 then (s.gpr .rdx).toNat else (s.gpr .rcx).toNat) % 16) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        bytesAt s'.mem (s.gpr .r8) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .rdi)) (ghash (ctxH s.mem (s.gpr .rdi))
            (blocks (x ++ zeros (padLen x.length)))) [ofBytes (lensBlock (s.gpr .rdx).toNat (s.gpr .rcx).toNat)] ^^^
            ctxCiph s.mem (s.gpr .rdi) (blockAt s.mem (s.gpr .rsi)))) := by
  have hp' := hp
  simp only [Proof.Sm4Gcm.streamFinishX86_64, Proof.Sm4Gcm.finPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret,
    Proof.Sm4Gcm.spOk] at hp'
  obtain ⟨hrd, hwr, d_cs, d_ct, d_cw, d_sw, d_ts, d_tw, r_s, r_t, r_w, k_c, k_s, -, k_w, wc, ws, -, ww, hsp⟩ := hp'
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hT : s.gpr .r8 = T at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  obtain L : Lay4 Ctx St W SP 768 := Lay4.of wc ws ww d_cs d_cw d_sw hsp k_c k_s k_w
  obtain hperm : Perm Ctx St W s 768 := ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  obtain hTw : Covers [⟨T, 16⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- The entry, and the address of `tag` kept at `W + 200`.
  refine WP.seq (WP.mono (finishEntry_ok L hCtx hSt hSP hT hW hperm) fun s₂ ⟨he, hT₂⟩ => ?_)
  have F₂ := he.frame
  have he₂ := he.env
  obtain dF : ∀ d k, (d + k ≤ 16 ∨ (16 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ [savedR W, slotsR W],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_sw.sub_left (Lay.stSub (by omega_using [hk]))).sub_right (Lay.wSub (by decide))
    · exact (d_sw.sub_left (Lay.stSub (by omega_using [hk]))).sub_right (Lay.wSub (by decide))
  obtain dC : ∀ r ∈ [savedR W, slotsR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact d_cw.sub_right (Lay.wSub (by decide))
  obtain hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame F₂ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))]
  refine WP.seq (WP.seq (WP.mono (WP.with_rdwr (finTag_ok v L (o := 0) (.inl rfl) he₂ he.alen he.tlen hx))
    fun s₃ ⟨⟨he₃, f₃, ht⟩, hrd₃, hwr₃⟩ => ?_))
  -- The tag copied to `tag`.
  obtain dT : ∀ r ∈ tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 200, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.lay.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.kw.sub_right (Lay.wSub (by decide))).symm
  obtain hT₃ : s₃.mem.readW (s₃.gpr .r15 + BitVec.ofNat 64 200) 64 = T := by
    rw [he₃.r15, f₃.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) dT (by decide), hT₂]
  obtain ⟨s₄, run₄, hb₄, f₄, hg₄, hrd₄, hwr₄⟩ := tagOut_ok (b := .r15) (d := 200) he₃.r15 hT₃
    (by rw [he₃.r15]; exact he₃.perm.wR (show 200 + 8 ≤ 768 by decide)) he₃.perm.w
    (by rw [hwr₃, he.wr]; exact hTw)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain he₄ : Env Ctx St W SP s₄ 768 := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  obtain hsv₄ : SavedAt s₄.mem W s :=
    (he.saved.frame f₃ (saved_tagFrame L (.inl rfl))).frame f₄
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (d_tw.sub_right (Lay.wSub (by decide))).symm
  obtain k₄ : s₄.mem.readW SP 64 = s₃.mem.readW SP 64 := ret_kept f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact r_t
  obtain k₃ : s₃.mem.readW SP 64 = s₂.mem.readW SP 64 := ret_kept f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Region.sub_prefix (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_stk SP
  obtain k₂ : s₂.mem.readW SP 64 = s.mem.readW SP 64 := ret_kept F₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
  obtain hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by rw [k₄, k₃, k₂]
  refine WP.mono (exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ha => ?_⟩
  obtain ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s₂.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH]
    exact ha.congr (blockAt_frame F₂ (dF 16 16 (.inr ⟨by decide, by decide⟩)))
      (bytesAt_frame F₂ (dF 32 (x.length % 16) (.inr ⟨by decide, by omega_using []⟩)) (by omega_using []))
  obtain hc : ciphOf s₂.mem Ctx = ctxCiph s.mem Ctx := ciph_frame F₂ dC
  obtain hJ : blockAt s₂.mem St = blockAt s.mem St := by
    simpa using blockAt_frame F₂ (dF 0 16 (.inl (by decide)))
  rw [hm, hb₄, show W = W + BitVec.ofNat 64 0 by simp, ht ha₂, hc, hJ, hH]

/-- `vg_sm4_gcm_stream_finish`. -/
theorem streamFinish_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamFinishX86_64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamFinishX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamFinish_run v hp (x := List.replicate
      ((if s.gpr .rcx = 0 then (s.gpr .rdx).toNat else (s.gpr .rcx).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamFinish_run v hp (ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  rw [hq (iv, a, c) ⟨hA, hT⟩ ha, Proof.Gcm.fullTag_eq, hj, hA, hT, BitVec.toNat_ofNat, lensBlock_mod_left]
  rfl

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. A tag length `tagLenOk` does
not allow gives 0; any other pads the received tag, read from `tag`
(AES-GCM's `recv`), computes the tag (`finTag 0`) and compares (AES-GCM's
`cmp 0`), without a branch, as AES-GCM's
(`Proof/AesGcm/X86_64/StreamVerify.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm recv cmp tlO tagLenOk)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm exit_ok SavedAt savedR slotsR ret_kept covers_left
  covers_of_mem in_off add_ofNat_assoc blockAt_frame bytesAt_frame ctxH_eq ofNat_lit ghashInput_lens
  lensBlock_mod_left recv_ok cmp_ok tagLenOk_ok bytesAt_take length_bytesAt eval_e WP.run WP.forall_det)

/-- The regions the check of a received tag writes. -/
abbrev verFrame (St W SP : Addr) : List Region :=
  [⟨St, 32⟩, ⟨W, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP stkN]

/-- The tag `finTag` computes, for buffered input `x`. -/
abbrev tagOf (m : Mem) (Ctx St : Addr) (aL tL : BitVec 64) (x : List Byte) : List Byte :=
  toBytes (ghashFrom (blockAt m (Ctx + BitVec.ofNat 64 240))
    (ghash (blockAt m (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
    [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ ciphOf m Ctx (blockAt m St))

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

/-- A received tag of an allowed length `t`, at `Tp` (in `rsi`), checked. -/
theorem verifyCheck_ok {t : Nat} {s : State} (he : Env Ctx St W SP s 768)
    {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {Tp : Addr} (hsi : s.gpr .rsi = Tp)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 768⟩) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
      fun s' => Env Ctx St W SP s' 768 ∧ Frame (verFrame St W SP) s.mem s'.mem ∧
        (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
          s'.gpr .rax = (if (tagOf s.mem Ctx St aL tL x).take t = bytesAt s.mem Tp t then 1 else 0)) := by
  have La := L.lay
  refine WP.seq (WP.mono (recv_ok he hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide))))
    fun s₁ ⟨he₁, hrc, f₁, _⟩ => ?_)
  obtain dW : ∀ d k, (d + k ≤ 256 ∨ 272 ≤ d) → d + k ≤ 768 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h h' r hr; simp only [List.mem_singleton] at hr; subst hr
    exact La.w_w (by omega_using [h]) h' (by decide)
  obtain dS : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], ∀ d k, d + k ≤ 80 →
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro r hr d k hk; simp only [List.mem_singleton] at hr; subst hr
    exact La.st_w hk (.inr ⟨by decide, by decide⟩)
  obtain rd₁ : ∀ d, d + 8 ≤ 256 → s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₁.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dW d 8 (.inl hd) (by omega_using [hd]))
      (by decide)
  refine WP.seq (WP.mono (finTag_ok v L (o := 0) (.inl rfl) he₁ (by rw [rd₁ 184 (by decide), hA])
    (by rw [rd₁ 192 (by decide), hT]) hx) fun s₂ ⟨he₂, f₂, ht⟩ => ?_)
  obtain dT : ∀ d k, 112 ≤ d → d + k ≤ 512 → ∀ r ∈ tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (La.st_w (a := 0) (n := 32) (d := d) (k := k) (by decide) (.inr ⟨by omega_using [h₁], by omega_using [h₂]⟩)).symm
    · exact La.w_w (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
    · simpa using La.w_w (a := d) (n := k) (d := 0) (k := 16) (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
    · exact La.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact (L.kw.sub_right (Lay.wSub (by omega_using [h₂]))).symm
  obtain rd₂ : ∀ d, 112 ≤ d → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dT d 8 h₁ h₂) (by decide)
  obtain r₂ := he₂.perm.wR (show 224 + 8 ≤ 768 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [he₂.r15, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, rd₂ 224 (by decide) (by decide), rd₁ 224 (by decide), htl]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ : Env Ctx St W SP s₃ 768 := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  obtain hrc₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem Tp t ++ zeros (16 - t) := by
    rw [hm₃, bytesAt_frame f₂ (dT 256 16 (by decide) (by decide)) (by decide), hrc]
  refine WP.mono (cmp_ok La (by decide) (o := 0) (.inl rfl) he₃ hbx₃ h1 h16 (length_bytesAt _ _ _) hrc₃)
    fun s₄ ⟨he₄, hax₄, f₄⟩ => ⟨he₄, ?_, fun ha => ?_⟩
  · rw [hm₃] at f₄
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 32⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W, 16⟩, by simp, by simpa using Region.sub_prefix (base := W) (show 16 ≤ 16 by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
      · exact ⟨below SP stkN, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
  · have dC : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨Ctx, 256⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact La.cw'.sub_right (Lay.wSub (by decide))
    obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
      blockAt_frame f₁ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
    obtain hJ₁ : blockAt s₁.mem St = blockAt s.mem St := by simpa using blockAt_frame f₁ fun r hr => dS r hr 0 16 (by decide)
    obtain hc₁ : ciphOf s₁.mem Ctx = ciphOf s.mem Ctx := ciph_frame f₁ dC
    obtain ha₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
        (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) x := by
      rw [hH₁]
      exact ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide))
        (bytesAt_frame f₁ (fun r hr => dS r hr 32 (x.length % 16) (by omega_using [])) (by omega_using []))
    obtain hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 0) 16 = tagOf s.mem Ctx St aL tL x := by
      rw [ht ha₁, hH₁, hc₁, hJ₁]
    obtain hT₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 0) t = (tagOf s.mem Ctx St aL tL x).take t := by
      rw [hm₃, bytesAt_take _ _ h16, hT₂]
    rw [hax₄, hT₃]

end

/-- After the entry of `verify`: `FinEntry`, the tag length at `W + 224` and
in `rbx`, and the address of `tag` in `rsi`. -/
structure VerEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : Env Ctx St W SP s 768
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rdx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .rcx
  tl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = s₀.gpr .r9
  rbx : s.gpr .rbx = s₀.gpr .r9
  rsi : s.gpr .rsi = s₀.gpr .r8
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `verify`, with `W` at `[rsp + 8]`. -/
theorem verifyEntry_ok {s : State} {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rsi = St) (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8) (hperm : Perm Ctx St W s 768) :
    WP isa (.block (([.mov .rax (.mem (at_ .rsp 8))] : List Instr) ++ finEntry .rax ++
      ([.mov .rbx (.reg .r9), .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r8)] : List Instr))) s
      (VerEntry s Ctx St W SP) := by
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 8))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, ha], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.mono (finEntry_ok hg₀ (by rw [hg₀ _ (by decide), hCtx]) (by rw [hg₀ _ (by decide), hSt])
      (by rw [hg₀ _ (by decide), hSP]) hax₀ (hperm.of_eq hrd₀ hwr₀) hm₀ hrd₀ hwr₀ fun p hp => by
        simp only [VG.Impl.AesGcm.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)) fun s₁ he => ?_⟩))
  obtain w₁ := he.env.perm.wW (show 224 + 8 ≤ 768 by decide)
  obtain ⟨s₂, run₂, hbx₂, hsi₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.reg .r9),
      .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r8)] s₁ = some s₂ ∧ s₂.gpr .rbx = s.gpr .r9 ∧
      s₂.gpr .rsi = s.gpr .r8 ∧ (∀ r, r ≠ .rbx → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (s.gpr .r9) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.r15, w₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · intro r a b; simp [gpr_setReg, a, b]
    · simp [mem_setReg, gpr_setReg, he.r9]
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain rd₂ : ∀ d, (d + 8 ≤ 224 ∨ 232 ≤ d) → d + 8 ≤ 768 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega_using [h]) h' (by decide)) (by decide)
  exact ⟨he.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen,
    by rw [hm₂, Mem.readW_writeW_self64], hbx₂, hsi₂,
    he.saved.frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)),
    (he.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp).trans
      (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp),
    hrd₂.trans he.rd, hwr₂.trans he.wr⟩

/-- What the precondition of `verify` gives. -/
theorem ver_lay {s : State} (hp : Proof.Sm4Gcm.verifyPre s) :
    Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) 768 ∧
      Perm (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) s 768 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 0, 768⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 80⟩ ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, 768⟩ ∧
      (⟨s.gpr .rsi, 80⟩ : Region).Disjoint ⟨stackArg s 0, 768⟩ := by
  simp only [Proof.Sm4Gcm.verifyPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.args,
    Proof.Sm4Gcm.arg, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, -, d_tw, -, -, r_s, r_w, k_c, k_s, -, k_w, wc, ws, -, ww, hsp, -⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  rw [hA] at hrd
  refine ⟨Lay4.of wc ws ww d_cs d_cw d_sw hsp k_c k_s k_w,
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩,
    by rw [hrd]; exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))), by simpa using Region.contains_self (s.gpr .rsp + BitVec.ofNat 64 8) 8⟩,
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
    d_tw, r_s, r_w, d_sw⟩

/-- One run of `vg_sm4_gcm_stream_verify`, for the input `x` GHASH has. -/
theorem streamVerify_run (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamVerifyX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .rcx = 0 then (s.gpr .rdx).toNat else (s.gpr .rcx).toNat) % 16) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rsi + BitVec.ofNat 64 16) (s.gpr .rsi + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        let T := tagOf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) x
        let t := (s.gpr .r9).toNat
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s.mem (s.gpr .r8) t then s'.gpr .rax = 1
        else s'.gpr .rax = 0) := by
  obtain ⟨L, hperm, ha, hTr, dTW, r_s, r_w, d_sw⟩ := ver_lay hp
  have hW : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have hR9 := s.gpr .r9
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hTp : s.gpr .r8 = Tp at *
  generalize hWd : stackArg s 0 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  -- The entry, and the tag length kept at `W + 224`.
  refine WP.seq (WP.mono (verifyEntry_ok L hCtx hSt hSP hW ha hperm) fun s₂ he => ?_)
  generalize htl : s.gpr .r9 = tl at *
  refine WP.seq (WP.mono (tagLenOk_ok s₂ (t := tl.toNat) (by rw [he.rbx, htl]; simp) tl.isLt) fun s₃ ⟨hz₃, k₃⟩ => ?_)
  have he₃ : Env Ctx St W SP s₃ 768 := he.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k₃.gpr _ (by decide)) k₃.rd k₃.wr
  have F₃ : Frame [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₃.mem := by rw [k₃.mem]; exact he.frame
  have dF : ∀ p k, (⟨p, k⟩ : Region).Disjoint ⟨W, 768⟩ → ∀ r ∈ [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact h.sub_right (Lay.wSub (by decide))
  generalize ht : tl.toNat = t at *
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [k₃.mem, he.tl, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k₃.gpr _ (by decide), he.rbx, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsi₃ : s₃.gpr .rsi = Tp := by rw [k₃.gpr _ (by decide), he.rsi, hTp]
  have hA₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = s.gpr .rdx := by rw [k₃.mem]; exact he.alen
  have hT₃ : s₃.mem.readW (W + BitVec.ofNat 64 192) 64 = s.gpr .rcx := by rw [k₃.mem]; exact he.tlen
  have hTr₃ : Covers [⟨Tp, t⟩] (s₃.rd ++ s₃.wr) := by rw [k₃.rd, k₃.wr, he.rd, he.wr]; exact hTr
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env Ctx St W SP s₄ 768 ∧ Frame (verFrame St W SP) s₃.mem s₄.mem ∧
      (Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
          (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x →
        let T := tagOf s₃.mem Ctx St (s.gpr .rdx) (s.gpr .rcx) x
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s₃.mem Tp t then s₄.gpr .rax = 1 else s₄.gpr .rax = 0))
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₃) (fun hbad => ?_) (fun hok => ?_)) fun s₄ h₄ => ?_)
  · -- A length `tagLenOk` does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₄ => s₄.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
        s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₄ ⟨hax, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
    refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄, by rw [hm₄]; exact Frame.refl _ _,
      fun _ => ?_⟩
    simp only [hbad', Bool.false_eq_true, false_and, ↓reduceIte]
    exact hax
  · -- An allowed length.
    have hok' : Spec.Gcm.tagLenOk t = true := by simpa using hok
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
      omega_using [hok']
    refine WP.mono (verifyCheck_ok v L he₃ hA₃ hT₃ htl₃ hbx₃ hb.1 hb.2 hsi₃ hTr₃ dTW hx)
      fun s₄ ⟨he₄, f₄, hq⟩ => ⟨he₄, f₄, fun ha => ?_⟩
    simp only [hok', true_and]
    have hax := hq ha
    split
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
  obtain ⟨he₄, f₄, hq⟩ := h₄
  have dV : ∀ r ∈ verFrame St W SP, (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using (L.lay.st_w (a := 0) (n := 32) (d := 128) (k := 48) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · simpa using L.lay.w_w (a := 128) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.kw.sub_right (Lay.wSub (by decide))).symm
  have hsv₃ : SavedAt s₃.mem W s := by rw [k₃.mem]; exact he.saved
  have hsv₄ : SavedAt s₄.mem W s := hsv₃.frame f₄ dV
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₄ (fun r hr => ?_), ret_kept F₃ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact ret_stk SP
  refine WP.mono (exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, _, hax⟩ => ⟨hg, fun ha => ?_⟩
  have dS : ∀ d k, d + k ≤ 80 → ∀ r ∈ [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun d k hk => dF _ _ (d_sw.sub_left (Lay.stSub hk))
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq]; exact blockAt_frame F₃ (dF _ _ (L.lay.cw'.sub_left (Lay.ctxSub (by decide))))
  have ha₃ : Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
      (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH₃]
    exact ha.congr (blockAt_frame F₃ (dS 16 16 (by decide))) (bytesAt_frame F₃ (dS 32 _ (by omega_using [])) (by omega_using []))
  have hT : tagOf s₃.mem Ctx St (s.gpr .rdx) (s.gpr .rcx) x = tagOf s.mem Ctx St (s.gpr .rdx) (s.gpr .rcx) x := by
    simp only [tagOf]
    rw [hH₃, ← ctxH_eq, ciph_frame F₃ (dF _ _ L.lay.cw'), show blockAt s₃.mem St = blockAt s.mem St by
      simpa using blockAt_frame F₃ (dS 0 16 (by decide))]
  have hrc : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame F₃ (dF _ _ dTW) (by rw [← ht]; exact Nat.le_of_lt tl.isLt)
  have hq' := hq ha₃
  rw [hT, hrc] at hq'
  dsimp only
  rw [hax]
  exact hq'

theorem tagOf_eq {m : Mem} {Ctx St : Addr} {aL tL : BitVec 64} {ciph : Spec.Gcm.Block → Spec.Gcm.Block}
    {iv a c : List Byte} (hj : blockAt m St = Spec.Gcm.j0 (ctxH m Ctx) iv) (hc : ciph = ctxCiph m Ctx)
    (hA : aL = BitVec.ofNat 64 a.length) (hT : tL.toNat = c.length) :
    tagOf m Ctx St aL tL (ghashInput a c) = Spec.Gcm.fullTag ciph (ctxH m Ctx) iv a c := by
  rw [Proof.Gcm.fullTag_eq, tagOf, ← ctxH_eq, hj, hA, hT, BitVec.toNat_ofNat, lensBlock_mod_left, hc]
  rfl

/-- `vg_sm4_gcm_stream_verify`. -/
theorem streamVerify_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamVerifyX86_64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamVerifyX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamVerify_run v hp (x := List.replicate
      ((if s.gpr .rcx = 0 then (s.gpr .rdx).toNat else (s.gpr .rcx).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamVerify_run v hp (ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  obtain e := hq (iv, a, c) ⟨hA, hT⟩ ha
  dsimp only at e ⊢
  rw [tagOf_eq hj rfl hA hT] at e
  split
  · next hc => simp only [hc, and_self, ↓reduceIte] at e; rw [e]; rfl
  · next hc => simp only [hc, ↓reduceIte] at e; rw [e]; rfl

end VG.Proof.Sm4Gcm.X86_64

end

end

/-!
# SM4-GCM on x86-64: `stream_finish` and `stream_verify` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/StreamFinishCT.lean`, `StreamVerifyCT.lean`): after the
entry, both runs compute the tag from the same lengths (`finTag_rel`);
`finish` copies it to the same address, kept in `W`, and `verify` branches
only on the tag length, reads the received tag from the same address and
compares without a branch.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ tagLenOk recv cmp tlO tagPO)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm Keeps rel_regs rel_taint rel_wp rel_ite_e rel_env
  rel_reassoc_inner EnvAgree EnvAgree.regs env_agree covers_of_mem TagAt TagAtN tagOut_rel fn_rel fn_rel₂ fn_relN fn_rel₂N ct_of_rel
  recv_ok tagLenOk_ok)

theorem fin_lay {s : State} (hp : Proof.Sm4Gcm.finPre s) :
    Lay4 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) 768 ∧ Perm (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) s 768 := by
  simp only [Proof.Sm4Gcm.finPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_cs, -, d_cw, d_sw, -, -, -, -, -, k_c, k_s, -, k_w, wc, ws, -, ww, hsp⟩ := hp
  exact ⟨Lay4.of wc ws ww d_cs d_cw d_sw hsp k_c k_s k_w,
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩⟩

theorem finishEntry_fin {s : State} (hp : Proof.Sm4Gcm.finPre s) :
    WP isa (.block (finEntry .r9 ++ ([.store (at_ .r15 tagPO) .r8] : List Instr))) s fun s' =>
      FinS (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) s' ∧
        s'.mem.readW (s.gpr .r9 + BitVec.ofNat 64 200) 64 = s.gpr .r8 := by
  obtain ⟨L, hperm⟩ := fin_lay hp
  exact WP.mono (finishEntry_ok L rfl rfl rfl rfl rfl hperm) fun _ ⟨e, h⟩ => ⟨⟨e.env, e.alen, e.tlen⟩, h⟩

theorem streamFinish_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.Sm4Gcm.streamFinishX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.streamFinishX86_64.pre s₀') (hq : Proof.Sm4Gcm.streamFinishX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamFinish v.callees) fun _ _ => True := by
  obtain ⟨L, -⟩ := fin_lay hp
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have hE₂ := finishEntry_fin hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇] at hE₂
  have hE₁ := finishEntry_fin hp
  refine fn_relN (N := 768) (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := s₀.gpr .r9) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    ⟨_, by taint_decide⟩ hE₁ hE₂ ?_
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rsi = St at *
  generalize s₀.gpr .r9 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r8 = T at *
  have hw : ∀ s, FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s ∧
      s.mem.readW (W + BitVec.ofNat 64 200) 64 = T → WP isa (finTag v.callees 0) s fun s' =>
        Env Ctx St W SP s' 768 ∧ s'.mem.readW (W + BitVec.ofNat 64 200) 64 = T :=
    fun s h => WP.mono (finTag_ok v L (.inl rfl) h.1.1 h.1.2.1 h.1.2.2
      (x := List.replicate ((if s₀.gpr .rcx = 0 then (s₀.gpr .rdx).toNat else (s₀.gpr .rcx).toNat) % 16) 0)
      (by simp)) fun _ ⟨he, f, _⟩ => ⟨he, by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (L.lay.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide)
              (.inr ⟨by decide, by decide⟩)).symm
          · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2]⟩
  have a := rel_wp ((finTag_rel v L (aL := s₀.gpr .rdx) (tL := s₀.gpr .rcx) (.inl rfl)).mono
      (P' := fun (s₁ s₂ : State) => True ∧ (FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s₁ ∧
        s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = T) ∧ (FinS Ctx St W SP (s₀.gpr .rdx) (s₀.gpr .rcx) s₂ ∧
          s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T))
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2) hw hw
  -- The address of `tag`, loaded from `W + 200`, is the same in both runs.
  have tg : ∀ s, Env Ctx St W SP s 768 ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = T →
      TagAtN Ctx St W SP .r15 200 T 768 s := fun s ⟨he, hT⟩ =>
    ⟨he, by rw [he.r15]; exact hT, by rw [he.r15]; exact he.perm.wR (show 200 + 8 ≤ 768 by decide)⟩
  exact RelCT.seq a ((tagOut_rel (b := .r15) (d := 200) (by simp) ⟨_, by taint_decide⟩
    (fun _ _ h => ⟨tg _ h.2.1, tg _ h.2.2⟩)).mono (fun _ _ h => h) fun _ _ h => h)

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamFinishX86_64.pre Proof.Sm4Gcm.streamFinishX86_64.pub
      (streamFinish v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamFinish_rel v hp hp' hq

/-- The lengths kept, and the tag length at `W + 224`. -/
def VerS (Ctx St W SP : Addr) (aL tL tl : BitVec 64) (s : State) : Prop :=
  FinS Ctx St W SP aL tL s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP 768)
include L

/-- What `verify` has before checking a received tag of length `t` at `Tp`. -/
def VerT (aL tL : BitVec 64) (t : Nat) (Tp : Addr) (s : State) : Prop :=
  VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧ s.gpr .rsi = Tp ∧
    Covers [⟨Tp, t⟩] (s.rd ++ s.wr)

omit L in
theorem VerT.keep {aL tL : BitVec 64} {t : Nat} {Tp : Addr} {s s' : State}
    (h : VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s) (k : Keeps s s') :
    VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s' :=
  ⟨⟨h.1.1.keep (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) k.mem k.rd k.wr, by rw [k.mem]; exact h.1.2⟩,
    by rw [k.gpr _ (by decide), h.2.1], by rw [k.gpr _ (by decide), h.2.2.1], by rw [k.rd, k.wr]; exact h.2.2.2⟩

/-- The tag computed and compared, for an allowed length `t`. -/
theorem verifyCheck_rel {t : Nat} (h1 : 1 ≤ t) (h16 : t ≤ 16) {aL tL : BitVec 64} {Tp : Addr}
    (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 768⟩) :
    RelCT isa (fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₁ ∧
        VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₂)
      (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0))))
      fun _ _ => True := by
  have La := L.lay
  -- `recv` keeps the lengths.
  have hR : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s →
      WP isa recv s (VerS Ctx St W SP aL tL (BitVec.ofNat 64 t)) := fun s ⟨⟨h, ht⟩, hbx, hsi, hTr⟩ =>
    WP.mono (recv_ok h.1 hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide)))) fun s' ⟨he', _, f, _⟩ => by
      have d : ∀ d, 176 ≤ d → d + 8 ≤ 256 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact La.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
      exact ⟨⟨he',
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 184 (by decide) (by decide)) (by decide), h.2.1],
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 192 (by decide) (by decide)) (by decide), h.2.2]⟩,
        by rw [f.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (d 224 (by decide) (by decide)) (by decide), ht]⟩
  have a := rel_wp (rel_taint (P := fun s₁ s₂ => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) aL tL t Tp s₂) ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
      (fun _ _ h => EnvAgree.regs ⟨h.1.1.1.1, h.2.1.1.1, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hR hR
  -- `finTag` keeps the tag length.
  have hT : ∀ s, VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s → WP isa (finTag v.callees 0) s fun s' =>
      Env Ctx St W SP s' 768 ∧ s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := fun s ⟨h, ht⟩ =>
    WP.mono (finTag_ok v L (.inl rfl) h.1 h.2.1 h.2.2
      (x := List.replicate ((if tL = 0 then aL.toNat else tL.toNat) % 16) 0) (by simp)) fun _ ⟨he', f, _⟩ =>
      ⟨he', by
        rw [f.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · simpa using (La.st_w (a := 0) (n := 32) (d := 224) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          · exact La.w_w (.inr (by decide)) (by decide) (by decide)
          · simpa using La.w_w (a := 224) (n := 8) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
          · exact La.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), ht]⟩
  have b := rel_wp ((finTag_rel v L (aL := aL) (tL := tL) (.inl rfl)).mono
      (P' := fun s₁ s₂ => True ∧ VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s₁ ∧
        VerS Ctx St W SP aL tL (BitVec.ofNat 64 t) s₂) (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hT hT
  -- The tag length, and the comparison.
  have hL : ∀ s, (Env Ctx St W SP s 768 ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) →
      WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO))]) s fun s' => Env Ctx St W SP s' 768 ∧
        s'.gpr .rbx = BitVec.ofNat 64 t := fun s ⟨he, ht⟩ => by
    have r₁ := he.perm.wR (show 224 + 8 ≤ 768 by decide)
    obtain ⟨s₁, run₁, hbx, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s = some s₁ ∧
        s₁.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [he.r15, r₁], ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, ht]
      · intro r a; simp [gpr_setReg, a]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => ?_) hrd hwr, hbx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ 768 ∧
      s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) ∧ (Env Ctx St W SP s₂ 768 ∧
      s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.1 h.2.2.1) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hL hL
  have d := rel_taint (P := fun s₁ s₂ => True ∧ (Env Ctx St W SP s₁ 768 ∧ s₁.gpr .rbx = BitVec.ofNat 64 t) ∧
      (Env Ctx St W SP s₂ 768 ∧ s₂.gpr .rbx = BitVec.ofNat 64 t)) (c := cmp 0) ([.rbx] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c d))

end

theorem streamVerify_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.Sm4Gcm.streamVerifyX86_64.pre s₀)
    (hp' : Proof.Sm4Gcm.streamVerifyX86_64.pre s₀') (hq : Proof.Sm4Gcm.streamVerifyX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamVerify v.callees) fun _ _ => True := by
  obtain ⟨L, hperm, ha, hTr, dTW, -, -, -⟩ := ver_lay hp
  obtain ⟨L', hperm', ha', hTr', -, -, -, -⟩ := ver_lay hp'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq
  simp only [Proof.Sm4Gcm.arg] at q₈
  have hw8 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 8) 64 := q₈
  -- What the entry leaves in each run.
  let I : State → State → Prop := fun s₀ s => VerS (s₀.gpr .rdi) (s₀.gpr .rsi) (stackArg s₀ 0) (s₀.gpr .rsp)
      (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) s ∧ s.gpr .rbx = s₀.gpr .r9 ∧
    s.gpr .rsi = s₀.gpr .r8 ∧ Covers [⟨s₀.gpr .r8, (s₀.gpr .r9).toNat⟩] (s.rd ++ s.wr)
  have hE : ∀ {s : State}, Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) 768 →
      Perm (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) s 768 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 →
      Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr) →
      WP isa (.block (([.mov .rax (.mem (at_ .rsp 8))] : List Instr) ++ (finEntry .rax ++
        ([.mov .rbx (.reg .r9), .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r8)] : List Instr)))) s (I s) :=
    fun L hperm ha hTr => by
      rw [← List.append_assoc]
      exact WP.mono (verifyEntry_ok L rfl rfl rfl rfl ha hperm) fun _ e =>
        ⟨⟨⟨e.env, e.alen, e.tlen⟩, e.tl⟩, e.rbx, e.rsi, by rw [e.rd, e.wr]; exact hTr⟩
  have hE₁ := hE L hperm ha hTr
  have hE₂ := hE L' hperm' ha' hTr'
  simp only [I] at hE₁ hE₂
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  rw [streamVerify, List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂N (N := 768) (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := stackArg s₀ 0)
    (SP := s₀.gpr .rsp) (k := 8) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp) ⟨_, by taint_decide⟩
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    hw8 ha ha' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  generalize s₀.gpr .rdi = Ctx at *
  generalize s₀.gpr .rsi = St at *
  generalize stackArg s₀ 0 = W at *
  generalize s₀.gpr .rsp = SP at *
  generalize s₀.gpr .r8 = Tp at *
  generalize htl : s₀.gpr .r9 = tl at *
  generalize ht : tl.toNat = t at *
  have htl' : tl = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  subst htl'
  -- The tag length.
  let A : State → Prop := fun s => VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s ∧
    s.zf = some (!Spec.Gcm.tagLenOk t)
  have hK : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s →
      WP isa tagLenOk s A := fun s h =>
    WP.mono (tagLenOk_ok s h.2.1 (by rw [← ht]; exact (BitVec.ofNat 64 t).isLt)) fun s' ⟨hz, k⟩ => ⟨h.keep k, hz⟩
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => True ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s₁ ∧
      VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s₂)
      ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.1.1, h.2.2.1.1.1,
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) hK hK
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow (`rax` is 0).
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.1.1, h.1.2.2.1.1.1.1⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.1.1 h.1.2.2.1.1.1.1)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega_using [hok]
    have hc : ∀ s, VerT (Ctx := Ctx) (St := St) (W := W) (SP := SP) (s₀.gpr .rdx) (s₀.gpr .rcx) t Tp s →
        WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
          (Env Ctx St W SP · 768) := fun s ⟨⟨h, hm⟩, hbx, hsi, hTr⟩ =>
      WP.mono (verifyCheck_ok v L h.1 h.2.1 h.2.2 hm hbx hb.1 hb.2 hsi hTr dTW
        (x := List.replicate ((if s₀.gpr .rcx = 0 then (s₀.gpr .rdx).toNat else (s₀.gpr .rcx).toNat) % 16) 0)
        (by simp)) fun _ h => h.1
    exact (rel_wp ((verifyCheck_rel v L hb.1 hb.2 dTW).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) hc hc).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamVerifyX86_64.pre Proof.Sm4Gcm.streamVerifyX86_64.pub
      (streamVerify v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamVerify_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
