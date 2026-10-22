module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

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
  env : Env Ctx St W SP s
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
    (hSP : s.gpr .rsp = SP) (hW : s.gpr w = W) (hperm : Perm Ctx St W s) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsv : ∀ p ∈ saved, s.gpr p.1 = s₀.gpr p.1) :
    WP isa (.block (finEntry w)) s (FinEntry s₀ Ctx St W SP) := by
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s w hW hperm.w
  have hsv₁' : SavedAt s₁.mem W s₀ := by
    intro p hp; rw [hsv₁ p hp, hsv p hp]
  rw [hm] at f₁
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₁] at w₂ w₃
  have hw₁ : s₁.gpr w = W := by rw [hg₁, hW]
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
  have sep : Mem.Sep (W + BitVec.ofNat 64 184) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    Offset.sep W (.inl (by decide)) (by decide) (by decide)
  have f₂ : Frame [slotsR W] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 208 → (slotsR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  have hrd' : s₂.rd = s₀.rd := hrd₂.trans (hrd₁.trans hrd)
  have hwr' : s₂.wr = s₀.wr := hwr₂.trans (hwr₁.trans hwr)
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq (hrd₂.trans hrd₁) (hwr₂.trans hwr₁)⟩, ?_, ?_, h8, h9, ?_, ?_, hrd', hwr'⟩
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · refine hsv₁'.frame f₂ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · exact (f₁.mono fun r hr => by simp at hr; subst hr; simp).trans (f₂.mono fun r hr => by simp at hr; subst hr; simp)

/-- The entry of `finish`, and the address `T` of `tag` kept at `W + 200`. -/
theorem finishEntry_ok {s : State} {Ctx St W SP T : Addr} (L : Lay4 Ctx St W SP) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rsi = St) (hSP : s.gpr .rsp = SP) (hT : s.gpr .r8 = T) (hW : s.gpr .r9 = W)
    (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .r9 ++ ([.store (at_ .r15 tagPO) .r8] : List Instr))) s fun s₂ =>
      FinEntry s Ctx St W SP s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T := by
  refine WP.block_append (WP.mono (finEntry_ok (fun _ _ => rfl) hCtx hSt hSP hW hperm rfl rfl rfl
    fun _ _ => rfl) fun s₁ he => ?_)
  have w₁ := he.env.perm.wW (show 200 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.store (at_ .r15 tagPO) .r8] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 200) T ∧ (∀ r, s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.r15, w₁], ?_, ?_, ?_, ?_⟩
    · simp [he.r8, hT]
    all_goals intros; rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have f₂ : Frame [⟨W + BitVec.ofNat 64 200, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 200 ∨ 208 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega) h' (by decide)) (by decide)
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
  have L : Lay4 Ctx St W SP := Lay4.of wc ws ww d_cs d_cw d_sw hsp k_c k_s k_w
  have hperm : Perm Ctx St W s := ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  have hTw : Covers [⟨T, 16⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- The entry, and the address of `tag` kept at `W + 200`.
  refine WP.seq (WP.mono (finishEntry_ok L hCtx hSt hSP hT hW hperm) fun s₂ ⟨he, hT₂⟩ => ?_)
  have F₂ := he.frame
  have he₂ := he.env
  have dF : ∀ d k, (d + k ≤ 16 ∨ (16 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ [savedR W, slotsR W],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
  have dC : ∀ r ∈ [savedR W, slotsR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact d_cw.sub_right (Lay.wSub (by decide))
  have hH : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame F₂ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))]
  refine WP.seq (WP.seq (WP.mono (WP.with_rdwr (finTag_ok v L (o := 0) (.inl rfl) he₂ he.alen he.tlen hx))
    fun s₃ ⟨⟨he₃, f₃, ht⟩, hrd₃, hwr₃⟩ => ?_))
  -- The tag copied to `tag`.
  have dT : ∀ r ∈ tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 200, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.lay.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.kw.sub_right (Lay.wSub (by decide))).symm
  have hT₃ : s₃.mem.readW (s₃.gpr .r15 + BitVec.ofNat 64 200) 64 = T := by
    rw [he₃.r15, f₃.readW (r := ⟨W + BitVec.ofNat 64 200, 8⟩) (Region.contains_self _ _) dT (by decide), hT₂]
  obtain ⟨s₄, run₄, hb₄, f₄, hg₄, hrd₄, hwr₄⟩ := tagOut_ok (b := .r15) (d := 200) he₃.r15 hT₃
    (by rw [he₃.r15]; exact he₃.perm.wR (show 200 + 8 ≤ 2560 by decide)) he₃.perm.w
    (by rw [hwr₃, he.wr]; exact hTw)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have he₄ : Env Ctx St W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  have hsv₄ : SavedAt s₄.mem W s :=
    (he.saved.frame f₃ (saved_tagFrame L (.inl rfl))).frame f₄
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (d_tw.sub_right (Lay.wSub (by decide))).symm
  have k₄ : s₄.mem.readW SP 64 = s₃.mem.readW SP 64 := ret_kept f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact r_t
  have k₃ : s₃.mem.readW SP 64 = s₂.mem.readW SP 64 := ret_kept f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Region.sub_prefix (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_stk SP
  have k₂ : s₂.mem.readW SP 64 = s.mem.readW SP 64 := ret_kept F₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by rw [k₄, k₃, k₂]
  refine WP.mono (exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ha => ?_⟩
  have ha₂ : Absorbed s₂.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s₂.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH]
    exact ha.congr (blockAt_frame F₂ (dF 16 16 (.inr ⟨by decide, by decide⟩)))
      (bytesAt_frame F₂ (dF 32 (x.length % 16) (.inr ⟨by decide, by omega⟩)) (by omega))
  have hc : ciphOf s₂.mem Ctx = ctxCiph s.mem Ctx := ciph_frame F₂ dC
  have hJ : blockAt s₂.mem St = blockAt s.mem St := by
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
