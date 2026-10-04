import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry of `finish` and
`verify` takes `W` from the stack and keeps the number of rounds and the
lengths in it (`finEntry_ok`); `finish` keeps the address of `tag` there too,
computes the tag (`finTag 0`) for any message the state represents and
copies it to `tag` (`tagOut_ok`, `streamFinish_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

/-- The kept public values. -/
abbrev slotsR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 176, 32⟩

/-- After `finEntry`: the registers, the kept values, and what changed. -/
structure FinEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W, slotsR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `finEntry wo`, with `W` at `[rsp + wo]`. -/
theorem finEntry_ok {s : State} {wo : Nat} {Ctx St W SP : Addr} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 wo) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 wo) 8) (hperm : Perm Ctx St W s)
    (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry wo)) s (FinEntry s Ctx St W SP) := by
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp wo))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, ha], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  rw [hm₀] at f₁
  have w₁ := in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃
  have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
  obtain ⟨s₂, run₂, h15, h14, h13, hsp, h9, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
        .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rsp = SP ∧ s₂.gpr .r9 = s.gpr .r9 ∧
      s₂.mem = ((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hax : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    refine ⟨_, by xrun [hax, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax]
    · simp [gpr_setReg, g .rdx (by decide), hSt]
    · simp [gpr_setReg, g .rdi (by decide), hCtx]
    · simp [gpr_setReg, g .rsp (by decide), hSP]
    · simp [gpr_setReg, g .r9 (by decide)]
    · simp [mem_setReg, gpr_setReg, g .rsi (by decide), g .rcx (by decide), g .r8 (by decide)]
    all_goals rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have s₁₂ := sep 176 184 (by decide) (by decide) (by decide)
  have s₁₃ := sep 176 192 (by decide) (by decide) (by decide)
  have s₂₃ := sep 184 192 (by decide) (by decide) (by decide)
  have f₂ : Frame [slotsR W] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 208 → (slotsR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, ⟨?_, hR⟩, ?_, ?_, h9, ?_, ?_, hrd', hwr'⟩
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
    exact BitVec.eq_of_toNat_eq (by simp)
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · rw [hm₂]
    simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · refine hsv₁'.frame f₂ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · exact (f₁.mono fun r hr => by simp at hr; subst hr; simp).trans (f₂.mono fun r hr => by simp at hr; subst hr; simp)

/-- `tagOut src`: the 16 bytes at `W` copied to `T`, whose address is at `b + d`. -/
theorem tagOut_ok {s : State} {W T : Addr} {b : Reg} {d : Nat} (h15 : s.gpr .r15 = W)
    (hs : s.mem.readW (s.gpr b + BitVec.ofNat 64 d) 64 = T)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 d) 8) (hw : Covers [⟨W, 2560⟩] s.wr)
    (hT : Covers [⟨T, 16⟩] s.wr) :
    ∃ s', runBlock isa (tagOut (at_ b d)) s = some s' ∧ bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧
      Frame [⟨T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .rdi → r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := in_left (rd := s.rd) (in_off hw (show 0 + 8 ≤ 2560 by decide) (by decide))
  have r₁ := in_left (rd := s.rd) (in_off hw (show 8 + 8 ≤ 2560 by decide) (by decide))
  have t₀ := in_off hT (show 0 + 8 ≤ 16 by decide) (by decide)
  have t₁ := in_off hT (show 8 + 8 ≤ 16 by decide) (by decide)
  have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
  have f0 : T + BitVec.ofNat 64 0 = T := BitVec.add_zero T
  rw [e0] at r₀
  rw [f0] at t₀
  refine ⟨_, by simp only [tagOut]; xrun [hs, hr, h15, r₀, r₁, t₀, t₁, e0, f0], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hs, f0]
    rw [Cmac.bytesAt_store2, Cmac.le8_readW, Cmac.le8_readW, ← Cmac.bytesAt_split]
  · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hs, f0]
    exact Cmac.frame_store2 _ _ _
  · intro r a b c; simp [gpr_setReg, a, b, c]
  all_goals rfl

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput ghashFrom ghash blocks zeros padLen ofBytes
  toBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

theorem ghashInput_mod (a c : List Byte) :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

/-- The entry of `finish`, and the address `T` of `tag` kept at `W + 200`. -/
theorem finishEntry_ok {s : State} {Ctx St W SP T : Addr} (L : Lay Ctx St W SP) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rdx = St) (hSP : s.gpr .rsp = SP) (hT : s.gpr .r9 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W) (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8)
    (hperm : Perm Ctx St W s)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry 8 ++ ([.store (at_ .r15 tagPO) .r9] : List Instr))) s fun s₂ =>
      FinEntry s Ctx St W SP s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = T := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hSP hW ha hperm L.ww hR) fun s₁ he => ?_)
  have w₁ := he.env.perm.wW (show 200 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.store (at_ .r15 tagPO) .r9] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 200) T ∧ (∀ r, s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.r15, w₁], ?_, ?_, ?_, ?_⟩
    · simp [he.r9, hT]
    all_goals intros; rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have f₂ : Frame [⟨W + BitVec.ofNat 64 200, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 200 ∨ 208 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  refine ⟨⟨he.env.keep (fun r _ => hg₂ r) hrd₂ hwr₂,
    ⟨by rw [rd₂ 176 (.inl (by decide)) (by decide)]; exact he.rounds.1, he.rounds.2⟩,
    by rw [rd₂ 184 (.inl (by decide)) (by decide)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (by decide)]; exact he.tlen, by rw [hg₂]; exact he.r9,
    he.saved.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by decide)) (by decide) (by decide),
    he.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨slotsR W, by simp, Offset.sub _ (by decide) (by decide)⟩), hrd₂.trans he.rd, hwr₂.trans he.wr⟩,
    by rw [hm₂, Mem.readW_writeW_self64]⟩

/-- One run of `vg_aes_gcm_stream_finish`, for the input `x` GHASH has. -/
theorem streamFinish_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rdx + BitVec.ofNat 64 16) (s.gpr .rdx + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        bytesAt s'.mem (s.gpr .r9) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .rdi)) (ghash (ctxH s.mem (s.gpr .rdi))
            (blocks (x ++ zeros (padLen x.length)))) [ofBytes (lensBlock (s.gpr .rcx).toNat (s.gpr .r8).toNat)] ^^^
            ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat (blockAt s.mem (s.gpr .rdx)))) := by
  have hp' := hp
  simp only [Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret,
    Proof.AesGcm.rounds, Proof.AesGcm.args, Proof.AesGcm.arg] at hp'
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, d_ts, d_tw, r_s, r_t, r_w, k_c, k_s, -, k_w, wc, ws, -, ww, hR⟩ := hp'
  have hWa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  rw [hA] at hrd
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hT : s.gpr .r9 = T at *
  generalize hW : stackArg s 0 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have L : Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have hperm : Perm Ctx St W s := ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  have hra : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 := by
    rw [hrd]
    exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩
  have hTw : Covers [⟨T, 16⟩] s.wr := by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- The entry, and the address of `tag` kept at `W + 200`.
  refine WP.seq (WP.mono (finishEntry_ok L hCtx hSt hSP hT hWa hra hperm hR) fun s₂ ⟨he, hT₂⟩ => ?_)
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
  refine WP.seq (WP.seq (WP.mono (WP.with_rdwr (finTag_ok v L (o := 0) (.inl rfl) he₂ he.rounds he.alen he.tlen hx))
    fun s₃ ⟨⟨he₃, _, f₃, ht⟩, hrd₃, hwr₃⟩ => ?_))
  -- The tag copied to `tag`.
  have dT : ∀ r ∈ tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 200, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := 200) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
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
    · exact ret_below SP
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
  have hc : ciphOf s₂.mem Ctx (s.gpr .rsi).toNat = ctxCiph s.mem Ctx (s.gpr .rsi).toNat :=
    ciph_frame F₂ dC hR
  have hJ : blockAt s₂.mem St = blockAt s.mem St := by
    simpa using blockAt_frame F₂ (dF 0 16 (.inl (by decide)))
  rw [hm, hb₄, show W = W + BitVec.ofNat 64 0 by simp, ht ha₂, hc, hJ, hH]

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH ctxCiph ghashInput)

theorem toNat_eq_zero {x : BitVec 64} : x = 0 ↔ x.toNat = 0 :=
  ⟨fun h => by subst h; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- The length GHASH has buffered, from `aad_len` and `text_len`. -/
theorem ghashInput_lens {a c : List Byte} {aL tL : BitVec 64} (ha : aL = BitVec.ofNat 64 a.length)
    (hc : tL.toNat = c.length) :
    (ghashInput a c).length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16 := by
  rw [ghashInput_mod]
  by_cases h : c = []
  · subst h
    have : tL = 0 := toNat_eq_zero.mpr hc
    simp only [this, ↓reduceIte, ha, toNat_mod16]
  · have : tL ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero (by rw [← hc, toNat_eq_zero.mp e]))
    simp only [h, this, ↓reduceIte, hc]

/-- `vg_aes_gcm_stream_finish`. -/
theorem streamFinish_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamFinishX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamFinish_run v hp (x := List.replicate
      ((if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamFinish_run v hp (ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  rw [hq (iv, a, c) ⟨hA, hT⟩ ha, Proof.Gcm.fullTag_eq, hj, hA, hT, BitVec.toNat_ofNat, lensBlock_mod_left]
  rfl

end VG.Proof.AesGcm.X86_64
