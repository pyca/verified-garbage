import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts

/-!
# AES-GCM on x86-64: the entry of `vg_aes_gcm_stream_encrypt` and `_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`), and what the precondition gives
(`CryptCtx`); `streamText` follows (`StreamText.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the entry writes in `W`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- After `cryptEntry`. -/
structure CryptEntry (s₀ : State) (Ctx St W SP D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 ((s₀.gpr .r8).toNat % 16)
  saved : SavedAt s.mem W s₀
  frame : Frame [entryR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cryptEntry_ok {s : State} {Ctx St W SP D : Addr} {n : Nat} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hD : s.gpr .r9 = D) (hSP : s.gpr .rsp = SP) (hW : stackArg s 1 = W) (hn : (stackArg s 0).toNat = n)
    (hperm : Perm Ctx St W s) (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hargs : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hdA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block cryptEntry) s (CryptEntry s Ctx St W SP D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W := by rw [← hW, ← hSP]; rfl
  have hn' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := by
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hSP]; rfl
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, hargs.2], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₁ := in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off hperm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off hperm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₁ w₂ w₃ w₄ w₅
  have a₁ := hargs.1
  rw [← hrd₀, ← hwr₀, ← hrd₁, ← hwr₁] at a₁
  have hsepA : ∀ (m : Mem) (k : Nat), Frame [⟨W + BitVec.ofNat 64 128, k⟩] s.mem m → k ≤ 2432 →
      m.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := fun m k hf hk => by
    rw [hf.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hdA.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))) (by decide), hn']
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := hsepA _ 48 (hm₀ ▸ f₁) (by decide)
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 216 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Region.Disjoint.sep ((hdA.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (n := 8) (d := d) (by omega))) (Region.contains_self _ _) (Region.contains_self _ _)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have a₁₇₆ := sA 176 (by decide) (by decide)
  have a₁₈₄ := sA 184 (by decide) (by decide)
  have a₁₉₂ := sA 192 (by decide) (by decide)
  have a₂₀₀ := sA 200 (by decide) (by decide)
  have q0 := sep 176 184 (by decide) (by decide) (by decide)
  have q1 := sep 176 192 (by decide) (by decide) (by decide)
  have q2 := sep 176 200 (by decide) (by decide) (by decide)
  have q3 := sep 176 208 (by decide) (by decide) (by decide)
  have q4 := sep 184 192 (by decide) (by decide) (by decide)
  have q5 := sep 184 200 (by decide) (by decide) (by decide)
  have q6 := sep 184 208 (by decide) (by decide) (by decide)
  have q7 := sep 192 200 (by decide) (by decide) (by decide)
  have q8 := sep 192 208 (by decide) (by decide) (by decide)
  have q9 := sep 200 208 (by decide) (by decide) (by decide)
  have hand := and15 (s.gpr .r8)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi),
        .store (at_ .r15 roundsO) .rsi, .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8,
        .store (at_ .r15 dataO) .r9, .mov .rbp (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rbp,
        .mov .r12 (.reg .r9), .mov .rbx (.reg .r8), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧ s₂.gpr .rbp = BitVec.ofNat 64 n ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((s.gpr .r8).toNat % 16) ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8)).writeW (W + BitVec.ofNat 64 200) D).writeW
          (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₁, w₂, w₃, w₄, w₅, a₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, hrdx, hSt]
    · simp [gpr_setReg, hrdi, hCtx]
    · simp [gpr_setReg, hr9, hD]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, Mem.readW_writeW_sep, hn₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hr8, hand]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags, Mem.readW_writeW_sep,
        hn₁, hrsi, hrcx, hr8, hr9, hD]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 176, 40⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 176, 40⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 176 ∧ v = s.gpr .rsi) ∨ (d = 184 ∧ v = s.gpr .rcx) ∨ (d = 192 ∧ v = s.gpr .r8) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, ⟨?_, hR⟩, rd 184 _ (.inr (.inl ⟨rfl, rfl⟩)),
    rd 192 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))), rd 200 _ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))),
    rd 208 _ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))), h12, hbp, hbx, ?_, ?_, hrd', hwr'⟩
  · rw [rd 176 _ (.inl ⟨rfl, rfl⟩)]; exact BitVec.eq_of_toNat_eq (by simp)
  · exact hsv₁'.frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · rw [hm₀] at f₁
    exact (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What the precondition of `encrypt` and `decrypt` gives. -/
structure CryptCtx (s : State) (Ctx St W SP D : Addr) (n : Nat) : Prop where
  lay : Lay Ctx St W SP
  perm : Perm Ctx St W s
  ww : W.toNat + 2560 ≤ 2 ^ 64
  args : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8 ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  dA : (⟨SP + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  data : DataW Ctx St W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  /-- The stack of the call of `vg_aes_gcm_encrypt_blocks` or `_decrypt_blocks`. -/
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_s : (below SP 24).Disjoint ⟨St, 80⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat

theorem CryptCtx.of {cl : Nat} {s : State} (hp : Proof.AesGcm.streamCryptPre cl s) (hcl : 256 ≤ cl) :
    CryptCtx s (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .r9) (stackArg s 0).toNat := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, hwr, d_cs, d_cd, d_cw, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, r_s, r_d, r_w, t_c, t_s, t_d, t_w,
    wc, ws, wd, ww, sp24, wsp, hR⟩ := hp
  have c256 : Region.Sub ⟨s.gpr .rdi, 256⟩ ⟨s.gpr .rdi, cl⟩ := Region.sub_prefix hcl
  replace d_cs := d_cs.sub_left c256
  replace d_cd := d_cd.sub_left c256
  replace d_cw := d_cw.sub_left c256
  replace t_c := t_c.sub_right c256
  replace wc : (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 := by omega
  have b8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by decide) (by decide)
  have k_c := t_c.sub_left b8
  have k_s := t_s.sub_left b8
  have k_d := t_d.sub_left b8
  have k_w := t_w.sub_left b8
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  have L : Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ww, ⟨?_, ?_⟩, d_wa.symm, ⟨⟨?_, by have := (stackArg s 0).isLt; omega, wd, d_sd.symm, d_dw,
    k_d⟩, ?_, d_cd⟩, r_d, r_s, r_w, d_dw, hR, t_c, t_s, t_w, t_d, sp24⟩
  · rw [hrd]; intro a m ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), by simp only [Region.Contains] at hc ⊢; omega⟩
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · simpa using in_off pm (show 0 + 8 ≤ 16 by decide) (by decide)
  · have := in_off pm (show 8 + 8 ≤ 16 by decide) (by decide)
    rwa [add_ofNat_assoc] at this
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The key context of kind `M`, from the precondition of `encrypt` and `decrypt`. -/
theorem CtxExt.ofCrypt {M : Gcm.X86_64.Stitch.CtxMode} {s : State} (hp : Proof.AesGcm.streamCryptPre M.len s)
    (hok : M.ok s.mem (s.gpr .rdi)) :
    CtxExt M (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .r9) (stackArg s 0).toNat s := by
  simp only [Proof.AesGcm.streamCryptPre, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.args,
    Proof.AesGcm.arg, Proof.AesGcm.rounds] at hp
  obtain ⟨hrd, -, d_cs, d_cd, d_cw, -, -, -, -, -, -, -, -, -, t_c, -, -, -, wc, -⟩ := hp
  exact ⟨wc, d_cs, d_cw, d_cd, t_c,
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)), hok⟩

end VG.Proof.AesGcm.X86_64
