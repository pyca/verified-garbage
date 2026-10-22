module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

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
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- A received tag of an allowed length `t`, at `Tp` (in `rsi`), checked. -/
theorem verifyCheck_ok {t : Nat} {s : State} (he : Env Ctx St W SP s)
    {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {Tp : Addr} (hsi : s.gpr .rsi = Tp)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, 2560⟩) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
      fun s' => Env Ctx St W SP s' ∧ Frame (verFrame St W SP) s.mem s'.mem ∧
        (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
          s'.gpr .rax = (if (tagOf s.mem Ctx St aL tL x).take t = bytesAt s.mem Tp t then 1 else 0)) := by
  have La := L.lay
  refine WP.seq (WP.mono (recv_ok he hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (by decide))))
    fun s₁ ⟨he₁, hrc, f₁, _⟩ => ?_)
  have dW : ∀ d k, (d + k ≤ 256 ∨ 272 ≤ d) → d + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h h' r hr; simp only [List.mem_singleton] at hr; subst hr
    exact La.w_w (by omega) h' (by decide)
  have dS : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], ∀ d k, d + k ≤ 80 →
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro r hr d k hk; simp only [List.mem_singleton] at hr; subst hr
    exact La.st_w hk (.inr ⟨by decide, by decide⟩)
  have rd₁ : ∀ d, d + 8 ≤ 256 → s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₁.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dW d 8 (.inl hd) (by omega))
      (by decide)
  refine WP.seq (WP.mono (finTag_ok v L (o := 0) (.inl rfl) he₁ (by rw [rd₁ 184 (by decide), hA])
    (by rw [rd₁ 192 (by decide), hT]) hx) fun s₂ ⟨he₂, f₂, ht⟩ => ?_)
  have dT : ∀ d k, 112 ≤ d → d + k ≤ 512 → ∀ r ∈ tagFrame St W SP 0, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (La.st_w (a := 0) (n := 32) (d := d) (k := k) (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact La.w_w (.inr (by omega)) (by omega) (by decide)
    · simpa using La.w_w (a := d) (n := k) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
    · exact La.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.kw.sub_right (Lay.wSub (by omega))).symm
  have rd₂ : ∀ d, 112 ≤ d → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dT d 8 h₁ h₂) (by decide)
  have r₂ := he₂.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [he₂.r15, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, rd₂ 224 (by decide) (by decide), rd₁ 224 (by decide), htl]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hrc₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem Tp t ++ zeros (16 - t) := by
    rw [hm₃, bytesAt_frame f₂ (dT 256 16 (by decide) (by decide)) (by decide), hrc]
  refine WP.mono (cmp_ok La (o := 0) (.inl rfl) he₃ hbx₃ h1 h16 (length_bytesAt _ _ _) hrc₃)
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
    have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
      blockAt_frame f₁ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
    have hJ₁ : blockAt s₁.mem St = blockAt s.mem St := by simpa using blockAt_frame f₁ fun r hr => dS r hr 0 16 (by decide)
    have hc₁ : ciphOf s₁.mem Ctx = ciphOf s.mem Ctx := ciph_frame f₁ dC
    have ha₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
        (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) x := by
      rw [hH₁]
      exact ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide))
        (bytesAt_frame f₁ (fun r hr => dS r hr 32 (x.length % 16) (by omega)) (by omega))
    have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 0) 16 = tagOf s.mem Ctx St aL tL x := by
      rw [ht ha₁, hH₁, hc₁, hJ₁]
    have hT₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 0) t = (tagOf s.mem Ctx St aL tL x).take t := by
      rw [hm₃, bytesAt_take _ _ h16, hT₂]
    rw [hax₄, hT₃]

end

/-- After the entry of `verify`: `FinEntry`, the tag length at `W + 224` and
in `rbx`, and the address of `tag` in `rsi`. -/
structure VerEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : Env Ctx St W SP s
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
theorem verifyEntry_ok {s : State} {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rsi = St) (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8) (hperm : Perm Ctx St W s) :
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
  have w₁ := he.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
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
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 224 ∨ 232 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.w_w (by omega) h' (by decide)) (by decide)
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
    Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) ∧
      Perm (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) s ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 0, 2560⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 80⟩ ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, 2560⟩ ∧
      (⟨s.gpr .rsi, 80⟩ : Region).Disjoint ⟨stackArg s 0, 2560⟩ := by
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
  have he₃ : Env Ctx St W SP s₃ := he.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k₃.gpr _ (by decide)) k₃.rd k₃.wr
  have F₃ : Frame [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₃.mem := by rw [k₃.mem]; exact he.frame
  have dF : ∀ p k, (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
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
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env Ctx St W SP s₄ ∧ Frame (verFrame St W SP) s₃.mem s₄.mem ∧
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
      omega
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
    exact ha.congr (blockAt_frame F₃ (dS 16 16 (by decide))) (bytesAt_frame F₃ (dS 32 _ (by omega)) (by omega))
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
  have e := hq (iv, a, c) ⟨hA, hT⟩ ha
  dsimp only at e ⊢
  rw [tagOf_eq hj rfl hA hT] at e
  split
  · next hc => simp only [hc, and_self, ↓reduceIte] at e; rw [e]; rfl
  · next hc => simp only [hc, ↓reduceIte] at e; rw [e]; rfl

end VG.Proof.Sm4Gcm.X86_64
