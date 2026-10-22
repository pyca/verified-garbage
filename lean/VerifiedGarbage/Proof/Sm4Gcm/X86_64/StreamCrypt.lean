module
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamText
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fn

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`), from what the precondition gives
(`CryptCtx`); `streamText` follows (`StreamText.lean`), then the exit, for
any message the state represents (`streamText_run`): encrypting appends the
ciphertext it writes (`streamEncrypt_wp`), decrypting the ciphertext it reads
(`streamDecrypt_wp`), as AES-GCM's (`Proof/AesGcm/X86_64/StreamCrypt.lean`,
`StreamRun.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm save restore saved alenO tlenO dataO lenO)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput gctr inc32)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env Perm DataOk DataW save_ok exit_ok SavedAt savedR ret_kept
  covers_left covers_of_mem in_off add_ofNat_assoc and15 imm_eq bytesAt_frame blockAt_frame ctxH_eq ofNat_lit
  ctext length_ctext length_bytesAt abs_frame ctr_frame WP.forall_det)

/-- What the entry writes in `W`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- After `cryptEntry`. -/
structure CryptEntry (s₀ : State) (Ctx St W SP D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rdx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .rcx
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 ((s₀.gpr .rcx).toNat % 16)
  saved : SavedAt s.mem W s₀
  frame : Frame [entryR W] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cryptEntry_ok {s : State} {Ctx St W SP D : Addr} {n : Nat} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rsi = St)
    (hD : s.gpr .r8 = D) (hSP : s.gpr .rsp = SP) (hW : stackArg s 0 = W) (hn : (s.gpr .r9).toNat = n)
    (hperm : Perm Ctx St W s) (hargs : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8) :
    WP isa (.block cryptEntry) s (CryptEntry s Ctx St W SP D n) := by
  have hW' : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = W := by rw [← hW, ← hSP]; rfl
  have h9 : s.gpr .r9 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₀, run₀, hax₀, hg₀, hm₀, hrd₀, hwr₀⟩ : ∃ s₀', runBlock isa [.mov .rax (.mem (at_ .rsp 8))] s = some s₀' ∧
      s₀'.gpr .rax = W ∧ (∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r) ∧ s₀'.mem = s.mem ∧ s₀'.rd = s.rd ∧ s₀'.wr = s.wr := by
    refine ⟨_, by xrun [hSP, hargs], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hW']
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  have hperm₀ : Perm Ctx St W s₀ := hperm.of_eq hrd₀ hwr₀
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s₀ .rax hax₀ hperm₀.w
  have hsv₁' : SavedAt s₁.mem W s := by
    intro p hp; rw [hsv₁ p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₀ _ (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off hperm.w (show 200 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off hperm.w (show 208 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₀, ← hwr₁] at w₂ w₃ w₄ w₅
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have q4 := sep 184 192 (by decide) (by decide) (by decide)
  have q5 := sep 184 200 (by decide) (by decide) (by decide)
  have q6 := sep 184 208 (by decide) (by decide) (by decide)
  have q7 := sep 192 200 (by decide) (by decide) (by decide)
  have q8 := sep 192 208 (by decide) (by decide) (by decide)
  have q9 := sep 200 208 (by decide) (by decide) (by decide)
  have hand := and15 (s.gpr .rcx)
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .rax), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
        .store (at_ .r15 alenO) .rdx, .store (at_ .r15 tlenO) .rcx, .store (at_ .r15 dataO) .r8,
        .mov .rbp (.reg .r9), .store (at_ .r15 lenO) .rbp, .mov .r12 (.reg .r8), .mov .rbx (.reg .rcx),
        .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .r12 = D ∧ s₂.gpr .rbp = BitVec.ofNat 64 n ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((s.gpr .rcx).toNat % 16) ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 184) (s.gpr .rdx)).writeW (W + BitVec.ofNat 64 192)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 200) D).writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 n) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r h => by rw [hg₁, hg₀ r h]
    have hax₁ : s₁.gpr .rax = W := by rw [hg₁, hax₀]
    have hsp₁ : s₁.gpr .rsp = SP := by rw [g _ (by decide), hSP]
    have hrdx := g .rdx (by decide); have hrdi := g .rdi (by decide); have hrsi := g .rsi (by decide)
    have hrcx := g .rcx (by decide); have hr8 := g .r8 (by decide); have hr9 := g .r9 (by decide)
    refine ⟨_, by xrun [hax₁, hsp₁, w₂, w₃, w₄, w₅], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hax₁]
    · simp [gpr_setReg, hrsi, hSt]
    · simp [gpr_setReg, hrdi, hCtx]
    · simp [gpr_setReg, hr8, hD]
    · simp [gpr_setReg, hr9, h9]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hrcx, hand]
    · simp [gpr_setReg, gpr_arithFlags, hsp₁]
    · simp (disch := first | decide | with_reducible assumption) [gpr_setReg, mem_setReg, mem_arithFlags,
        Mem.readW_writeW_sep, hrdx, hrcx, hr8, hr9, hD, h9]
    all_goals rfl
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hrd' : s₂.rd = s.rd := hrd₂.trans (hrd₁.trans hrd₀)
  have hwr' : s₂.wr = s.wr := hwr₂.trans (hwr₁.trans hwr₀)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 184, 32⟩] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 184 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 184, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  have rd : ∀ d (v : BitVec 64), (d = 184 ∧ v = s.gpr .rdx) ∨ (d = 192 ∧ v = s.gpr .rcx) ∨
      (d = 200 ∧ v = D) ∨ (d = 208 ∧ v = BitVec.ofNat 64 n) → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = v := by
    intro d v h
    rw [hm₂]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := first | decide | with_reducible assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq hrd' hwr'⟩, rd 184 _ (.inl ⟨rfl, rfl⟩),
    rd 192 _ (.inr (.inl ⟨rfl, rfl⟩)), rd 200 _ (.inr (.inr (.inl ⟨rfl, rfl⟩))),
    rd 208 _ (.inr (.inr (.inr ⟨rfl, rfl⟩))), h12, hbp, hbx, ?_, ?_, hrd', hwr'⟩
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

/-- What the precondition of `encrypt` and `decrypt` gives. -/
structure CryptCtx (s : State) (Ctx St W SP D : Addr) (n : Nat) : Prop where
  lay : Lay4 Ctx St W SP
  perm : Perm Ctx St W s
  args : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8
  data : DataW4 Ctx St W SP s D n
  rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩
  rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  dE : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

theorem CryptCtx.of {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s) :
    CryptCtx s (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) (s.gpr .r8) (s.gpr .r9).toNat := by
  simp only [Proof.Sm4Gcm.streamCryptPre, Proof.Sm4Gcm.stk, Proof.Sm4Gcm.ret, Proof.Sm4Gcm.args,
    Proof.Sm4Gcm.arg, Proof.Sm4Gcm.spOk] at hp
  obtain ⟨hrd, hwr, d_cs, d_cd, d_cw, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, r_s, r_d, r_w, t_c, t_s, t_d, t_w,
    wc, ws, wd, ww, sp, wsp⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  have L : Lay4 (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) := Lay4.of wc ws ww d_cs d_cw d_sw sp t_c t_s t_w
  have pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_, ⟨⟨⟨?_, by have := (s.gpr .r9).isLt; omega, wd, d_sd.symm, d_dw,
    t_d.sub_left (below8_stk _)⟩, ?_, d_cd⟩, t_d⟩, r_d, r_s, r_w, d_dw⟩
  · rw [hrd]; intro a m ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), by simp only [Region.Contains] at hc ⊢; omega⟩
  · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · simpa using in_off pm (show 0 + 8 ≤ 8 by decide) (by decide)
  · rw [hwr]; exact covers_left (covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- The slots of `W` below `176` are outside `stFrame`. -/
theorem w_stFrame {D : Addr} {n d k : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (h₁ : 128 ≤ d)
    (h₂ : d + k ≤ 176) : ∀ r ∈ stFrame St W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact L.lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.kw.sub_right (Lay.wSub (by omega))).symm

/-- `J₀` is outside `stFrame`. -/
theorem j0_stFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ stFrame St W SP D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  have e : (⟨St, 16⟩ : Region) = ⟨St + BitVec.ofNat 64 0, 16⟩ := by rw [BitVec.add_zero]
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.stSub (by decide))).symm
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.ks.sub_right (Lay.stSub (by decide))).symm

omit L in
/-- The return address is outside `stFrame`. -/
theorem ret_stFrame {D : Addr} {n : Nat} (rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩)
    (rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) (rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ stFrame St W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact rS.sub_right (Lay.stSub (by decide))
  · exact rD
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact ret_stk SP

end

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamText_run (v : GcmImpl) (enc : Bool) {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s)
    {iv a c₀ : List Byte} (hA : s.gpr .rdx = BitVec.ofNat 64 a.length) (hT : (s.gpr .rcx).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi)
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rsi) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rsi) ciph h iv a
          (c₀ ++ ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) ∧
        bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) := by
  have C := CryptCtx.of hp
  have hP : c₀.length < 2 ^ 64 := hT ▸ (s.gpr .rcx).isLt
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rsi = St at *
  generalize hW : stackArg s 0 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r8 = D at *
  generalize hn : (s.gpr .r9).toNat = n at *
  have L := C.lay
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.args) fun s₁ E => ?_)
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (d := 240) (by decide))), ← hH, ctxH_eq]
  have hc₁ : ciphOf s₁.mem Ctx = ciph := by rw [ciph_frame E.frame dCE, ← hciph]; rfl
  have eS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.lay.st_w hk (.inr ⟨by decide, by decide⟩)
  have hyA : StreamRepr s.mem St ciph H iv a c₀ → Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀) :=
    fun hy => by
      rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hy
      exact abs_frame E.frame (eS (by decide)) hy.2.1
  have hyC : StreamRepr s.mem St ciph H iv a c₀ → Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx) icb
      c₀.length := fun hy => by
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hicb] at hy
    rw [hc₁]
    exact ctr_frame E.frame (eS (by decide)) hy.2.2
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (streamText_ok v L enc E.env rfl (C.data.of_eq E.rd E.wr) E.rbp hP hH₁ (E.alen.trans hA)
    htl E.dat E.len hyA hyC) fun s₂ ⟨he₂, rd₂, wr₂, f₂, hq⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.dw.ok.w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hy => ?_⟩
  rw [hicb]
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide)))
    (by have := C.data.dw.ok.lt; omega)
  obtain ⟨qa, qc, qo⟩ := hq hy
  simp only [hc₁, hd₁] at qa qc qo
  refine ⟨?_, by rw [hm]; exact qo⟩
  have hj := hy
  rw [Proof.Gcm.streamRepr_iff] at hj ⊢
  rw [ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, hicb, List.length_append, length_ctext, length_bytesAt]
  refine ⟨?_, qa, qc⟩
  rw [← hj.1]
  have e : St = St + BitVec.ofNat 64 0 := (BitVec.add_zero St).symm
  rw [blockAt_frame f₂ (j0_stFrame L C.data.dw.ok.st), e]
  exact blockAt_frame E.frame (eS (by decide))

/-- `vg_sm4_gcm_stream_encrypt`. -/
theorem streamEncrypt_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamEncryptX86_64.pre s) :
    WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamEncryptX86_64.post s s' := by
  have run : ∀ {iv a p : List Byte}, s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = p.length →
      WP isa (streamEncrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi)
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rsi) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (streamText_run v true hp (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi)) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, ↓reduceIte, Proof.Gcm.length_gctr] at h₁ h₂
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rdx).toNat 0)
      (p := List.replicate (s.gpr .rcx).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

/-- `vg_sm4_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.streamDecryptX86_64.post s s' := by
  have run : ∀ {iv a c : List Byte}, s.gpr .rdx = BitVec.ofNat 64 a.length → (s.gpr .rcx).toNat = c.length →
      WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi)
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rsi) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
          StreamRepr s'.mem (s.gpr .rsi) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (streamText_run v false hp (iv := iv) (c₀ := c) hA hT)
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, Bool.false_eq_true, ↓reduceIte] at h₁
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rdx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .rcx).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rdx).toNat 0)
      (c := List.replicate (s.gpr .rcx).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.Sm4Gcm.X86_64
