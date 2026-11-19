module

import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece

/-! ### `AesGcm.X86_64.StreamCrypt`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86-64: the entry of `vg_aes_gcm_stream_encrypt` and `_decrypt`

Untrusted: everything here is checked by Lean. The entry keeps the public
arguments in `W` (`cryptEntry_ok`), and what the precondition gives
(`CryptCtx`); `streamText` follows (`StreamText.lean`).
-/

@[expose] public section

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
      exact (hdA.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega_using [hk]))) (by decide), hn']
  have hn₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n := hsepA _ 48 (hm₀ ▸ f₁) (by decide)
  have sA : ∀ d, 176 ≤ d → d + 8 ≤ 216 → Mem.Sep (SP + BitVec.ofNat 64 8) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Region.Disjoint.sep ((hdA.sub_left (Region.sub_prefix (by decide))).sub_right
      (Lay.wSub (n := 8) (d := d) (by omega_using [h₂]))) (Region.contains_self _ _) (Region.contains_self _ _)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega_using [ha]) (by omega_using [hd])
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
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
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
      exact Offset.disjoint _ (.inl (by decide)) (by omega_using []) (by omega_using [])
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
  obtain c256 : Region.Sub ⟨s.gpr .rdi, 256⟩ ⟨s.gpr .rdi, cl⟩ := Region.sub_prefix hcl
  replace d_cs := d_cs.sub_left c256
  replace d_cd := d_cd.sub_left c256
  replace d_cw := d_cw.sub_left c256
  replace t_c := t_c.sub_right c256
  replace wc : (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 := by omega_using [hcl, wc]
  obtain b8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by decide) (by decide)
  obtain k_c := t_c.sub_left b8
  obtain k_s := t_s.sub_left b8
  obtain k_d := t_d.sub_left b8
  obtain k_w := t_w.sub_left b8
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at hrd d_sa d_da d_wa
  obtain L : Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain pm : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨L, ⟨?_, ?_, ?_⟩, ww, ⟨?_, ?_⟩, d_wa.symm, ⟨⟨?_, by have := (stackArg s 0).isLt; omega_using [], wd, d_sd.symm, d_dw,
    k_d⟩, ?_, d_cd⟩, r_d, r_s, r_w, d_dw, hR, t_c, t_s, t_w, t_d, sp24⟩
  · rw [hrd]; intro a m ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), by simp only [Region.Contains] at hc ⊢; omega_using [hcl, hc]⟩
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

end

end

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. Both runs take the same
pieces of `streamText` (`streamText_rel`): the branches are on the length
of the data and of the text so far, the same in both; `crypt`, `absorb`,
`flush` and the call of the whole blocks are on data at the same address,
of the same length (`part_rel`, `blocks_rel`, `start_rel`); between them,
each run keeps `SInv` (with no hypotheses: `SI`), from the correctness
proofs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)

/-- Two runs, each with what it satisfies after `c`. -/
theorem rel_both {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True) (hw₁ : ∀ s, F₁ s → WP isa c s G₁)
    (hw₂ : ∀ s, F₂ s → WP isa c s G₂) : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp h (fun _ _ h => h) hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code whose leakage depends only on the registers `rs` and the
environment's. -/
theorem rel_envT {Ctx St W SP : Addr} {N : Nat} {F : State → Prop} {c : Prog isa} (rs : List Reg)
    (hF : ∀ s, F s → Env Ctx St W SP s N) (hag : ∀ s₁ s₂, F s₁ → F s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (rs ++ ([.r13, .r14, .r15, .rsp] : List Reg))) c hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) c fun _ _ => True :=
  rel_taint (rs ++ [.r13, .r14, .r15, .rsp]) (fun s₁ s₂ h r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hag _ _ h.1 h.2 r hr
    · exact env_agree (hF _ h.1) (hF _ h.2) r hr) hc

/-- One run between the pieces of `streamText`: `SInv`, with no hypotheses. -/
def SI (M : Gcm.X86_64.Stitch.CtxMode) (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  ∃ H icb x₀ m₀, SCtx M Ctx St W SP R H D n m₀ ∧ x₀.length % 16 = P₀ % 16 ∧
    SInv M False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s

section
variable {M : Gcm.X86_64.Stitch.CtxMode} {Ctx St W SP : Addr} {R P₀ : Nat} {enc : Bool} {D : Addr} {n : Nat}

theorem SI.env {j : Nat} {s : State} (h : SI M Ctx St W SP R P₀ enc D n j s) : Env Ctx St W SP s :=
  let ⟨_, _, _, _, _, _, I⟩ := h; I.env

/-- What a piece does to `SInv`, to `SI`. -/
theorem SI.lift {j j' : Nat} {s : State} {c : Prog isa} {G : State → Prop} (h : SI M Ctx St W SP R P₀ enc D n j s)
    (hw : ∀ {H icb x₀ m₀}, SCtx M Ctx St W SP R H D n m₀ → x₀.length % 16 = P₀ % 16 →
      SInv M False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s →
      WP isa c s fun s' => SInv M False Ctx St W SP R H icb x₀ P₀ enc D n m₀ j' s' ∧ G s') :
    WP isa c s fun s' => SI M Ctx St W SP R P₀ enc D n j' s' ∧ G s' := by
  obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := h
  exact WP.mono (hw K hx I) fun s' ⟨I', g⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, g⟩

theorem SI.regs {j : Nat} {s s' : State} (h : SI M Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : SI M Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.regs hg hm hrd hwr⟩

theorem SI.slots {j : Nat} {s s' : State} (h : SI M Ctx St W SP R P₀ enc D n j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] s.mem s'.mem) :
    SI M Ctx St W SP R P₀ enc D n j s' :=
  let ⟨H, icb, x₀, m₀, K, hx, I⟩ := h; ⟨H, icb, x₀, m₀, K, hx, I.slots K hg hrd hwr h₁ h₂ hf⟩

end

/-! ## A part of the data -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R P₀ : Nat} {D : Addr} {n : Nat}
include L

/-- Before `part`: what `part_ok` needs. -/
def PartPre (M : Gcm.X86_64.Stitch.CtxMode) (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j k : Nat) (s : State) : Prop :=
  SI M Ctx St W SP R P₀ enc D n j s ∧ j + k ≤ n ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧
    s.gpr .rbp = BitVec.ofNat 64 k ∧ s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- Between `crypt` and `absorb`, in either order. -/
def PartMid (Ctx St W SP : Addr) (R P₀ : Nat) (D : Addr) (j k : Nat) (s : State) : Prop :=
  Env Ctx St W SP s ∧ RoundsAt s.mem W R ∧ DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- `PartMid` with the registers the parts start from. -/
abbrev PartIn (Ctx St W SP : Addr) (R P₀ : Nat) (D : Addr) (j k : Nat) (s : State) : Prop :=
  PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
    s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)

omit L in
theorem PartPre.mid {enc : Bool} {j k : Nat} {s : State} (h : PartPre M Ctx St W SP R P₀ enc D n j k s) :
    PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  exact ⟨⟨I.env, I.rounds K, (I.data.drop I.le).take (by have := I.le; omega_arith), hdat, hlen, htl⟩, h12, hbp, hbx⟩

omit L in
theorem PartMid.crIn {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    CrIn Ctx St W SP R 0 (P₀ + j) (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.1, h.1.2.1⟩

omit L in
theorem PartMid.absIn {j k : Nat} {s : State}
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    AbsIn Ctx St W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (List.replicate (P₀ + j) 0)
      (D + BitVec.ofNat 64 j) k s :=
  ⟨h.1.1, h.2.1, h.2.2.1, by rw [List.length_replicate]; exact h.2.2.2, h.1.2.2.1.ok, rfl⟩

omit L in
/-- The data reloaded. -/
theorem partMid_load {j k : Nat} {s : State} (h : PartMid Ctx St W SP R P₀ D j k s) :
    WP isa (.block streamLoad) s fun s' => PartMid Ctx St W SP R P₀ D j k s' ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 j ∧ s'.gpr .rbp = BitVec.ofNat 64 k ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16) := by
  obtain ⟨he, hR, hd, hdat, hlen, htl⟩ := h
  obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok he hdat hlen htl
  rw [toNat_mod16] at hbx
  exact WP.of_runBlock ⟨s', run, ⟨he.keep (load_env hg) hrd hwr, hm ▸ hR, hd.of_eq hrd hwr, hm ▸ hdat, hm ▸ hlen,
    hm ▸ htl⟩, h12, hbp, hbx⟩

/-- After `cr`, which does what `crypt` does. -/
theorem partMid_crypt {cr : Prog isa} {j k : Nat} {s : State}
    (hcr : ∀ {t : State}, CrIn Ctx St W SP R 0 (P₀ + j) (D + BitVec.ofNat 64 j) k t →
      WP isa cr t (CrOut Ctx St W SP R 0 (P₀ + j) (D + BitVec.ofNat 64 j) k t.mem))
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa cr s (PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (hcr (PartMid.crIn h))) fun s' ⟨co, hrd, hwr⟩ => ?_
  obtain sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd.ok h₁ (by omega_arith))
      (by decide)
  exact ⟨co.env, co.rounds, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

/-- After `ab`, which does what `absorb` does. -/
theorem partMid_absorb {ab : Prog isa} {j k : Nat} {s : State}
    (hab : ∀ {H : Block} {t : State}, AbsIn Ctx St W SP 16 H (List.replicate (P₀ + j) 0) (D + BitVec.ofNat 64 j) k t →
      WP isa ab t (AbsOut Ctx St W SP 16 H (List.replicate (P₀ + j) 0)
        (List.replicate (P₀ + j) 0 ++ bytesAt t.mem (D + BitVec.ofNat 64 j) k) t.mem))
    (h : PartMid Ctx St W SP R P₀ D j k s ∧ s.gpr .r12 = D + BitVec.ofNat 64 j ∧ s.gpr .rbp = BitVec.ofNat 64 k ∧
      s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16)) :
    WP isa ab s (PartMid Ctx St W SP R P₀ D j k) := by
  have hd := h.1.2.2.1
  refine WP.mono (WP.with_rdwr (hab (PartMid.absIn h))) fun s' ⟨ao, hrd, hwr⟩ => ?_
  obtain sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega_arith))
      (by decide)
  exact ⟨ao.env, rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) h.1.2.1, hd.of_eq hrd hwr,
    by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2.2⟩

omit L in
/-- `cr` and `ab` over the same part of the data in both runs, for any `cr`
and `ab` that do what `crypt` and `absorb` do, and leak only what the
registers they start from fix. -/
theorem partWith_rel (enc : Bool) {cr ab : Prog isa} {j k : Nat}
    (crR : RelCT isa (fun s₁ s₂ => PartIn Ctx St W SP R P₀ D j k s₁ ∧ PartIn Ctx St W SP R P₀ D j k s₂) cr
      fun _ _ => True)
    (abR : RelCT isa (fun s₁ s₂ => PartIn Ctx St W SP R P₀ D j k s₁ ∧ PartIn Ctx St W SP R P₀ D j k s₂) ab
      fun _ _ => True)
    (crW : ∀ s, PartIn Ctx St W SP R P₀ D j k s → WP isa cr s (PartMid Ctx St W SP R P₀ D j k))
    (abW : ∀ s, PartIn Ctx St W SP R P₀ D j k s → WP isa ab s (PartMid Ctx St W SP R P₀ D j k)) :
    RelCT isa (fun s₁ s₂ => PartPre M Ctx St W SP R P₀ enc D n j k s₁ ∧ PartPre M Ctx St W SP R P₀ enc D n j k s₂)
      (partWith enc cr ab) fun _ _ => True := by
  obtain ld := rel_both (rel_envT (F := PartMid Ctx St W SP R P₀ D j k) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partMid_load h) (fun _ h => partMid_load h)
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    exact (RelCT.seq (rel_both abR abW abW) (RelCT.seq ld crR)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩)
      fun _ _ h => h
  · simp only [partWith, ↓reduceIte]
    exact (RelCT.seq (rel_both crR crW crW) (RelCT.seq ld abR)).mono (fun _ _ h => ⟨h.1.mid, h.2.mid⟩)
      fun _ _ h => h

omit L in
/-- The registers the parts start from agree. -/
theorem PartIn.agree {j k : Nat} {s₁ s₂ : State} (h₁ : PartIn Ctx St W SP R P₀ D j k s₁)
    (h₂ : PartIn Ctx St W SP R P₀ D j k s₂) : ∀ r ∈ absRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · rw [h₁.1.1.r13, h₂.1.1.r13]
  · rw [h₁.1.1.r14, h₂.1.1.r14]
  · rw [h₁.1.1.r15, h₂.1.1.r15]
  · rw [h₁.1.1.rsp, h₂.1.1.rsp]

/-- `crypt` and `absorb` over the same part of the data in both runs. -/
theorem part_rel (enc : Bool) {j k : Nat} :
    RelCT isa (fun s₁ s₂ => PartPre M Ctx St W SP R P₀ enc D n j k s₁ ∧ PartPre M Ctx St W SP R P₀ enc D n j k s₂)
      (partWith enc (crypt v.callees) (absorb v.callees 16)) fun _ _ => True :=
  partWith_rel enc
    ((crypt_rel v L (icb₁ := 0) (icb₂ := 0) rfl).mono (fun _ _ h => ⟨PartMid.crIn h.1, PartMid.crIn h.2⟩)
      fun _ _ h => h)
    ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => absorb_rel v L (yo := 16) (.inr rfl) (H₁ := H₁) (H₂ := H₂)
      (x₁ := List.replicate (P₀ + j) 0) (x₂ := List.replicate (P₀ + j) 0) rfl).mono
      (fun _ _ h => ⟨_, _, PartMid.absIn h.1, PartMid.absIn h.2⟩) fun _ _ h => h)
    (fun _ h => partMid_crypt L (crypt_ok v L) h) (fun _ h => partMid_absorb L (absorb_ok v L (.inr rfl)) h)

/-- The head in both runs: `cryptHead` and `absorbHead`, for a head within
the rest of the block the text so far left partial. -/
theorem headPart_rel (enc : Bool) {k : Nat} (hk0 : k ≠ 0) (hP : P₀ % 16 ≠ 0) (hle : k ≤ 16 - P₀ % 16) :
    RelCT isa (fun s₁ s₂ => PartPre M Ctx St W SP R P₀ enc D n 0 k s₁ ∧ PartPre M Ctx St W SP R P₀ enc D n 0 k s₂)
      (partWith enc cryptHead (absorbHead v.callees 16)) fun _ _ => True :=
  partWith_rel enc
    (rel_taint absRegs (fun _ _ h => PartIn.agree h.1 h.2) ⟨_, by taint_decide⟩)
    ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => head_rel v L (yo := 16) (.inr rfl) (H₁ := H₁) (H₂ := H₂)
      (x₁ := List.replicate (P₀ + 0) 0) (x₂ := List.replicate (P₀ + 0) 0) rfl).mono
      (fun _ _ h => ⟨_, _, PartMid.absIn h.1, PartMid.absIn h.2⟩) fun _ _ h => h)
    (fun _ h => partMid_crypt L (fun hc => cryptHead_out hc hk0 (by rwa [Nat.add_zero]) (by rwa [Nat.add_zero])) h)
    (fun _ h => partMid_absorb L (fun ha => absorbHead_out v L (.inr rfl) ha hk0
      (by rw [List.length_replicate, Nat.add_zero]; exact hP) (by rw [List.length_replicate, Nat.add_zero]; exact hle)) h)

end

/-! ## The whole blocks -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R P₀ : Nat} {D : Addr} {n : Nat}
include L

theorem callBlocks_rel (enc : Bool) {D' : Addr} {n' q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn M Ctx St W SP R D' n' q s₁ ∧ ObIn M Ctx St W SP R D' n' q s₂)
      (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
        (if enc then B.enc else B.dec).code) (.pop .rax 1)) fun _ _ => True := by
  cases enc
  · exact obFrameD_rel B L
  · exact obFrameE_rel B L

/-- Before `streamBlocks`: what `blocks_ok` needs. -/
def BPre (M : Gcm.X86_64.Stitch.CtxMode) (Ctx St W SP : Addr) (R P₀ : Nat) (enc : Bool) (D : Addr) (n j : Nat) (s : State) : Prop :=
  SI M Ctx St W SP R P₀ enc D n j s ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)

/-- `streamBlocks`, with the same number of whole blocks, at the same
address, in both runs. -/
theorem blocks_rel (enc : Bool) {j : Nat} :
    RelCT isa (fun s₁ s₂ => BPre M Ctx St W SP R P₀ enc D n j s₁ ∧ BPre M Ctx St W SP R P₀ enc D n j s₂)
      (streamBlocks (if enc then B.enc else B.dec)) fun _ _ => True := by
  -- After the number of whole blocks: what the call's arguments need.
  let G₁ : State → Prop := fun s => s.zf = some (decide ((n - j) / 16 = 0)) ∧ Env Ctx St W SP s ∧
    ((n - j) / 16 ≠ 0 → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)))
  obtain g₁ : ∀ s, BPre M Ctx St W SP R P₀ enc D n j s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) s G₁ := fun s h => by
    obtain ⟨⟨H, icb, x₀, m₀, K, hx, I⟩, hdat, hlen, htl⟩ := h
    have hlt := I.data.ok.lt
    have hj := I.le
    refine WP.mono (sb1_ok (L := n - j) (by omega_arith) I.env hlen) fun s₁ ⟨r₁, z₁, g, m₁, rd₁, wr₁⟩ => ⟨z₁, ?_, fun hz => ?_⟩
    · exact I.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    obtain he₁ : Env Ctx St W SP s₁ := I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd₁ wr₁
    refine WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ (m₁ ▸ I.rounds K) (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
    obtain he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    exact ⟨he₂, (I.data.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega_arith, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega_arith)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s,
      (I.ext K).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁) (m₂.trans m₁)⟩
  obtain a := rel_both (rel_envT (F := BPre M Ctx St W SP R P₀ enc D n j) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) g₁ g₁
  obtain hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block (([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++
      ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++
      ptr .rax .r15 bScrO)) s (ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16)) :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  obtain b := rel_both (rel_envT (F := fun s => G₁ s ∧ s.zf = some false) [] (fun _ h => h.1.2.1)
    (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩) hw₂ hw₂
  obtain hw₃ : ∀ s, ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) ((n - j) / 16) s →
      WP isa (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
        (if enc then B.enc else B.dec).code) (.pop .rax 1)) s (Env Ctx St W SP) := fun s h =>
    WP.mono (callBlocks_ok B L enc h) fun _ o => h.env.of_saved o.1 o.2.1 o.2.2.1
  obtain c := rel_both (callBlocks_rel B L enc) hw₃ hw₃
  obtain d := rel_envT (F := Env Ctx St W SP) (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax),
      .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx),
      .mov .rcx (.mem (at_ .r15 dataO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx,
      .mov .rcx (.mem (at_ .r15 tlenO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx])
    [] (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩
  unfold streamBlocks
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  exact (RelCT.seq b (RelCT.seq c d)).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩)
    fun _ _ h => h

end

/-! ## The start -/

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N : Nat} (L : Lay Ctx St W SP N)
include L

omit L in
/-- Whether there is text yet. -/
theorem tl_ok {P : Nat} (hP : P < 2 ^ 64) {s : State} (he : Env Ctx St W SP s N)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P)
    (hN : 200 ≤ N := by decide) (hNl : N < 2 ^ 64 := by decide) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s fun s' =>
      s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' N ∧ s'.mem = s.mem := by
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ N by omega_using [hN]) (hk := hNl)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (P = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₂, run₂, hz₂, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂, hm₂⟩

omit L in
/-- The length of the additional data modulo 16. -/
theorem al_ok {aL : Nat} {s : State} (he : Env Ctx St W SP s N)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL)
    (hN : 200 ≤ N := by decide) (hNl : N < 2 ^ 64 := by decide) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s' N := by
  obtain r₃ := he.perm.wR (show 184 + 8 ≤ N by omega_using [hN]) (hk := hNl)
  obtain hand := and15 (BitVec.ofNat 64 aL)
  rw [imm_eq (by decide), toNat_mod16] at hand
  obtain ⟨s₃, run₃, hbx₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)] s = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧
      (∀ r, r ≠ .rbx → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₃], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hal, hand]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  exact WP.of_runBlock ⟨s₃, run₃, hbx₃, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃⟩

/-- The additional data padded if there is no text yet, in both runs. -/
theorem start_rel {aL P : Nat} (hP : P < 2 ^ 64) {F : State → Prop} (hF : ∀ s, F s → Env Ctx St W SP s N ∧
      s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P ∧
      s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) {gs : Nat} [GhFits v N gs]
    (hN : 200 ≤ N := by decide) (hNl : N < 2 ^ 64 := by decide) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) fun _ _ => True := by
  let G : State → Prop := fun s' => s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' N ∧
    s'.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  obtain g : ∀ s, F s → WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s G :=
    fun s h => WP.mono (tl_ok hP (hF s h).1 (hF s h).2.1 hN hNl) fun s' ⟨z, e, m⟩ => ⟨z, e, by rw [m]; exact (hF s h).2.2⟩
  obtain a := rel_both (rel_envT (F := F) [] (fun s h => (hF s h).1) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g g
  obtain b := rel_both (rel_envT (F := fun s => G s ∧ s.zf = some true) [] (fun _ h => h.1.2.1)
      (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
    (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl) (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl)
  obtain c := (flush_rel v L (yo := 16) (.inr rfl)).mono (P' := fun (s₁ s₂ : State) =>
      (s₁.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₁ N) ∧
      (s₂.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₂ N))
    (fun _ _ h => ⟨h.1.2, h.2.2, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]⟩) fun _ _ h => h
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) ?_ (RelCT.block_nil fun _ _ _ => trivial))
  unfold firstFlush
  exact (RelCT.seq b c).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

/-! ## All of `streamText` -/

/-- Before `streamText`: what the entry leaves, in each run. -/
structure TPre (M : Gcm.X86_64.Stitch.CtxMode) (Ctx St W SP : Addr) (R aL P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  K : SCtx M Ctx St W SP R (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) D n s.mem
  hP : P₀ < 2 ^ 64
  cov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R aL P₀ : Nat} {D : Addr} {n : Nat}

/-- What `part_ok` does to `PartPre`. -/
theorem si_part (enc : Bool) {j k : Nat} {s : State} (h : PartPre M Ctx St W SP R P₀ enc D n j k s) :
    WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s fun s' =>
      SI M Ctx St W SP R P₀ enc D n (j + k) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  let ⟨hs, hk, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  hs.lift fun K hx I => part_ok v K enc I hx hk h12 hbp hbx hdat hlen htl

/-- What `headPart_ok` does to `PartPre`. -/
theorem si_head (enc : Bool) {s : State} (h : PartPre M Ctx St W SP R P₀ enc D n 0 (headLen P₀ n) s) (hn : n ≠ 0) :
    WP isa (headPart v.callees enc) s fun s' =>
      SI M Ctx St W SP R P₀ enc D n (0 + headLen P₀ n) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  let ⟨hs, _, h12, hbp, hbx, hdat, hlen, htl⟩ := h
  hs.lift fun K hx I => headPart_ok v K enc I hx hn h12 hbp hbx hdat hlen htl

include L in
/-- `streamText` in two runs, with the same data and lengths. -/
theorem streamText_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre M Ctx St W SP R aL P₀ D n s₁ ∧ TPre M Ctx St W SP R aL P₀ D n s₂)
      (streamText (v.withBlk B) enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : headLen P₀ n = k
  obtain hkw := headLen_whole P₀ n
  obtain hkn := headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre M Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  obtain g₁ : ∀ s, TPre M Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP, by rw [hrd, hwr]; exact h.cov⟩, hz⟩
  obtain a := rel_both (rel_envT (F := TPre M Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  obtain g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (start_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data t.cov (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega_arith
  obtain b := rel_both (start_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  obtain g₃ : ∀ s, G₂ s → WP isa (.block streamLoad) s G₃ := fun s h => by
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok h.1.env h.2.1 h.2.2.1 h.2.2.2
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, h.1.regs (load_env hg) hm hrd hwr, h12, hbp, hbx, hm ▸ h.2.1, hm ▸ h.2.2.1,
      hm ▸ h.2.2.2⟩
  obtain c := rel_both (rel_envT (F := G₂) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₃ g₃
  -- Fewer than 256 bytes, or more.
  obtain g₃s : ∀ s, G₃ s → WP isa (.block streamSmall) s fun s' => G₃ s' ∧ s'.cf = some (decide (n < 256)) :=
    fun s h => by
      obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
      obtain hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
      obtain ⟨s', run, hcf, hg, hm, hrd, hwr⟩ := small_ok s hbp hlt
      exact WP.of_runBlock ⟨s', run, ⟨hs.regs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hm hrd hwr,
        by rw [hg .r12 (by decide)]; exact h12, by rw [hg .rbp (by decide)]; exact hbp,
        by rw [hg .rbx (by decide)]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hcf⟩
  obtain cs := rel_both (rel_envT (F := G₃) [.rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₃s g₃s
  obtain pp : ∀ s, G₃ s → PartPre M Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega_arith, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  obtain gsm : ∀ s, PartPre M Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  -- The head's length.
  let G₄ : State → Prop := fun s => PartPre M Ctx St W SP R P₀ enc D n 0 k s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  obtain g₄ : ∀ s, G₃ s → WP isa streamHead s G₄ := fun s h => by
    obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
    obtain hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    refine WP.mono (sHead_ok hs.env hlt hbx hbp) fun s' ⟨hbp', hg, hl, ha, f, hrd, hwr⟩ => ?_
    rw [hk] at hbp' hl
    obtain rd : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide)
    refine ⟨⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (by decide) (by decide) f,
      by omega_arith, by simp [hg .r12 (by decide) (by decide), h12], hbp',
      by rw [hg .rbx (by decide) (by decide), hbx, Nat.add_zero], by rw [rd 200 (by decide) (by decide), hdat]; simp, hl,
      by rw [rd 192 (by decide) (by decide), htl, Nat.add_zero]⟩, ha⟩
  obtain d := rel_both (rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₄ g₄
  -- The head.
  let G₅ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n k s ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀ ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  obtain g₅ : n ≠ 0 → ∀ s, G₄ s → WP isa (headPart v.callees enc) s G₅ := fun hn s h => by
    obtain ⟨hp, ha⟩ := h
    have ⟨_, _, _, _, _, hdat, hlen, htl⟩ := hp
    subst hk
    refine WP.mono (si_head v enc hp hn) fun s' ⟨hs, sl⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.zero_add] at hs; exact hs
    · rw [sl 208 (by decide) (by decide)]; exact hlen
    · rw [sl 200 (by decide) (by decide), hdat]; simp
    · rw [sl 192 (by decide) (by decide), htl, Nat.add_zero]
    · rw [sl 216 (by decide) (by decide)]; exact ha
  -- Whether the text so far left a block partial: the head, by `cryptHead` and `absorbHead`, if so.
  let T₄ : State → Prop := fun s => G₄ s ∧ s.zf = some (decide (P₀ % 16 = 0))
  obtain g₄t : ∀ s, G₄ s → WP isa (.block [.alu .test .rbx (.reg .rbx)]) s T₄ := fun s h => by
    obtain ⟨⟨hs, hk', h12, hbp, hbx, hdat, hlen, htl⟩, ha⟩ := h
    obtain hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbx hbx (by omega_arith)
    rw [Nat.add_zero] at hz
    exact WP.of_runBlock ⟨s', run, ⟨⟨hs.regs (fun r _ => by rw [hg]) hm hrd hwr, hk', by rw [hg]; exact h12,
      by rw [hg]; exact hbp, by rw [hg]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hm ▸ ha⟩, hz⟩
  obtain e₁ := rel_both (rel_envT (F := G₄) [.rbx] (fun _ h => h.1.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]) ⟨_, by taint_decide⟩) g₄t g₄t
  obtain e : n ≠ 0 → RelCT isa (fun s₁ s₂ => G₄ s₁ ∧ G₄ s₂) (headPart v.callees enc) fun s₁ s₂ => G₅ s₁ ∧ G₅ s₂ :=
    fun hn => by
    refine rel_both (RelCT.seq e₁ (rel_ite_e (fun _ _ h => h.1.2.trans h.2.2.symm)
      (RelCT.block_nil fun _ _ _ => trivial) ?_)) (g₅ hn) (g₅ hn)
    by_cases hz : P₀ % 16 = 0
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hz] at this
    obtain e' : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, hz]
    rw [hk] at e'
    exact (headPart_rel v L enc (k := k) (by omega_arith) hz (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩)
      fun _ _ h => h
  -- Past the head.
  obtain g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (BPre M Ctx St W SP R P₀ enc D n k) := fun s h => by
    obtain ⟨hs, hl, hdat, htl, ha⟩ := h
    obtain hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    exact WP.mono (next_ok hs.env hkn hlt hl hdat htl ha) fun s' ⟨hg, d', t', l', f, hrd, hwr⟩ =>
      ⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (Nat.le_refl _)
        (by decide) f, d', l', t'⟩
  obtain f := rel_both (rel_envT (F := G₅) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₆ g₆
  -- The whole blocks.
  let G₇ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  obtain g₇ : ∀ s, BPre M Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then B.enc
      else B.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (blocks_ok B K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega_arith)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  obtain g := rel_both (blocks_rel B L enc) g₇ g₇
  -- The rest.
  obtain g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (load_env hg) hm hrd hwr, by omega_arith, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  obtain i := rel_both (rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  obtain g₉ : ∀ s, PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  obtain j := rel_both (part_rel v L enc) g₉ g₉
  simp only [streamText]
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  by_cases hs : n < 256
  · -- All of it is the rest.
    refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs (RelCT.seq
      (RelCT.ite (M := isa) (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelCT.block_nil fun _ _ h => ⟨pp _ h.1.1.1, pp _ h.1.2.1⟩)
        (RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this))
      (rel_both (part_rel v L enc (j := 0) (k := n)) gsm gsm))))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)
  · -- The head and the whole blocks first.
    refine rel_reassoc2 ((RelCT.seq b (RelCT.seq c (RelCT.seq cs (RelCT.seq
      (RelCT.ite (M := isa) (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this)
        ((RelCT.seq d (RelCT.seq (e (by omega_arith)) (RelCT.seq f (RelCT.seq g i)))).mono
          (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))
      j)))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)

end

/-! ## The functions -/

/-- After the entry, what `streamText` needs. -/
theorem cryptEntry_tpre {M : Gcm.X86_64.Stitch.CtxMode} {s : State} (hp : Proof.AesGcm.streamCryptPre M.len s)
    (hok : M.ok s.mem (s.gpr .rdi)) :
    WP isa (.block cryptEntry) s (TPre M (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat) := by
  obtain C := CryptCtx.of hp M.ge
  obtain X := CtxExt.ofCrypt hp hok
  refine WP.mono (cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.ww C.args C.dA C.rounds) fun s₁ E => ?_
  exact ⟨E.env, C.data.of_eq E.rd E.wr, E.rbp, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.tlen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    ⟨C.lay, E.rounds, rfl, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw, X.cd, X.ct,
      M.frame E.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩,
    (s.gpr .r8).isLt, by rw [E.rd, E.wr]; exact X.cov⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem stream_rel (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s₀) (hok : M.ok s₀.mem (s₀.gpr .rdi))
    (hp' : Proof.AesGcm.streamCryptPre M.len s₀') (hok' : M.ok s₀'.mem (s₀'.gpr .rdi))
    (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamText (v.withBlk B) enc) (.block restore))) fun _ _ => True := by
  obtain L := (CryptCtx.of hp M.ge).lay
  obtain hE₂ := cryptEntry_tpre hp' hok'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  obtain hE₁ := cryptEntry_tpre hp hok
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp M.ge).args.2 (CryptCtx.of hp' M.ge).args.2 ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamText_rel v B L enc (s₀.gpr .r8).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncryptM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptX86_64M M).pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncrypt (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v B true hp.1 hp.2 hp'.1 hp'.2 hq

theorem streamDecryptM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamDecryptX86_64M M).pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecrypt (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v B false hp.1 hp.2 hp'.1 hp'.2 hq

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamEncryptX86_64.pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v v.blkB true hp trivial hp' trivial hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamDecryptX86_64.pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v v.blkB false hp trivial hp' trivial hq

end VG.Proof.AesGcm.X86_64
