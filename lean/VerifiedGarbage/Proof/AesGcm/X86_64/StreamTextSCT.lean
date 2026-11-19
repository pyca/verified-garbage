module

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
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
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamClr
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.AesGcm.X86_64.StreamClr
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcm.X86_64.StreamTextS`, which this module and modules that import it used -/

section

/-!
# AES-GCM on x86-64: the text of `stream_encrypt`, padding in the state

Untrusted: everything here is checked by Lean. `streamTextS` is
`streamText` with the additional data padded in the state's keystream block
(`flushS`), which holds nothing before the first text, rather than in `T`:
`flushS_ok`, `startS_ok` and `streamTextS_ok` are `flush_ok`, `start_ok`
and `streamText_ok` with that block in the frame in `T`'s place.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashInput ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- The regions `flushS` writes. -/
abbrev sFrame (St W SP : Addr) (yo : Nat) (gs : Nat := 256) : List Region :=
  [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨St + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 512, gs⟩, below SP 8]

theorem gh_sFrame {St W SP : Addr} {yo gs : Nat} {m m' : Mem}
    (h : Frame [⟨St + BitVec.ofNat 64 yo, 16⟩, ⟨W + BitVec.ofNat 64 512, gs⟩, below SP 8] m m') :
    Frame (sFrame St W SP yo gs) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem sFrame_st {St W SP D : Addr} {n : Nat} {t : Bool} {m m' : Mem} (hf : Frame (sFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n t) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

/-- After `flushS yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOutS (Ctx St W SP : Addr) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) (N : Nat := 2560)
    (gs : Nat := 256) : Prop where
  env : Env Ctx St W SP s N
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (St + BitVec.ofNat 64 yo) (St + BitVec.ofNat 64 32) H x
  frame : Frame (sFrame St W SP yo gs) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N gs : Nat} [G : GhFits v N gs] (L : Lay Ctx St W SP N) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include G L hyo

/-- `flushS yo`: `flush yo`, padding in the state's keystream block. -/
theorem flushS_ok {H : Block} {x : List Byte} {s : State} (h : FlIn Ctx St W SP yo H x s N)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 (x.length % 16)) :
    WP isa (flushS v.callees yo) s (FlOutS Ctx St W SP yo H x (x ++ zeros (padLen x.length)) s.mem · N gs) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hzf, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbx hbx (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ N := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hcx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        ([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax] ++
          ptr .rdi .r14 64 ++ ptr .rsi .r14 32 ++ [.mov .rcx (.reg .rbx)]) s₁ = some s₂ ∧
        s₂.mem = (s.mem.writeW (St + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
          (St + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        s₂.gpr .rdi = St + BitVec.ofNat 64 64 ∧ s₂.gpr .rsi = St + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (x.length % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr := by
      have w₁ := in_off he₁.perm.st (show 64 + 8 ≤ 80 by decide) (by decide)
      have w₂ := in_off he₁.perm.st (show 72 + 8 ≤ 80 by decide) (by decide)
      refine ⟨_, by xrun [h14, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, add_ofNat_assoc, hm₁]; rfl
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, h14]
      · simp [gpr_setReg, hg₁, hbx]
      · intro r a b c d; simp [gpr_setReg, a, b, c, d, hg₁]
      · simp [rd_setReg, rd_arithFlags, hrd₁]
      · simp [wr_setReg, wr_arithFlags, hwr₁]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ N := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hrd₂ hwr₂
    have lp : LoopPre s₂ (St + BitVec.ofNat 64 32) (St + BitVec.ofNat 64 64) (x.length % 16) :=
      ⟨hsi, hdi, hcx, by omega_arith, by omega_arith, covers_left (he₂.perm.stC (by omega_arith)),
        he₂.perm.stC (by omega_arith), L.st_st (.inl (by omega_arith)) (by omega_arith) (by omega_arith)⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have he₃ : Env Ctx St W SP s₃ N := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- The memory so far.
    have fz : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact zeroT_frame _ _
    have hB₂ : bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16) =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) :=
      bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (.inl (by omega_arith)) (by omega_arith) (by decide))
        (by omega_arith)
    have hlen := length_bytesAt s₂.mem (St + BitVec.ofNat 64 32) (x.length % 16)
    have fc : Frame [⟨St + BitVec.ofNat 64 64, x.length % 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    have f₃ : Frame [⟨St + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem :=
      fz.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
    have hT : bytesAt s₃.mem (St + BitVec.ofNat 64 64) 16 =
        bytesAt s.mem (St + BitVec.ofNat 64 32) (x.length % 16) ++ zeros (16 - x.length % 16) := by
      rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₂]
      refine congrArg (_ ++ ·) ?_
      have := zeroT_bytes s.mem (St + BitVec.ofNat 64 64)
      rw [← hm₂, show (16 : Nat) = x.length % 16 + (16 - x.length % 16) by omega_arith, bytesAt_add] at this
      have e := congrArg (List.drop (x.length % 16)) this
      rw [List.drop_left' (length_bytesAt _ _ _)] at e
      rw [e, show x.length % 16 + (16 - x.length % 16) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
      rfl
    have hY₃ : blockAt s₃.mem (St + BitVec.ofNat 64 yo) = blockAt s.mem (St + BitVec.ofNat 64 yo) :=
      blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
    refine WP.mono (ghash1_ok v L hyo he₃ .r14 64 (.inl rfl) (P := St + BitVec.ofNat 64 64) (by rw [he₃.r14])
      (by decide) (L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)) (L.st_gh G.fit (by decide))
      (L.stk_st (by decide)) (covers_left (he₃.perm.stC (by decide)))) fun s₄ g => ?_
    refine ⟨g.env he₃, ?_, ?_, ?_⟩
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega_arith)
        · exact L.ctx_gh G.fit (by decide)
        · exact (L.stk_ctx (by decide)).symm), hH₃]
    · intro ha
      refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s₃.mem (St + BitVec.ofNat 64 64) 16) hT ?_
      rw [g.out, hY₃, hH₃]; rfl
    · refine (f₃.sub fun r hr => ?_).trans (gh_sFrame g.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- The additional data padded, if there is no text yet: then `SInv` holds,
with nothing done. -/
theorem startS_ok (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State} (he : Env Ctx St W SP s)
    (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n) (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s fun s' =>
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s' false ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  have L := K.lay
  have hlt := hd.ok.lt
  obtain r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (c₀.length = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  obtain hm₂' : s₂.mem = m₀ := hm₂.trans hm
  have hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H := K.hH
  obtain dD : ∀ r ∈ sFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hd.ok.st.sub_right (Lay.stSub (by decide))
    · exact hd.ok.st.sub_right (Lay.stSub (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · exact hd.ok.stk.symm
  obtain cT : ∀ r ∈ sFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.st_st (.inr (by decide)) (by decide) (by decide)
    · exact L.st_st (.inl (by decide)) (by decide) (by decide)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by decide)).symm
  obtain sT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ sFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
    · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact (L.stk_w (by omega_arith)).symm
  -- From a state with the padded additional data absorbed.
  obtain fin : ∀ s₄ : State, Env Ctx St W SP s₄ → s₄.rd = s.rd → s₄.wr = s.wr → Frame (sFrame St W SP 16) m₀ s₄.mem →
      (Hyp → Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length) ++ c₀)) →
      (Hyp → Ctr s₄.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) →
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s₄ false ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun s₄ he₄ rd₄ wr₄ f₄ ha hc => ⟨⟨he₄, hd.of_eq rd₄ wr₄, Nat.zero_le _, sFrame_st f₄,
      by simpa using bytesAt_frame f₄ dD (by omega_arith),
      fun hy => by simpa [bytesAt_zero, ctext_nil] using ha hy,
      fun hy => by simpa using hc hy, fun _ => rfl, by rw [rd₄, wr₄]; exact hcov⟩,
      fun d h₁ h₂ => by
        rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (sT d h₁ (by omega_arith)) (by decide), hm]⟩
  refine WP.ite (decide (c₀.length = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_)
  · have hc : c₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
    subst hc
    obtain r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
    obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
        (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
      obtain hand := and15 (BitVec.ofNat 64 a.length)
      rw [imm_eq (by decide), toNat_mod16] at hand
      refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    unfold firstFlushS
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    obtain he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    obtain hm₃' : s₃.mem = m₀ := hm₃.trans hm₂'
    refine WP.mono (WP.with_rdwr (flushS_ok v L (yo := 16) (.inr rfl) (H := H) (x := a) ⟨he₃, by rw [hm₃']; exact hH⟩
      hbx₃)) fun s₄ ⟨fo, rd₄, wr₄⟩ => fin s₄ fo.env (by rw [rd₄, hrd₃, hrd₂]) (by rw [wr₄, hwr₃, hwr₂])
        (hm₃' ▸ fo.frame) (fun hy => ?_) fun hy => ?_
    · rw [List.append_nil]
      exact fo.abs (by rw [hm₃']; exact hyA hy)
    · -- No text yet: the keystream block holds nothing, and the counter block is as it was.
      obtain ⟨h₁, -⟩ := hyC hy
      refine ⟨?_, fun h => absurd rfl h⟩
      rw [blockAt_frame (hm₃' ▸ fo.frame) cT]
      exact h₁
  · have hc : c₀ ≠ [] := fun e => by subst e; simp_all
    refine WP.block_nil (fin s₂ he₂ hrd₂ hwr₂ (by rw [hm₂']; exact Frame.refl _ _) (fun hy => ?_)
      fun hy => by rw [hm₂']; exact hyC hy)
    rw [hm₂', ← Proof.Gcm.ghashInput_of_ne hc]
    exact hyA hy

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamTextS enc`: as `streamText_ok`, the `n` bytes at `D` encrypted (`enc`) or decrypted,
and their ciphertext absorbed, after additional data `a` and text `c₀`. -/
theorem streamTextS_ok (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n)
    (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamTextS (v.withBlk B) enc) s fun s' => Env Ctx St W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (stFrame St W SP D n false) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := by
  suffices WP isa (streamTextS (v.withBlk B) enc) s fun s' => Env Ctx St W SP s' ∧ Frame (stFrame St W SP D n false) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) from
    WP.mono (WP.with_rdwr this) fun _ ⟨⟨a, b, c⟩, d, e⟩ => ⟨a, d, e, b, c⟩
  have hlt := hd.ok.lt
  obtain hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega_arith
  simp only [streamTextS]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₁, by rw [hm₁, hm]; exact Frame.refl _ _, fun hy => ⟨?_, ?_, rfl⟩⟩
    · rw [bytesAt_zero, ctext_nil, List.append_nil, hm₁, hm]; exact hyA hy
    · rw [hm₁, hm]; exact hyC hy
  obtain h0 : n ≠ 0 := by simpa using hf
  obtain sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (startS_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁) (by rw [hrd₁, hwr₁]; exact hcov) (c₀ := c₀) hP
    (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC) fun s₂ ⟨I₂, sl₂⟩ => ?_))
  -- The head.
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  obtain I₃ := I₂.regs (load_env hg₃) hm₃ hrd₃ hwr₃
  obtain sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  -- The end, from `SInv` over all the data.
  obtain fin : ∀ s', SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ n s' false →
      Env Ctx St W SP s' ∧ Frame (stFrame St W SP D n false) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := fun s' I => by
    refine ⟨I.env, I.frame, fun hy => ⟨?_, I.ctr hy, I.out hy⟩⟩
    obtain hne : c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n) ≠ [] := fun e => h0 (by
      have := congrArg List.length e
      rw [List.length_append, length_ctext, length_bytesAt, List.length_nil] at this
      omega_arith)
    rw [Proof.Gcm.ghashInput_of_ne hne, ← List.append_assoc]
    exact I.abs hy
  -- Fewer than 256 bytes: all of them at once.
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  obtain I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  obtain h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  obtain hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  obtain hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  obtain sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  -- Where the rest starts: all of it if short, after the head and the whole blocks otherwise.
  refine WP.seq (WP.mono (Q := fun (s' : State) => ∃ j k', j + k' = n ∧
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ j s' false ∧
      s'.gpr .r12 = D + BitVec.ofNat 64 j ∧ s'.gpr .rbp = BitVec.ofNat 64 k' ∧
      s'.gpr .rbx = BitVec.ofNat 64 ((c₀.length + j) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k' ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (c₀.length + j))
    (WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => ?_) (fun _ => ?_)) fun s' ⟨j, k', hjk, I, h12, hbp, hbx, hd, hl, ht⟩ => ?_)
  · exact WP.block_nil ⟨0, n, by omega_arith, I₃', by simp [h12₃'], hbp₃', by rw [hbx₃', Nat.add_zero],
      by rw [sl₃' 200 (by decide) (by decide), hdat]; simp, by rw [sl₃' 208 (by decide) (by decide), hlen],
      by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero]⟩
  · -- The head.
    refine WP.seq (WP.mono (sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
    generalize hk : headLen c₀.length n = k at hbp₄ hl₄
    obtain hkn : k ≤ n := hk ▸ headLen_le c₀.length n
    obtain hkw := headLen_whole c₀.length n
    rw [hk] at hkw
    obtain g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
    obtain I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
    obtain sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact K.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by decide), sl₃' d h₁ (by omega_arith)]
    subst hk
    refine WP.seq (WP.mono (headPart_ok v K enc I₄ hx h0 (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
      hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
      (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero])) fun s₅ ⟨I₅, sl₅⟩ => ?_)
    generalize headLen c₀.length n = k at hkn hkw I₅ hl₄
    -- Past the head.
    refine WP.seq (WP.mono (next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
      (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
      (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
      (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
    obtain I₆ := I₅.slots K (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
    rw [Nat.zero_add] at I₆
    -- The whole blocks.
    refine WP.seq (WP.mono (blocks_ok B K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega_arith)))
      fun s₇ ⟨I₇, d₇, l₇, t₇⟩ => ?_)
    generalize hj₂ : k + 16 * ((n - k) / 16) = j₂ at I₇ d₇ t₇
    -- The rest.
    obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := load_ok I₇.env d₇ l₇ t₇
    rw [toNat_mod16] at hbx₈
    obtain I₈ := I₇.regs (load_env hg₈) hm₈ hrd₈ hwr₈
    exact WP.of_runBlock ⟨s₈, run₈, j₂, (n - k) % 16, by omega_arith, I₈, h12₈, hbp₈, hbx₈, by rw [hm₈]; exact d₇,
      by rw [hm₈]; exact l₇, by rw [hm₈]; exact t₇⟩
  -- The rest.
  refine WP.mono (part_ok v K enc I hx (j := j) (k := k') (by omega_arith) h12 hbp hbx hd hl ht) fun s'' ⟨I', _⟩ => ?_
  rw [hjk] at I'
  exact fin s'' I'

end

/-! ## The functions -/

open VG.Spec.Gcm (StreamRepr ctxH ctxCiph gctr inc32)

/-- One run of `stream_encrypt` (`enc`) or `stream_decrypt`, for the message
the state represents, with ciphertext `c₀` so far. -/
theorem streamTextS_run (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s) (hok : M.ok s.mem (s.gpr .rdi))
    {iv a c₀ : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = c₀.length) :
    WP isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s fun s' =>
      gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c₀ →
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a
          (c₀ ++ ctext enc ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) ∧
        bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
          xorKs ciph (inc32 (Spec.Gcm.j0 h iv)) c₀.length (bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)) := by
  have C := CryptCtx.of hp M.ge
  have X := CtxExt.ofCrypt hp hok
  have hR := C.rounds
  have hP : c₀.length < 2 ^ 64 := hT ▸ (s.gpr .r8).isLt
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx R = ciph
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (by decide))), ← hH, ctxH_eq]
  have hc₁ : ciphOf s₁.mem Ctx R = ciph := by rw [ciph_frame E.frame dCE hR, ← hciph]; rfl
  have K : SCtx M Ctx St W SP R H D n s₁.mem := ⟨L, hRo, hH₁, C.t_c, C.t_s, C.t_w, C.t_d, C.sp24, X.w, X.cs, X.cw,
    X.cd, X.ct, M.frame E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact X.cw.sub_right (Lay.wSub (by decide))) X.w X.ok⟩
  have eS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [entryR W], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have hyA : StreamRepr s.mem St ciph H iv a c₀ → Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀) :=
    fun hy => by
      rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hy
      exact abs_frame E.frame (eS (by decide)) hy.2.1
  have hyC : StreamRepr s.mem St ciph H iv a c₀ → Ctr s₁.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₁.mem Ctx R) icb
      c₀.length := fun hy => by
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hicb] at hy
    rw [hc₁]
    exact ctr_frame E.frame (eS (by decide)) hy.2.2
  have htl : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length := by
    rw [E.tlen, ← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (streamTextS_ok v B K enc E.env rfl (C.data.of_eq E.rd E.wr) (by rw [E.rd, E.wr]; exact X.cov) E.rbp hP (E.alen.trans hA) htl
    E.dat E.len hyA hyC) fun s₂ ⟨he₂, rd₂, wr₂, f₂, hq⟩ => ?_)
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ (w_stFrame L C.data.ok.w C.t_w (by decide) (by decide))
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (ret_stFrame C.rS C.rD C.rW), ret_kept E.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide)))]
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w) hsv₂ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hy => ?_⟩
  rw [hicb]
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide)))
    (by have := C.data.ok.lt; omega_using [hn])
  obtain ⟨qa, qc, qo⟩ := hq hy
  simp only [hc₁, hd₁] at qa qc qo
  refine ⟨?_, by rw [hm]; exact qo⟩
  have hj := hy
  rw [Proof.Gcm.streamRepr_iff] at hj ⊢
  rw [ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hm, hicb, List.length_append, length_ctext, length_bytesAt]
  refine ⟨?_, qa, qc⟩
  rw [← hj.1]
  have e : St = St + BitVec.ofNat 64 0 := (BitVec.add_zero St).symm
  rw [blockAt_frame f₂ (j0_stFrame L C.data.ok.st C.t_s), e]
  exact blockAt_frame E.frame (eS (by decide))

/-- `vg_aes_gcm_stream_encrypt`, for a key context of kind `M`. -/
theorem streamEncryptSM_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.streamEncryptX86_64M M).pre s) :
    WP isa (streamEncryptS (v.withBlk B)) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  have run : ∀ {iv a p : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      WP isa (streamEncryptS (v.withBlk B)) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) p) →
          let c := gctr ciph (inc32 (Spec.Gcm.j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = c.drop p.length) := fun {iv a p} hA hT =>
    WP.mono (streamTextS_run v B true hp.1 hp.2 (iv := iv) (c₀ := gctr (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (inc32 (Spec.Gcm.j0 (ctxH s.mem (s.gpr .rdi)) iv)) p) hA (by rw [hT, Proof.Gcm.length_gctr]))
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, ↓reduceIte, Proof.Gcm.length_gctr] at h₁ h₂
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (p := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a p hr hA hT => hq (iv, a, p) ⟨hA, hT⟩ hr⟩

/-- `vg_aes_gcm_stream_decrypt`, for a key context of kind `M`. -/
theorem streamDecryptSM_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.streamDecryptX86_64M M).pre s) :
    WP isa (streamDecryptS (v.withBlk B)) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  have run : ∀ {iv a c : List Byte}, s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      WP isa (streamDecryptS (v.withBlk B)) s fun s' => gprPreserved s s' ∧
        let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        let h := ctxH s.mem (s.gpr .rdi)
        (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
          let c' := c ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
          StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
            bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat =
              (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := fun {iv a c} hA hT =>
    WP.mono (streamTextS_run v B false hp.1 hp.2 (iv := iv) (c₀ := c) hA hT)
      fun s' ⟨hg, hq⟩ => ⟨hg, fun hr => by
        obtain ⟨h₁, h₂⟩ := hq hr
        simp only [ctext, Bool.false_eq_true, ↓reduceIte] at h₁
        dsimp only
        rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
        exact ⟨h₁, h₂⟩⟩
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (run (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (c := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (run (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64: `streamTextS` is constant time

Untrusted: everything here is checked by Lean. As `StreamCryptCT.lean` for
`streamText`: `flushS_rel`, `startS_rel`, `streamTextS_rel` and
`streamS_rel` are `flush_rel`, `start_rel`, `streamText_rel` and
`stream_rel` with the additional data padded in the state.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)

theorem gh1Check_r14_64 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : Gh1Check yo .r14 64 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N gs : Nat} [G : GhFits v N gs] (L : Lay Ctx St W SP N) {yo : Nat}
  (hyo : yo = 0 ∨ yo = 16)
include G L hyo

/-- `flushS yo`, with the same number of buffered bytes. -/
theorem flushS_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx] · · N) (flushS v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_regs ([.rbx] ++ [.r13, .r14, .r15, .rsp]) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine rel_reassoc2 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (rel_taint ([.rbx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1) ⟨_, by taint_decide⟩))
    ?_)
  refine (ghash1_rel v L hyo .r14 64 (.inl rfl) (by decide) (P := St + BitVec.ofNat 64 64)
    (L.st_st (.inl (by omega_using [hyo])) (by omega_using [hyo]) (by decide)) (L.st_gh G.fit (by decide))
    (L.stk_st (by decide)) (gh1Check_r14_64 hyo) (F₁ := (Env Ctx St W SP · N)) (F₂ := (Env Ctx St W SP · N))
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s N := hs.elim id id
  exact ⟨he, by rw [he.r14], covers_left (he.perm.stC (by decide))⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N : Nat} (L : Lay Ctx St W SP N)
include L

/-- The additional data padded if there is no text yet, in both runs. -/
theorem startS_rel {aL P : Nat} (hP : P < 2 ^ 64) {F : State → Prop} (hF : ∀ s, F s → Env Ctx St W SP s N ∧
      s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P ∧
      s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL) {gs : Nat} [GhFits v N gs]
    (hN : 200 ≤ N := by decide) (hNl : N < 2 ^ 64 := by decide) :
    RelCT isa (fun s₁ s₂ => F s₁ ∧ F s₂) (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) fun _ _ => True := by
  let G : State → Prop := fun s' => s'.zf = some (decide (P = 0)) ∧ Env Ctx St W SP s' N ∧
    s'.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  have g : ∀ s, F s → WP isa (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)]) s G :=
    fun s h => WP.mono (tl_ok hP (hF s h).1 (hF s h).2.1 hN hNl) fun s' ⟨z, e, m⟩ => ⟨z, e, by rw [m]; exact (hF s h).2.2⟩
  have a := rel_both (rel_envT (F := F) [] (fun s h => (hF s h).1) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g g
  have b := rel_both (rel_envT (F := fun s => G s ∧ s.zf = some true) [] (fun _ h => h.1.2.1)
      (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩)
    (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl) (fun s h => al_ok h.1.2.1 h.1.2.2 hN hNl)
  have c := (flushS_rel v L (yo := 16) (.inr rfl)).mono (P' := fun (s₁ s₂ : State) =>
      (s₁.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₁ N) ∧
      (s₂.gpr .rbx = BitVec.ofNat 64 (aL % 16) ∧ Env Ctx St W SP s₂ N))
    (fun _ _ h => ⟨h.1.2, h.2.2, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1, h.2.1]⟩) fun _ _ h => h
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) ?_ (RelCT.block_nil fun _ _ _ => trivial))
  unfold firstFlushS
  exact (RelCT.seq b c).mono (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R aL P₀ : Nat} {D : Addr} {n : Nat}

include L in
/-- `streamTextS` in two runs, with the same data and lengths. -/
theorem streamTextS_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre M Ctx St W SP R aL P₀ D n s₁ ∧ TPre M Ctx St W SP R aL P₀ D n s₂)
      (streamTextS (v.withBlk B) enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : headLen P₀ n = k
  have hkw := headLen_whole P₀ n
  have hkn := headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre M Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre M Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP, by rw [hrd, hwr]; exact h.cov⟩, hz⟩
  have a := rel_both (rel_envT (F := TPre M Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (startS_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data t.cov (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I.toT⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega_arith
  have b := rel_both (startS_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₃ : ∀ s, G₂ s → WP isa (.block streamLoad) s G₃ := fun s h => by
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok h.1.env h.2.1 h.2.2.1 h.2.2.2
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, h.1.regs (load_env hg) hm hrd hwr, h12, hbp, hbx, hm ▸ h.2.1, hm ▸ h.2.2.1,
      hm ▸ h.2.2.2⟩
  have c := rel_both (rel_envT (F := G₂) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₃ g₃
  -- Fewer than 256 bytes, or more.
  have g₃s : ∀ s, G₃ s → WP isa (.block streamSmall) s fun s' => G₃ s' ∧ s'.cf = some (decide (n < 256)) :=
    fun s h => by
      obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
      have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
      obtain ⟨s', run, hcf, hg, hm, hrd, hwr⟩ := small_ok s hbp hlt
      exact WP.of_runBlock ⟨s', run, ⟨hs.regs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hm hrd hwr,
        by rw [hg .r12 (by decide)]; exact h12, by rw [hg .rbp (by decide)]; exact hbp,
        by rw [hg .rbx (by decide)]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hcf⟩
  have cs := rel_both (rel_envT (F := G₃) [.rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₃s g₃s
  have pp : ∀ s, G₃ s → PartPre M Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega_arith, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  have gsm : ∀ s, PartPre M Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  -- The head's length.
  let G₄ : State → Prop := fun s => PartPre M Ctx St W SP R P₀ enc D n 0 k s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₄ : ∀ s, G₃ s → WP isa streamHead s G₄ := fun s h => by
    obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    refine WP.mono (sHead_ok hs.env hlt hbx hbp) fun s' ⟨hbp', hg, hl, ha, f, hrd, hwr⟩ => ?_
    rw [hk] at hbp' hl
    have rd : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
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
  have d := rel_both (rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
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
  have g₅ : n ≠ 0 → ∀ s, G₄ s → WP isa (headPart v.callees enc) s G₅ := fun hn s h => by
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
  have g₄t : ∀ s, G₄ s → WP isa (.block [.alu .test .rbx (.reg .rbx)]) s T₄ := fun s h => by
    obtain ⟨⟨hs, hk', h12, hbp, hbx, hdat, hlen, htl⟩, ha⟩ := h
    have hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbx hbx (by omega_arith)
    rw [Nat.add_zero] at hz
    exact WP.of_runBlock ⟨s', run, ⟨⟨hs.regs (fun r _ => by rw [hg]) hm hrd hwr, hk', by rw [hg]; exact h12,
      by rw [hg]; exact hbp, by rw [hg]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hm ▸ ha⟩, hz⟩
  have e₁ := rel_both (rel_envT (F := G₄) [.rbx] (fun _ h => h.1.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]) ⟨_, by taint_decide⟩) g₄t g₄t
  have e : n ≠ 0 → RelCT isa (fun s₁ s₂ => G₄ s₁ ∧ G₄ s₂) (headPart v.callees enc) fun s₁ s₂ => G₅ s₁ ∧ G₅ s₂ :=
    fun hn => by
    refine rel_both (RelCT.seq e₁ (rel_ite_e (fun _ _ h => h.1.2.trans h.2.2.symm)
      (RelCT.block_nil fun _ _ _ => trivial) ?_)) (g₅ hn) (g₅ hn)
    by_cases hz : P₀ % 16 = 0
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hz] at this
    have e' : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, hz]
    rw [hk] at e'
    exact (headPart_rel v L enc (k := k) (by omega_arith) hz (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩)
      fun _ _ h => h
  -- Past the head.
  have g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (BPre M Ctx St W SP R P₀ enc D n k) := fun s h => by
    obtain ⟨hs, hl, hdat, htl, ha⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    exact WP.mono (next_ok hs.env hkn hlt hl hdat htl ha) fun s' ⟨hg, d', t', l', f, hrd, hwr⟩ =>
      ⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (Nat.le_refl _)
        (by decide) f, d', l', t'⟩
  have f := rel_both (rel_envT (F := G₅) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₆ g₆
  -- The whole blocks.
  let G₇ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  have g₇ : ∀ s, BPre M Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then B.enc
      else B.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (blocks_ok B K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega_arith)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  have g := rel_both (blocks_rel B L enc) g₇ g₇
  -- The rest.
  have g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (load_env hg) hm hrd hwr, by omega_arith, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  have i := rel_both (rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  have g₉ : ∀ s, PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  have j := rel_both (part_rel v L enc) g₉ g₉
  simp only [streamTextS]
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

/-! ## The stack below the frame, in two runs -/

/-- The 24 bytes below the stack pointer of `streamText`: the return
addresses of its calls, and the stack argument of the whole blocks. -/
abbrev Below24 (SP : Addr) : Addr → Prop := fun x => (below SP 24).Contains x 1

theorem slot_below16 {SP x : Addr} (_h : 24 ≤ SP.toNat) (hx : (below SP 8).Contains x 1) :
    ¬ (below (SP - BitVec.ofNat 64 8) 16).Contains x 1 := by
  have := SP.isLt; have := x.isLt
  simp only [below, Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
  generalize SP.toNat = P at *
  generalize x.toNat = X at *
  omega_arith

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R : Nat}
include L

/-- The call of the whole blocks leaves its stack argument as it found it. -/
theorem callBlocks_keep (enc : Bool) {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s)
    {t : List Leak} {u : State}
    (e : Exec isa (.call (if enc then B.enc else B.dec).name (if enc then B.enc else B.dec).code) (pushed [.rax] s) t u)
    (x : Addr) (hx : (⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩ : Region).Contains x 1) : u.mem x = (pushed [.rax] s).mem x := by
  have bp : BlkPost (pushed [.rax] s) (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 16) D
      (W + BitVec.ofNat 64 448) q u := by
    cases enc
    · obtain ⟨t', u', e', bp, -⟩ := blkD_call B (ObIn.call L h)
      obtain ⟨-, rfl⟩ := Exec.det e e'
      exact bp
    · obtain ⟨t', u', e', bp, -⟩ := blkE_call B (ObIn.call L h)
      obtain ⟨-, rfl⟩ := Exec.det e e'
      exact bp
  have hsp := h.env.rsp
  rw [hsp] at hx
  have h24 : (below SP 24).Contains x 1 := below_sub (by decide) (by decide) x hx
  have hq := h.q_le
  obtain qd : Region.Sub ⟨D, q * 16⟩ ⟨D, n⟩ := Region.sub_prefix (by omega_arith)
  obtain sS : Region.Sub ⟨W + BitVec.ofNat 64 448, 2112⟩ ⟨W, 2560⟩ := Lay.wSub (by decide)
  obtain sC : Region.Sub ⟨St + BitVec.ofNat 64 48, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  obtain sY : Region.Sub ⟨St + BitVec.ofNat 64 16, 16⟩ ⟨St, 80⟩ := Lay.stSub (by decide)
  refine bp.frame x fun r hr => ?_
  simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (h.t_s.sub_right sC) x h24
  · exact (h.t_s.sub_right sY) x h24
  · exact (h.t_d.sub_right qd) x h24
  · exact (h.t_w.sub_right sS) x h24
  · rw [pushed_rsp, hsp]; exact slot_below16 h.sp24 hx

/-- The frame of the call of the whole blocks keeps `Same`: both runs push
the same argument, and the call leaves it as it found it. -/
theorem callBlocks_relS (enc : Bool) {D : Addr} {n q : Nat}
    (hn : UpperLock.inames (if enc then B.enc else B.dec).code = []) :
    StackLock.RelS (Below24 SP) (fun s₁ s₂ => ObIn M Ctx St W SP R D n q s₁ ∧ ObIn M Ctx St W SP R D n q s₂)
      (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
        (if enc then B.enc else B.dec).code) (.pop .rax 1)) fun _ _ => True :=
  StackLock.RelS.push1 (callBlocks_rel B L enc)
    (by cases enc
        · exact B.decNosp
        · exact B.encNosp) hn
    (fun _ _ h => by rw [h.1.rax, h.2.rax])
    fun _ _ h => ⟨fun _ _ e => callBlocks_keep B L enc h.1 e, fun _ _ e => callBlocks_keep B L enc h.2 e⟩

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R P₀ : Nat} {D : Addr} {n : Nat}
include L

open StackLock in
/-- `blocks_rel`, keeping `Same` below the stack pointer. -/
theorem blocks_relS (enc : Bool) {j : Nat} (hn : UpperLock.inames (if enc then B.enc else B.dec).code = []) :
    RelS (Below24 SP) (fun s₁ s₂ => BPre M Ctx St W SP R P₀ enc D n j s₁ ∧ BPre M Ctx St W SP R P₀ enc D n j s₂)
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
  obtain c := RelS.post (callBlocks_relS B L enc hn) (rel_both (callBlocks_rel B L enc) hw₃ hw₃)
  obtain d := rel_envT (F := Env Ctx St W SP) (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax),
      .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx),
      .mov .rcx (.mem (at_ .r15 dataO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx,
      .mov .rcx (.mem (at_ .r15 tlenO)), .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx])
    [] (fun _ h => h) (fun _ _ _ _ _ h => by cases h) ⟨_, by taint_decide⟩
  unfold streamBlocks
  refine RelS.seq (RelS.lift a (by plain_tac))
    (RelS.ite_e (fun _ _ h => by rw [h.1.1, h.2.1]) (RelS.block_nil fun _ _ _ => trivial) ?_)
  exact (RelS.seq (RelS.lift b (by plain_tac)) (RelS.seq c (RelS.lift d (by plain_tac)))).mono
    (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.1, ← h.1.1.1, h.2]⟩⟩) fun _ _ h => h

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
  {R aL P₀ : Nat} {D : Addr} {n : Nat}
include L in
open StackLock in
/-- `streamTextS_rel`, keeping `Same` below the stack pointer. -/
theorem streamTextS_relS (enc : Bool) (hP : P₀ < 2 ^ 64) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames (if enc then B.enc else B.dec).code = []) :
    RelS (Below24 SP) (fun s₁ s₂ => TPre M Ctx St W SP R aL P₀ D n s₁ ∧ TPre M Ctx St W SP R aL P₀ D n s₂)
      (streamTextS (v.withBlk B) enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  generalize hk : headLen P₀ n = k
  have hkw := headLen_whole P₀ n
  have hkn := headLen_le P₀ n
  rw [hk] at hkw hkn
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre M Ctx St W SP R aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre M Ctx St W SP R aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbp h.rbp h.data.ok.lt
    exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r _ => by rw [hg]) hrd hwr, h.data.of_eq hrd hwr,
      by rw [hg]; exact h.rbp, hm ▸ h.alen, hm ▸ h.tlen, hm ▸ h.dat, hm ▸ h.len, by rw [hm]; exact h.K, h.hP, by rw [hrd, hwr]; exact h.cov⟩, hz⟩
  have a := rel_both (rel_envT (F := TPre M Ctx St W SP R aL P₀ D n) [.rbp] (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  -- The start.
  let F₀ : State → Prop := fun s => T1 s ∧ s.zf = some false
  let G₂ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₂ : ∀ s, F₀ s → WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) s G₂ := fun s h => by
    have t := h.1.1
    refine WP.mono (startS_ok v t.K enc (Hyp := False) (icb := 0) t.env rfl t.data t.cov (a := List.replicate aL 0)
      (c₀ := List.replicate P₀ 0) (by simpa using t.hP) (by simpa using t.alen) (by simpa using t.tlen)
      False.elim False.elim) fun s' ⟨I, sl⟩ => ?_
    simp only [List.length_replicate] at I
    refine ⟨⟨_, _, _, _, t.K, ?_, I.toT⟩, by rw [sl 200 (by decide) (by decide)]; exact t.dat,
      by rw [sl 208 (by decide) (by decide)]; exact t.len, by rw [sl 192 (by decide) (by decide)]; exact t.tlen⟩
    have := Proof.Gcm.length_pad_mod aL
    simp only [List.length_append, List.length_replicate, Proof.Gcm.length_zeros]; omega_arith
  have b := rel_both (startS_rel v L (aL := aL) (F := F₀) hP (fun s h => ⟨h.1.1.env, h.1.1.tlen, h.1.1.alen⟩))
    g₂ g₂
  -- The data loaded.
  let G₃ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n 0 s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  have g₃ : ∀ s, G₂ s → WP isa (.block streamLoad) s G₃ := fun s h => by
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok h.1.env h.2.1 h.2.2.1 h.2.2.2
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, h.1.regs (load_env hg) hm hrd hwr, h12, hbp, hbx, hm ▸ h.2.1, hm ▸ h.2.2.1,
      hm ▸ h.2.2.2⟩
  have c := rel_both (rel_envT (F := G₂) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₃ g₃
  -- Fewer than 256 bytes, or more.
  have g₃s : ∀ s, G₃ s → WP isa (.block streamSmall) s fun s' => G₃ s' ∧ s'.cf = some (decide (n < 256)) :=
    fun s h => by
      obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
      have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
      obtain ⟨s', run, hcf, hg, hm, hrd, hwr⟩ := small_ok s hbp hlt
      exact WP.of_runBlock ⟨s', run, ⟨hs.regs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hm hrd hwr,
        by rw [hg .r12 (by decide)]; exact h12, by rw [hg .rbp (by decide)]; exact hbp,
        by rw [hg .rbx (by decide)]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hcf⟩
  have cs := rel_both (rel_envT (F := G₃) [.rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) ⟨_, by taint_decide⟩) g₃s g₃s
  have pp : ∀ s, G₃ s → PartPre M Ctx St W SP R P₀ enc D n 0 n s := fun s h =>
    ⟨h.1, by omega_arith, by simp [h.2.1], h.2.2.1, by rw [h.2.2.2.1, Nat.add_zero], by rw [h.2.2.2.2.1]; simp,
      h.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2, Nat.add_zero]⟩
  have gsm : ∀ s, PartPre M Ctx St W SP R P₀ enc D n 0 n s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  -- The head's length.
  let G₄ : State → Prop := fun s => PartPre M Ctx St W SP R P₀ enc D n 0 k s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  have g₄ : ∀ s, G₃ s → WP isa streamHead s G₄ := fun s h => by
    obtain ⟨hs, h12, hbp, hbx, hdat, hlen, htl⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    refine WP.mono (sHead_ok hs.env hlt hbx hbp) fun s' ⟨hbp', hg, hl, ha, f, hrd, hwr⟩ => ?_
    rw [hk] at hbp' hl
    have rd : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
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
  have d := rel_both (rel_envT (F := G₃) [.rbx, .rbp] (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
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
  have g₅ : n ≠ 0 → ∀ s, G₄ s → WP isa (headPart v.callees enc) s G₅ := fun hn s h => by
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
  have g₄t : ∀ s, G₄ s → WP isa (.block [.alu .test .rbx (.reg .rbx)]) s T₄ := fun s h => by
    obtain ⟨⟨hs, hk', h12, hbp, hbx, hdat, hlen, htl⟩, ha⟩ := h
    have hlt := Nat.mod_lt (P₀ + 0) (show 16 > 0 by decide)
    obtain ⟨s', run, hz, hg, hm, hrd, hwr⟩ := test_ok s .rbx hbx (by omega_arith)
    rw [Nat.add_zero] at hz
    exact WP.of_runBlock ⟨s', run, ⟨⟨hs.regs (fun r _ => by rw [hg]) hm hrd hwr, hk', by rw [hg]; exact h12,
      by rw [hg]; exact hbp, by rw [hg]; exact hbx, hm ▸ hdat, hm ▸ hlen, hm ▸ htl⟩, hm ▸ ha⟩, hz⟩
  have e₁ := rel_both (rel_envT (F := G₄) [.rbx] (fun _ h => h.1.1.env) (fun _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.2.2.1, h₂.1.2.2.2.2.1]) ⟨_, by taint_decide⟩) g₄t g₄t
  have e : n ≠ 0 → RelCT isa (fun s₁ s₂ => G₄ s₁ ∧ G₄ s₂) (headPart v.callees enc) fun s₁ s₂ => G₅ s₁ ∧ G₅ s₂ :=
    fun hn => by
    refine rel_both (RelCT.seq e₁ (rel_ite_e (fun _ _ h => h.1.2.trans h.2.2.symm)
      (RelCT.block_nil fun _ _ _ => trivial) ?_)) (g₅ hn) (g₅ hn)
    by_cases hz : P₀ % 16 = 0
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hz] at this
    have e' : headLen P₀ n = min (16 - P₀ % 16) n := by simp [headLen, hz]
    rw [hk] at e'
    exact (headPart_rel v L enc (k := k) (by omega_arith) hz (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩)
      fun _ _ h => h
  -- Past the head.
  have g₆ : ∀ s, G₅ s → WP isa (.block streamNext) s (BPre M Ctx St W SP R P₀ enc D n k) := fun s h => by
    obtain ⟨hs, hl, hdat, htl, ha⟩ := h
    have hlt := (let ⟨_, _, _, _, _, _, I⟩ := hs; I.data.ok.lt : n < 2 ^ 64)
    exact WP.mono (next_ok hs.env hkn hlt hl hdat htl ha) fun s' ⟨hg, d', t', l', f, hrd, hwr⟩ =>
      ⟨hs.slots (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hrd hwr (Nat.le_refl _)
        (by decide) f, d', l', t'⟩
  have f := rel_both (rel_envT (F := G₅) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₆ g₆
  -- The whole blocks.
  let G₇ : State → Prop := fun s => SI M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) s ∧
    s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - k) % 16) ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (k + 16 * ((n - k) / 16)))
  have g₇ : ∀ s, BPre M Ctx St W SP R P₀ enc D n k s → WP isa (streamBlocks (if enc then B.enc
      else B.dec)) s G₇ := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨H, icb, x₀, m₀, K, hx, I⟩ := hs
    exact WP.mono (blocks_ok B K enc I hx hdat hlen htl (fun hq => hkw.resolve_left (by omega_arith)))
      fun s' ⟨I', d', l', t'⟩ => ⟨⟨H, icb, x₀, m₀, K, hx, I'⟩, d', l', t'⟩
  have g := RelS.post (blocks_relS B L enc hn) (rel_both (blocks_rel B L enc) g₇ g₇)
  -- The rest.
  have g₈ : ∀ s, G₇ s → WP isa (.block streamLoad) s
      (PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16)) := fun s h => by
    obtain ⟨hs, hdat, hlen, htl⟩ := h
    obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok hs.env hdat hlen htl
    rw [toNat_mod16] at hbx
    exact WP.of_runBlock ⟨s', run, hs.regs (load_env hg) hm hrd hwr, by omega_arith, h12, hbp, hbx, hm ▸ hdat,
      hm ▸ hlen, hm ▸ htl⟩
  have i := rel_both (rel_envT (F := G₇) [] (fun _ h => h.1.env) (fun _ _ _ _ _ h => by cases h)
    ⟨_, by taint_decide⟩) g₈ g₈
  have g₉ : ∀ s, PartPre M Ctx St W SP R P₀ enc D n (k + 16 * ((n - k) / 16)) ((n - k) % 16) s →
      WP isa (partWith enc (crypt v.callees) (absorb v.callees 16)) s (Env Ctx St W SP) :=
    fun s h => WP.mono (si_part v enc h) fun _ h' => h'.1.env
  have j := rel_both (part_rel v L enc) g₉ g₉
  have pa : Plain (.block [.alu .test .rbp (.reg .rbp)]) := Plain.block (by decide)
  have pb : Plain (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlushS v.callees) (.block []))) := by plain_tac
  have pc : Plain (.block streamLoad) := Plain.block (by decide)
  have pcs : Plain (.block streamSmall) := Plain.block (by decide)
  -- Each part once, the heads first: `crypt` and `absorb` hold them, and either direction holds both, so
  -- that `plain_tac` finds them among the hypotheses rather than walk their code again.
  have pch : Plain cryptHead := by plain_tac
  have pah : Plain (absorbHead v.callees 16) := by plain_tac
  have pcr : Plain (crypt v.callees) := by plain_tac
  have pab : Plain (absorb v.callees 16) := by plain_tac
  have pj : Plain (partWith enc (crypt v.callees) (absorb v.callees 16)) := by
    unfold partWith; cases enc <;> plain_tac
  have pd : Plain streamHead := by plain_tac
  have pe : Plain (headPart v.callees enc) := by unfold headPart partWith; cases enc <;> plain_tac
  have pf : Plain (.block streamNext) := Plain.block (by decide)
  simp only [streamTextS]
  refine RelS.seq (RelS.lift a pa) (RelS.ite_e (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelS.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  by_cases hs : n < 256
  · -- All of it is the rest.
    refine RelS.assoc2 ((RelS.seq (RelS.lift b pb) (RelS.seq (RelS.lift c pc)
      (RelS.seq (RelS.lift cs pcs) (RelS.seq
      (RelS.ite (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelS.block_nil fun _ _ h => ⟨pp _ h.1.1.1, pp _ h.1.2.1⟩)
        (RelS.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this))
      (RelS.lift (rel_both (part_rel v L enc (j := 0) (k := n)) gsm gsm) pj))))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)
  · -- The head and the whole blocks first.
    refine RelS.assoc2 ((RelS.seq (RelS.lift b pb) (RelS.seq (RelS.lift c pc)
      (RelS.seq (RelS.lift cs pcs) (RelS.seq
      (RelS.ite (c := .b) (fun _ _ h => by show _ = _; exact h.1.2.trans h.2.2.symm)
        (RelS.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hs] at this)
        ((RelS.seq (RelS.lift d pd) (RelS.seq (RelS.lift (e (by omega_arith)) pe)
          (RelS.seq (RelS.lift f pf) (RelS.seq g (RelS.lift i pc))))).mono
          (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))
      (RelS.lift j pj))))).mono
      (fun _ _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, by rw [h.1.2.2, ← h.1.1.2, h.2]⟩⟩) fun _ _ h => h)


end

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem streamS_rel (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s₀) (hok : M.ok s₀.mem (s₀.gpr .rdi))
    (hp' : Proof.AesGcm.streamCryptPre M.len s₀') (hok' : M.ok s₀'.mem (s₀'.gpr .rdi))
    (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp M.ge).lay
  have hE₂ := cryptEntry_tpre hp' hok'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_tpre hp hok
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp M.ge).args.2 (CryptCtx.of hp' M.ge).args.2 ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamTextS_rel v B L enc (s₀.gpr .r8).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

open StackLock in
/-- `streamS_rel`, keeping `Same` below the stack pointer: two runs of
`stream_encrypt` (`enc`) or `stream_decrypt` with the same public values,
from states agreeing on the 24 bytes below it, end agreeing on them. -/
theorem streamS_same (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.AesGcm.streamCryptPre M.len s₀) (hok : M.ok s₀.mem (s₀.gpr .rdi))
    (hp' : Proof.AesGcm.streamCryptPre M.len s₀') (hok' : M.ok s₀'.mem (s₀'.gpr .rdi))
    (hq : Proof.AesGcm.streamCryptPub s₀ s₀') (hct : Plain v.callees.ctr.code) (hgh : Plain v.callees.gh.code)
    (hn : UpperLock.inames (if enc then B.enc else B.dec).code = [])
    (hs : Same (Below24 (s₀.gpr .rsp)) s₀ s₀') {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s₀ t₁ u₁)
    (e₂ : Exec isa (.seq (.block cryptEntry) (.seq (streamTextS (v.withBlk B) enc) (.block restore))) s₀' t₂ u₂) :
    Same (Below24 (s₀.gpr .rsp)) u₁ u₂ := by
  obtain ⟨ht, -⟩ := streamS_rel v B enc hp hok hp' hok' hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have L := (CryptCtx.of hp M.ge).lay
  have hE₂ := cryptEntry_tpre hp' hok'
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_tpre hp hok
  have pE : Plain (.block cryptEntry) := Plain.block (by decide)
  have pR : Plain (.block restore) := Plain.block (by decide)
  cases e₁ with
  | seq x₁ y₁ =>
    cases y₁ with
    | seq z₁ w₁ =>
      cases e₂ with
      | seq x₂ y₂ =>
        cases y₂ with
        | seq z₂ w₂ =>
          obtain ⟨rfl, -⟩ := UpperLock.lock x₁ x₂ ht (by rw [pE.2]; nofun)
          have ht' := List.append_cancel_left ht
          obtain ⟨_, _, ex₁, T₁⟩ := hE₁
          obtain ⟨_, _, ex₂, T₂⟩ := hE₂
          obtain ⟨-, rfl⟩ := Exec.det x₁ ex₁
          obtain ⟨-, rfl⟩ := Exec.det x₂ ex₂
          have hx := lock_eq pE.1 x₁ x₂ (by rw [pE.2]; nofun) hs
          obtain ⟨rfl, -, hz⟩ := streamTextS_relS v B L enc (s₀.gpr .r8).isLt hct hgh hn _ _ _ _ _ _
            ⟨⟨T₁, T₂⟩, hx⟩ z₁ z₂
          obtain rfl := List.append_cancel_left ht'
          exact lock_eq pR.1 w₁ w₂ (by rw [pR.2]; nofun) hz

theorem streamEncryptSM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptX86_64M M).pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncryptS (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => streamS_rel v B true hp.1 hp.2 hp'.1 hp'.2 hq

theorem streamDecryptSM_ct (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.streamDecryptX86_64M M).pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecryptS (v.withBlk B)) :=
  ct_of_rel fun _ _ hp hp' hq => streamS_rel v B false hp.1 hp.2 hp'.1 hp'.2 hq

end VG.Proof.AesGcm.X86_64
