module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `vg_aes_gcm_open_split_with_powers`, what it computes

Untrusted: everything here is checked by Lean.
`Impl.AesGcm.AArch64.Stitch.openSplitWithPw` is `open`'s entry with `work`
the stack argument 5, `src` (the stack argument 3) loaded into `x6`, then
`open`'s path for TLS records (`openFastS`) out of place: the interleaved
loop decrypts the ciphertext at `src` to `dst`, and the rest is `open`'s on
`dst` (`openRunWithS_postXT`). `openSpN` is what it needs, `splitPost` what
it computes (`openSp_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.OpenSplit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64 VG.Proof.AesGcm.AArch64.Fast
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The ciphertext, the stack argument 3, of `len` bytes. -/
abbrev srcR (s : State) : Region := ⟨stackArg s 3, (s.gpr .x7).toNat⟩

/-- What `vg_aes_gcm_open_split_with_powers` needs, on the regions its proofs
run on: `openPreXW 5`, with `pw` and `src` readable, apart from the text
(`dst`) and the working space, `pw` holding the powers of the hash subkey, a
12-byte nonce and at most 16 bytes of additional data. -/
def openSpN (s : State) : Prop :=
  openPreXW 5 [pwRO s, srcR s] s ∧ (pwRO s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (pwRO s).Disjoint ⟨stackArg s 5, 2560⟩ ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 2) (ctxH s.mem (s.gpr .x0)) ∧
    (srcR s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧ (srcR s).Disjoint ⟨stackArg s 5, 2560⟩ ∧
    (stackArg s 3).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat = 12 ∧ (s.gpr .x5).toNat ≤ 16 ∧
    (stackArg s 4).toNat = (s.gpr .x7).toNat

/-- What `open` computes for the arguments of `s`, of the ciphertext at `src`
(of `src_len` bytes, the stack argument 4). -/
def splitRes (s : State) : Option (List Byte) :=
  Spec.Gcm.openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- If the tag is right, 1 and the plaintext at `dst`; otherwise 0. -/
def splitPost (s s' : State) : Prop :=
  match splitRes s with
  | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
  | none => (s'.gpr .x0).setWidth 32 = 0

/-! ## The call of `vg_ghash_with_powers` -/

/-- `gwCallO_of`, with `work` the stack argument 5. -/
theorem gwCallS_of {σ s : State} {Y S : Addr} (hs : openSpN σ) (sY : Region.Sub ⟨Y, 16⟩ (workR (stackArg σ 5)))
    (sS : Region.Sub ⟨S, 256⟩ (workR (stackArg σ 5))) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR (stackArg σ 5), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem) :
    s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg σ 2 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 ∧
      GhWCall s (σ.gpr .x0) Y S (stackArg σ 2) := by
  obtain ⟨hpx, pd, pw, rep, -⟩ := hs
  obtain ⟨ol, -, -⟩ := openLay hpx
  have hrd₀ := hpx.1
  have hp' := hpx
  simp only [openPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, dda, -⟩ := hp'
  have hspA := ol.hsp 2 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ (args σ 6) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 16, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 6⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pw.sub_right sY).symm, (pw.sub_right sS).symm, ?_⟩⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ol.args.sub_left sA
      · exact (dda.sub_right sA).symm) (by decide)]
    rfl
  · refine Covers.left (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hrd, hrd₀]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  · have hH : Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = ctxH σ.mem (σ.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [hH]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwRO σ) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact pw
        · exact pd) (show 128 ≤ 2 ^ 64 by decide) hi) rep

/-- `pwTbl 16` writes the table, from the powers in `pw`. -/
theorem pwTbl_forS {s : State} (hs : openSpN s) :
    TbForOP (Impl.AesGcm.AArch64.Stitch.pwTbl 16) (s.gpr .x0) (stackArg s 5) s.sp (s.gpr .x6) (s.gpr .x7).toNat s :=
  fun u he hrd hwr hf => by
    obtain ⟨hP, hsl, k⟩ := gwCallS_of hs (Y := stackArg s 5 + BitVec.ofNat 64 512)
      (S := stackArg s 5 + BitVec.ofNat 64 512) (Lay.wSub (by decide)) (Lay.wSub (by decide)) hrd hwr he.sp hf
    obtain ⟨ol, -, -⟩ := openLay hs.1
    have hH : Spec.Gcm.blockAt u.mem (s.gpr .x0 + BitVec.ofNat 64 240) = ctxH s.mem (s.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [← hH]
    exact Stitch.pwTbl_ok (by decide) he hP hsl k.reads k.repr

/-! ## The entry -/

/-- `open`'s entry with `work` the stack argument 5, then `src` into `x6`. -/
theorem splitEntry_ok {s : State} (hs : openSpN s) :
    WP isa (.block (oneEntry 40 ++ stashArg 8 ++ ([.ldrSp .x12 0, .ldrSp .x6 24] : List Instr))) s fun s₂ =>
      OpenIn (s.gpr .x0) (stackArg s 5) s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (stackArg s 0)
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat s s₂ ∧
      s₂.gpr .x12 = stackArg s 0 ∧ s₂.gpr .x6 = stackArg s 3 ∧
      ∀ r ∈ [Reg.x4, .x5, .x7], s₂.gpr r = s.gpr r := by
  obtain ⟨ol, -, -⟩ := openLay hs.1
  rw [show oneEntry 40 ++ stashArg 8 ++ ([.ldrSp .x12 0, .ldrSp .x6 24] : List Instr) =
    (oneEntry (8 * 5) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr)) ++ [.ldrSp .x6 24] by simp,
    WP.block_append_iff]
  refine WP.mono (WP.gprs (rs := [.x4, .x5, .x7]) (openEntryW_ok ⟨by decide, by decide⟩ hs.1)
    (by decide) (by decide)) fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_
  have sp₁ : s₁.sp = s.sp := o₁.env.sp.trans o₁.sp₀.symm
  have sA : Region.Sub ⟨s.sp + BitVec.ofNat 64 24, 8⟩ (args s 6) := by
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 24, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * 6⟩
    rw [show s.sp + BitVec.ofNat 64 (8 * 0) = s.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  have hin : InRegions (s₁.rd ++ s₁.wr) (s₁.sp + BitVec.ofNat 64 24) 8 := by
    rw [o₁.rd₀, o₁.wr₀, sp₁]; exact ol.hsp 3 (by decide)
  have hval : s₁.mem.readW (s₁.sp + BitVec.ofNat 64 24) 64 = stackArg s 3 := by
    rw [sp₁, o₁.fr.readW (r := ⟨s.sp + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
      (fun r hr => (ol.args.sub_left sA).sub_right (entry16_work _ r hr)) (by decide)]
    rfl
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrSp ⟨by decide, by decide⟩ hin, WP.block_nil ?_⟩
  have r₂ : Regs [.x6] s₁ (s₁.write .x .x6 (s₁.mem.readW (s₁.sp + BitVec.ofNat 64 24) 64)) :=
    ⟨fun r hr => gpr_write_of_ne _ _ _ (fun h => hr (h ▸ List.mem_singleton_self _)), rfl, rfl, rfl, rfl⟩
  refine ⟨o₁.of_regs r₂, by rw [r₂.others _ (by decide), x12₁], ?_, fun r hr => ?_⟩
  · rw [gpr_write_self, BitVec.setWidth_eq, hval]
  · rw [r₂.others _ (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide), hx₁ r hr]

/-! ## What it computes -/

/-- `OpenPostG`, whatever the memory is if the tag is wrong. -/
theorem OpenPostG.true {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {C : List Byte} {F : Mem → Prop}
    {s₀ u : State} (h : OpenPostG Ctx W SP Np A D Tg R nl al n tl C F s₀ u) :
    OpenPostG Ctx W SP Np A D Tg R nl al n tl C (fun _ => True) s₀ u := by
  obtain ⟨e, sv, m⟩ := h
  refine ⟨e, sv, ?_⟩
  split
  next pt heq => rw [heq] at m; exact m
  next heq => rw [heq] at m; exact ⟨m.1, trivial⟩

/-- The ciphertext at `src`, after the entry: readable, apart from the
working space, and as it was. -/
theorem srcFacts {σ t : State} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} (hs : openSpN σ)
    (o : OpenIn Ctx W SP Np A D Tg R nl al n tl σ t) (hW : W = stackArg σ 5) (hn : n = (σ.gpr .x7).toNat) :
    DataOk (W + BitVec.ofNat 64 16) W t (stackArg σ 3) n ∧
      bytesAt t.mem (stackArg σ 3) n = bytesAt σ.mem (stackArg σ 3) n := by
  subst hW hn
  obtain ⟨hpx, -, -, -, -, sw, swrap, -⟩ := hs
  have hnl := (σ.gpr .x7).isLt
  refine ⟨⟨Covers.of_mem fun r hr => ?_, hnl, swrap, sw.sub_right (Lay.wSub (by decide)), sw⟩,
    Proof.AesGcm.bytesAt_congr fun i hi =>
      o.fr.bytes (R := srcR σ) (fun r hr => sw.sub_right (entry16_work _ r hr))
        (show (σ.gpr .x7).toNat ≤ 2 ^ 64 by omega) hi⟩
  simp only [List.mem_singleton] at hr
  subst hr
  rw [o.rd₀, o.wr₀, hpx.1]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
include hMK gh

theorem openSp_wp (s : State) (hs : openSpN s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openSplitWithPw v.callees g.fn) s fun s' =>
      GprAbi s s' ∧ splitPost s s' := by
  obtain ⟨-, -, -, -, sd, sw, -, h12, hal, h4n⟩ := id hs
  unfold Impl.AesGcm.AArch64.Stitch.openSplitWithPw Impl.AesGcm.AArch64.Stitch.openFastS
  refine WP.seq (WP.mono (splitEntry_ok hs) fun s₂ ⟨o₂, x12₂, x6₂, hx₂⟩ => ?_)
  refine WP.mono (openRestWithG_wp (w := 5) (F := fun _ => True)
    (C := bytesAt s.mem (stackArg s 3) (s.gpr .x7).toNat) o₂ x12₂ (fun _ _ => trivial)
    fun {t} o' hT hok hx' => ?_) fun s' ⟨ga, q⟩ => ⟨ga, ?_⟩
  · obtain ⟨hsrc, hS⟩ := srcFacts hs o' rfl rfl
    refine WP.mono (openRunWithS_postXT v _ hMK gh («to» := true) (ex := []) (I := fun _ => True) o' h12
      ((hx' .x4 (by simp)).trans (hx₂ .x4 (by simp)))
      (by rw [hx' .x5 (by simp), hx₂ .x5 (by simp), ofNat_toNat']) ((hx' .x6 (by simp)).trans x6₂)
      (by rw [hx' .x7 (by simp), hx₂ .x7 (by simp), ofNat_toNat']) hal hT hok hsrc sw sd hS
      (by simp) (by simp) (by simp) (fun _ _ => trivial)
      (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
        have q := gwCallS_of hs sY sS hrd hwr hsp hf
        WP.mono (pwSel_call v g (k := 16) (by decide) q.1 q.2.1 hc q.2.2) fun _ g => ⟨g, trivial⟩)
      (pwTbl_forS hs).tbFor) fun u q => OpenPostG.true q.1
  · unfold splitPost splitRes
    rw [h4n]
    split
    next pt heq => rw [heq] at q; exact q
    next heq => rw [heq] at q; exact q.1

end

end VG.Proof.AesGcm.AArch64.OpenSplit
