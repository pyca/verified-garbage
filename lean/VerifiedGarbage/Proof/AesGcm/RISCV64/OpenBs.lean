module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.Bitsliced
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.Bitsliced
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-!
# AES-GCM on RISC-V: `open` and `open_to` with the round keys bitsliced

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_bitsliced`
and `vg_aes_gcm_open_to_bitsliced` are the plain functions' body
(`openWithB true o`) with `bk`, a stack argument before the working space's
address, loaded into `s7` once `oneAad` is done (`bkLoad (bkOff o)`), and
`vg_aes_ctr32_bs` (or `_bs_to`) on it for `vg_aes_ctr32`. As `Verified.lean`'s
`open_head`, `open_tail` and `open_body`, which these follow: the buffer's
round keys reach the calls through the frame of everything before them,
which is within the working space and the stack below `sp` (`wF`), apart
from the buffer (`BkIn.frameW`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- The bitsliced round keys, after code whose frame is within the working
space and the stack below `sp`. -/
theorem BkIn.frameW {kb c st W sp : Addr} {R : Nat} {m m' : Mem} {S D : Addr} {n : Nat} {s s' : State}
    (hb : BkIn kb c st W sp R m S D n s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (wF W sp) m m')
    (hc : ∀ r ∈ wF W sp, (⟨c, 256⟩ : Region).Disjoint r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    BkIn kb c st W sp R m' S D n s' :=
  hb.frame hR hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hb.w
    · exact hb.sk) hc hrd hwr

/-- What the `_bitsliced` `open`'s body needs of the buffer `kb`: its round
keys, from the context, and its address at `sp + bkOff o`, a stack argument
apart from the working space and the stack below `sp`. -/
structure BkPre (o : Bool) (s₀ : State) (W Dst kb : Addr) : Prop where
  bk : BkIn kb (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp (s₀.gpr .a1).toNat s₀.mem (s₀.gpr .a6) Dst
    (s₀.gpr .a7).toNat s₀
  slot : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 (bkOff o)) 64 = kb
  inr : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (bkOff o)) 8
  dslot : ∀ r ∈ wF W s₀.sp, (⟨s₀.sp + BitVec.ofNat 64 (bkOff o), 8⟩ : Region).Disjoint r

/-- After the tags are compared, with the result in `s8`, out of place the
distance to the destination in `s9`, and the buffer `kb` in `s7`, from `s₄`
(after the entry). -/
structure OpenMidB (o : Bool) (s₀ : State) (W T Dst kb : Addr) (TL : Nat) (s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem W s₀
  frame : Frame (wF W s₀.sp) s₀.mem s.mem
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat))
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  s8 : s.gpr .s8 = BitVec.ofNat 64 (if OpenTagOk s₀ T TL then 1 else 0)
  s9 : o = true → s.gpr .s9 = Dst - s₀.gpr .a6
  s7 : s.gpr .s7 = kb

/-- `open_head`, with the round keys bitsliced. -/
theorem openB_head [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₄ : State} {W T Dst kb : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (hb : BkPre o s₀ W Dst kb) (h4 : SO2 o W T Dst s₀ s₄)
    (h19 : s₄.gpr .s8 = BitVec.ofNat 64 TL) (hok : Spec.Gcm.tagLenOk TL = true) {T' : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMidB o s₀ W T Dst kb TL s₄ s₉ → WP isa T' s₉ Q) :
    WP isa (.seq oneAad (.seq (.block (bkLoad (bkOff o))) (.seq (oneTagB true 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o)) T')))))) s₄ Q := by
  have L₀ := h.lay
  have hk₀ := h.stk
  have hR := h.rounds
  have wa := h.wa
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain he₄ := h4.env h.ctx h.w hk₀
  obtain L := L₀.v h4.s2 h4.s1 h4.s0
  have hk₄ := h4.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  have F₄ : Frame (wF W s₀.sp) s₀.mem s₄.mem := h4.frame
  -- `oneAad`
  obtain hN : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a2) (s₀.gpr .a3).toNat := by
    rw [h4.s1, h4.s0]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.nonce, (s₀.gpr .a3).isLt, h.fn, h.dnW.sub_right (Lay.wSub (by decide)),
      h.dnW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  obtain hAd : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a4) (s₄.gpr .s10).toNat := by
    rw [h4.s1, h4.s0, h4.s10]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.aad, (s₀.gpr .a5).isLt, h.fa, h.daW.sub_right (Lay.wSub (by decide)),
      h.daW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.s4 (by rw [h4.s5]; exact toN)
    (by rw [h4.s7]; exact toN) hN hAd (by rw [h4.s0]; exact h4.aad))) fun s₅ ⟨oa, rd₅, wr₅, sp₅⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.s1, h4.s0] at f₅
  obtain F₅ : Frame (wF W s₀.sp) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `bkLoad`: `s7 := kb`, the stack argument, which nothing has written
  obtain spA : s₅.sp = s₀.sp := sp₅.trans hk₄.sp
  refine WP.seq (WP.mono (bkLoad_ok (s := s₅) (off := bkOff o) (by cases o <;> decide) (by rw [spA]; exact h.al)
    (by cases o <;> decide) (by rw [rd₅, wr₅, hk₄.rd, hk₄.wr, spA]; exact hb.inr)) fun s₅' ⟨b7, g₅', k₅'⟩ => ?_)
  rw [spA, slot_keep F₅ hb.dslot, hb.slot] at b7
  obtain he₅' := oa.env.set7 b7 (fun r hr h7 => g₅' r (by rintro rfl; exact absurd hr (by decide)) h7) k₅'.sp
    k₅'.rd k₅'.wr
  obtain F₅' : Frame (wF W s₀.sp) s₀.mem s₅'.mem := by rw [k₅'.mem]; exact F₅
  -- `oneTag 112`
  obtain hs₄ : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a6) (s₄.gpr .s11).toNat := by
    rw [h4.s1, h4.s0, h4.s11]; exact h.dsrc.of_eq hk₄.rd hk₄.wr hk₄.sp
  obtain h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
  obtain dat₅ : s₅.mem.readW (s₄.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oa.frame (slot_j0 L he₄.stk' (by decide)), h4.s0]; exact h4.dat
  obtain dst₅ : o = true → s₅.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [← h4.s0, slot_keep oa.frame (slot_j0' L he₄.stk' (d := dstO) (by decide)), h4.s0]; exact h4.dst ho
  refine WP.seq (WP.mono (WP.with_rdwr (oneTagB_ok (V := setS7 s₄.gpr kb) (bs := true) L (o := 112) (.inr rfl)
    (H := blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240)) (a := bytesAt s₄.mem (s₀.gpr .a4) (s₄.gpr .s10).toNat)
    he₅' h28 hR (by rw [k₅'.mem]; exact oa.hH) (length_bytesAt _ _ _).symm (by rw [k₅'.mem]; exact oa.abs)
    (hs₄.of_eq (k₅'.rd.trans rd₅) (k₅'.wr.trans wr₅) (k₅'.sp.trans sp₅))
    (by rw [k₅'.mem]; exact dat₅) (S' := s₀.gpr .a6) (D' := Dst) (n' := (s₀.gpr .a7).toNat)
    fun _ => by
      show BkIn kb (s₄.gpr .s2) (s₄.gpr .s1) (s₄.gpr .s0) s₀.sp _ _ _ _ _ _
      rw [h4.s2, h4.s1, h4.s0]
      exact hb.bk.frameW hR F₅' dcF (k₅'.rd.trans (rd₅.trans hk₄.rd)) (k₅'.wr.trans (wr₅.trans hk₄.wr))))
    fun s₆ ⟨ot, rd₆, wr₆, sp₆⟩ => ?_)
  rw [k₅'.mem] at ot
  have f₆ := ot.frame
  simp only [setS7, reduceCtorEq, ↓reduceIte] at f₆
  rw [h4.s1, h4.s0] at f₆
  obtain F₆ : Frame (wF W s₀.sp) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .s8 = BitVec.ofNat 64 TL := h19
  obtain hTr : Covers [⟨s₄.gpr .s9, TL⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, k₅'.rd, k₅'.wr, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.s9]; exact h.tag
  obtain hTd : (⟨s₄.gpr .s9, TL⟩ : Region).Disjoint ⟨s₄.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.s9, h4.s0]; exact h.dtW.sub_right (Lay.wSub (by decide))
  obtain wa₄ : (s₄.gpr .s0).toNat % 8 = 0 := by rw [h4.s0]; exact wa
  refine WP.seq (WP.mono (recv_ok ot.env wa₄ h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  obtain he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  simp only [setS7, reduceCtorEq, ↓reduceIte] at hf₇ hb₇
  rw [h4.s0] at hf₇ hb₇
  obtain F₇ : Frame (wF W s₀.sp) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ wa₄ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  obtain he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  simp only [setS7, reduceCtorEq, ↓reduceIte] at hf₈ h3₈
  rw [h4.s0] at hf₈ h3₈
  obtain F₈ : Frame (wF W s₀.sp) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat
  let a := bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat
  let tg := bytesAt s₀.mem T TL
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
  let H := ctxH s₀.mem (s₀.gpr .a0)
  obtain hH₄ : blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240) = H := by
    rw [h4.s2]; exact ctxH_keep F₄ dcF
  obtain iv₄ : bytesAt s₄.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat = iv :=
    bytes_W F₄ h.dnW (h.bufs _ (by simp)) (by have := (s₀.gpr .a3).isLt; omega_arith)
  obtain a₄ : bytesAt s₄.mem (s₀.gpr .a4) (s₄.gpr .s10).toNat = a := by
    rw [h4.s10]; exact bytes_W F₄ h.daW (h.bufs _ (by simp)) (by have := (s₀.gpr .a5).isLt; omega_arith)
  obtain ct₅ : bytesAt s₅.mem (s₀.gpr .a6) (s₄.gpr .s11).toNat = ct := by
    rw [h4.s11]; exact bytes_W F₅ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain hc₅ : ciphOf s₅.mem (s₄.gpr .s2) (s₀.gpr .a1).toNat = ciph := by rw [h4.s2]; exact ciph_keep F₅ dcF hR
  obtain hj₅ : blockAt s₅.mem (s₄.gpr .s1) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  obtain hT₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    simp only [setS7, reduceCtorEq, ↓reduceIte] at ho
    rw [h4.s0, hc₅, hj₅, ct₅, ← h4.s0, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.s0]; exact ho
  obtain hT₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  obtain hr₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - TL) := by
    rw [hb₇, h4.s9]; congr 1; exact bytes_W F₆ h.dtW (h.bufs _ (by simp)) (by omega_arith)
  let X := (fullTag ciph H iv a ct).take TL = tg
  obtain hX : (bytesAt s₇.mem (W + BitVec.ofNat 64 112) TL ++
      zeros (16 - TL) = bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  obtain r3₈ : s₈.gpr .a0 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  obtain f₆₈ : Frame (otFrame (W + BitVec.ofNat 64 16) W 112 s₀.sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
    ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain cb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame f₆₈ (cb_ot L₀ hk₀), ← h4.s1, oa.cb, hH₄, iv₄]
  obtain dat₈ : s₈.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide)), ← h4.s0]; exact dat₅
  obtain dst₈ : o = true → s₈.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide))]; exact dst₅ ho
  obtain sv₈ : SavedAt s₈.mem W s₀ :=
    (((h4.saved.frame f₅ (saved_j0Frame L₀ hk₀)).frame f₆ (saved_otFrame L₀ hk₀ (.inr rfl))).frame hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame
      hf₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `s8`, and out of place the distance into `s9`
  refine WP.seq (WP.block_append (Steps.wp_mv fun s₉ u₉ => WP.block_nil ?_))
  obtain k₉ : Keeps s₈ s₉ := ⟨u₉.mem, u₉.rd, u₉.wr, u₉.sp⟩
  obtain g₉0 : s₉.gpr .s0 = W := by
    rw [u₉.other _ (by decide), he₈.fr _ (by decide)]; simp only [setS7, reduceCtorEq, ↓reduceIte]; exact h4.s0
  refine WP.mono (deltaArg_ok (o := o) (δ := Dst - s₀.gpr .a6) g₉0 wa (by
      rw [k₉.rd, k₉.wr, k₈.rd, k₈.wr, k₇.rd, k₇.wr, rd₆, wr₆, k₅'.rd, k₅'.wr, rd₅, wr₅, hk₄.rd, hk₄.wr]
      exact in_left (covers_off h.w (show dstO + 8 ≤ 2560 by decide) (by decide) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩))
      (fun ho => by rw [k₉.mem]; exact dst₈ ho)) fun s₁₀ ⟨d₁₀, g₁₀, k₁₀⟩ => ?_
  obtain kk : Keeps s₈ s₁₀ := k₉.trans k₁₀
  obtain g : ∀ r, r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₈.gpr r := fun r h8 h9 => by
    rw [g₁₀ r h9, u₉.other r h8]
  obtain he₁₀ : Env s₁₀.gpr s₀.sp s₁₀ := he₈.self' (g _ (by decide) (by decide)) (g _ (by decide) (by decide))
    (g _ (by decide) (by decide)) kk
  obtain e : ∀ r ∈ frozen, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₄.gpr r := fun r hf h7 h8 h9 =>
    (g r h8 h9).trans ((he₈.fr r hf).trans (by simp only [setS7, h7, ↓reduceIte]))
  obtain e7 : s₁₀.gpr .s7 = kb :=
    (g _ (by decide) (by decide)).trans ((he₈.fr _ (by decide)).trans (by simp only [setS7, ↓reduceIte]))
  obtain rd₁₀ : s₁₀.rd = s₄.rd := kk.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans (k₅'.rd.trans rd₅))))
  obtain wr₁₀ : s₁₀.wr = s₄.wr := kk.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans (k₅'.wr.trans wr₅))))
  refine k s₁₀ ⟨he₁₀, e, rd₁₀, wr₁₀, kk.mem ▸ sv₈, kk.mem ▸ F₈, by rw [kk.mem]; exact cb₈,
    by rw [kk.mem]; exact dat₈, fun ho => by rw [kk.mem]; exact dst₈ ho, ?_, d₁₀, e7⟩
  rw [g₁₀ _ (by decide), u₉.gpr, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- `open_tail`, with the round keys bitsliced. -/
theorem openB_tail {o : Bool} {s₀ s₄ s₉ : State} {W T Dst kb : Addr} {TL : Nat} (h : OPre o s₀ W T Dst TL)
    (hb : BkPre o s₀ W Dst kb) (h4 : SO2 o W T Dst s₀ s₄) (om : OpenMidB o s₀ W T Dst kb TL s₄ s₉) :
    WP isa (.seq (.ite (.zero .s8) (.block []) (oneCryptB true o)) (.block [mov .a0 .s8])) s₉
      (BodyOut o s₀ W T Dst TL) := by
  have L₀ := h.lay
  have hk₀ := h.stk
  have hR := h.rounds
  have hk₄ := h4.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  obtain h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
  let iv := bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  obtain sp₉ : s₉.sp = s₄.sp := he₉.sp.trans hk₄.sp.symm
  obtain src₉ : bytesAt s₉.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = ct :=
    bytes_W F₉ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain dst₉ : bytesAt s₉.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat :=
    bytes_W F₉ h.dDW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain hk₉ : Keeps' s₀ s₉ := ⟨rd₉.trans hk₄.rd, wr₉.trans hk₄.wr, sp₉.trans hk₄.sp⟩
  obtain hd₉₀ : DataW (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₉ Dst (s₀.gpr .a7).toNat :=
    h.ddst.of_eq hk₉.rd hk₉.wr hk₉.sp
  obtain hs₉₀ : DataOk (W + BitVec.ofNat 64 16) W s₉ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    h.dsrc.of_eq hk₉.rd hk₉.wr hk₉.sp
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite (.zero .s8) (.block []) (oneCryptB true o)) s₉ fun s₁₀ =>
      (∀ r ∈ frozen, r ≠ .s9 → s₁₀.gpr r = s₉.gpr r) ∧ s₁₀.sp = s₉.sp ∧ SavedAt s₁₀.mem W s₀ ∧
      s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      s₁₀.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 ∧
      (o = true → s₁₀.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6) ∧
      ((OpenTagOk s₀ T TL) → bytesAt s₁₀.mem Dst (s₀.gpr .a7).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(OpenTagOk s₀ T TL) → bytesAt s₁₀.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat) := by
    refine WP.ite _ (eval_zero om.s8 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(OpenTagOk s₀ T TL) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, sv₉, rd₉, wr₉, om.dat, om.dst, fun x => absurd x hx,
        fun _ => dst₉⟩
    · have hx : (OpenTagOk s₀ T TL) := Classical.byContradiction fun x => by simp [x] at hf
      obtain L₉ : Lay (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) := by
        rw [e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide) (by decide), h4.s2, h4.s1, h4.s0]
        exact L₀
      obtain e11 : s₉.gpr .s11 = s₀.gpr .a7 := by rw [e _ (by decide) (by decide) (by decide) (by decide), h4.s11]
      obtain hd₉ : DataW (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) s₉ Dst (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide) (by decide), e11, h4.s2, h4.s1, h4.s0]
        exact hd₉₀
      obtain hs₉ : DataOk (s₉.gpr .s1) (s₉.gpr .s0) s₉ (s₀.gpr .a6) (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide), e11, h4.s1, h4.s0]
        exact hs₉₀
      obtain h28₉ : s₉.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by
        rw [e _ (by decide) (by decide) (by decide) (by decide)]; exact h28
      obtain cb₉ : blockAt s₉.mem (s₉.gpr .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide) (by decide) (by decide), h4.s1]; exact om.cb
      obtain ds₉ : s₉.mem.readW (s₉.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
        rw [e _ (by decide) (by decide) (by decide) (by decide), h4.s0]; exact om.dat
      refine WP.mono (WP.with_rdwr (oneCryptB_ok (bs := true) L₉ he₉ h28₉ hR hd₉ hs₉ (by rw [e11]; exact h.alias)
        om.s9 ds₉ cb₉ fun _ => ?_)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      · rw [om.s7, e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide) (by decide), e11, h4.s2, h4.s1, h4.s0]
        exact hb.bk.frameW hR F₉ dcF hk₉.rd hk₉.wr
      have cf := oc.frame
      rw [e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide),
        e11, h4.s1, h4.s0] at cf
      obtain dS : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → s₁₀.mem.readW (W + BitVec.ofNat 64 d) 64 =
          s₉.mem.readW (W + BitVec.ofNat 64 d) 64 := fun hd =>
        slot_keep cf (slot_crFrame' (V := fun r => if r = .s2 then s₀.gpr .a0 else if r = .s1 then
          W + BitVec.ofNat 64 16 else W) L₀ hd₉₀ hd)
      refine ⟨fun r hr _ => oc.env.fr r hr, oc.env.sp.trans he₉.sp.symm, sv₉.frame cf (saved_crFrame L₀ hd₉₀), rd₁₀.trans rd₉,
        wr₁₀.trans wr₉, by rw [dS (by decide)]; exact om.dat, fun ho => by rw [dS (by decide)]; exact om.dst ho,
        fun _ => ?_, fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide) (by decide), h4.s11, h4.s2,
        ciph_keep F₉ dcF hR, src₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨g₁₀, sp₁₀, sv₁₀, rd₁₀, wr₁₀, dat₁₀, dst₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `a0`
  refine Steps.wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_
  refine ⟨by rw [u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide),
      e _ (by decide) (by decide) (by decide) (by decide), h4.s0],
    by rw [u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide),
      e _ (by decide) (by decide) (by decide) (by decide), h4.s11],
    by rw [u₁₁.sp, sp₁₀, sp₉, hk₄.sp], by rw [u₁₁.rd, rd₁₀, hk₄.rd], by rw [u₁₁.wr, wr₁₀, hk₄.wr],
    by rw [u₁₁.mem]; exact sv₁₀, by rw [u₁₁.mem]; exact dat₁₀, fun ho => by rw [u₁₁.mem]; exact dst₁₀ ho,
    by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide), om.s8],
    fun hx => by rw [u₁₁.mem]; exact hd₁ hx, fun hx _ => by rw [u₁₁.mem]; exact hd₂ hx⟩

/-- `open_good`, with the round keys bitsliced. -/
theorem openB_good [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₄ : State} {W T Dst kb : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (hb : BkPre o s₀ W Dst kb) (h4 : SO2 o W T Dst s₀ s₄)
    (h19 : s₄.gpr .s8 = BitVec.ofNat 64 TL) (hok : Spec.Gcm.tagLenOk TL = true) :
    WP isa (.seq oneAad (.seq (.block (bkLoad (bkOff o))) (.seq (oneTagB true 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o))
      (.seq (.ite (.zero .s8) (.block []) (oneCryptB true o)) (.block [mov .a0 .s8])))))))) s₄
      (BodyOut o s₀ W T Dst TL) :=
  openB_head h hb h4 h19 hok fun _ om => openB_tail h hb h4 om

/-- `open_body`, with the round keys bitsliced. -/
theorem openB_body [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₂ : State} {W T Dst kb : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (hb : BkPre o s₀ W Dst kb) (h2 : SO2 o W T Dst s₀ s₂)
    (h19 : s₂.gpr .s8 = BitVec.ofNat 64 TL)
    {F : Prog isa} {Q : State → Prop} (k : ∀ s, BodyRes o s₀ W T Dst TL s → WP isa F s Q) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .s5) (.block [.li .a0 0]) (openGoodWithB true o)) F)) s₂ Q := by
  have F₂ : Frame (wF W s₀.sp) s₀.mem s₂.mem := h2.frame
  refine WP.seq (WP.mono (tagLenOk_ok h19 h.tl) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (Q := BodyRes o s₀ W T Dst TL) ?_ k)
  refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
  · have hbad : Spec.Gcm.tagLenOk TL = false := by
      cases e : Spec.Gcm.tagLenOk TL
      · rfl
      · simp [e] at ht
    refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s0
    · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s11
    · rw [u.sp, k₃.sp]; exact h2.keeps.sp
    · rw [u.rd, k₃.rd]; exact h2.keeps.rd
    · rw [u.wr, k₃.wr]; exact h2.keeps.wr
    · rw [u.mem, k₃.mem]; exact h2.saved
    · rw [u.mem, k₃.mem]; exact h2.dat
    · intro ho; rw [u.mem, k₃.mem]; exact h2.dst ho
    · intro hx; rw [hbad] at hx; exact absurd hx.1 (by decide)
    · intro _; refine ⟨u.gpr, fun _ => ?_⟩
      rw [u.mem, k₃.mem]
      exact bytes_W F₂ h.dDW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  · have hok : Spec.Gcm.tagLenOk TL = true := by
      cases e : Spec.Gcm.tagLenOk TL
      · simp [e] at hf
      · rfl
    refine WP.seq (Steps.wp_mv fun s₄ u₄ => WP.block_nil ?_)
    obtain g₄ : ∀ r, r ≠ .t0 → r ≠ .s8 → s₄.gpr r = s₂.gpr r := fun r h0 h8 => by
      by_cases e : r = .s5
      · subst e
        rw [u₄.gpr, g₃ _ (by decide) (by decide), h2.s7, h2.s5]
      · rw [u₄.other r e, g₃ r h0 e]
    obtain h4 : SO2 o W T Dst s₀ s₄ :=
      h2.keep g₄ ⟨by rw [u₄.mem, k₃.mem], by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.sp, k₃.sp]⟩
    refine WP.mono (openB_good h hb h4 (by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h19) hok)
      fun s bo => ⟨bo.s0, bo.s11, bo.sp, bo.rd, bo.wr, bo.saved, bo.dat, bo.dst, fun hx => ⟨?_, bo.good hx.2⟩,
        fun hx => ⟨?_, bo.bad (fun x => hx ⟨hok, x⟩)⟩⟩
    · rw [bo.a0, ite_eq_left_of_eq_true _ _ (eq_true hx.2)]; rfl
    · rw [bo.a0, ite_eq_right_of_eq_false _ _ (eq_false (fun x => hx ⟨hok, x⟩))]; rfl


/-! ## `vg_aes_gcm_open_bitsliced` -/

/-- In place: `vg_aes_gcm_open_bitsliced`'s precondition. -/
theorem openBsPre.opre {s₀ : State} (h : openBsPre s₀) :
    OPre false s₀ (stackArg s₀ 3) (stackArg s₀ 0) (s₀.gpr .a6) (stackArg s₀ 1).toNat := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, ft, fW, fsp, hR,
    hstk, ca, wa, ba, hsl⟩ := h
  obtain mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  obtain hD : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  exact ⟨mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), covers_left hD,
    mr (by rw [hrd]; simp), by rw [hwr]; exact covers_mem (by simp), hD, dcW, dnW, daW, ddW, dtW, ddW, dcd, fc,
    fn, fa, fd, fd, fW, (stackArg s₀ 1).isLt, fun r hr => hstk.buf (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h <;> subst h <;> simp), hstk.1, hstk.2.1,
    hR, ca, wa, rfl⟩

/-- In place: what `vg_aes_gcm_open_bitsliced`'s precondition says of `bk`. -/
theorem openBsPre.bkpre {s₀ : State} (h : openBsPre s₀) :
    BkPre false s₀ (stackArg s₀ 3) (s₀.gpr .a6) (stackArg s₀ 2) := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, ft, fW, fsp, hR,
    hstk, ca, wa, ba, hsl⟩ := h
  obtain hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  obtain db : (⟨stackArg s₀ 2, 960⟩ : Region).Disjoint ⟨stackArg s₀ 3, 2560⟩ :=
    dbW.sub_left (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ba, db.sub_right (Lay.wSub (by decide)), db,
    (stkAll_mem hstk.2.2 (r := ⟨stackArg s₀ 2, 1248⟩) (by simp)).symm.sub_left (Region.sub_prefix (by decide)),
    dbd.sub_left (Region.sub_prefix (by decide)),
    keysAt_of_sliced hR14 hsl⟩, rfl, args_in hA (by decide) (i := 2) (by decide), fun r hr => ?_⟩
  · exact covers_appL (covers_prefix (k := 1248) (covers_mem (by rw [hrd]; simp)) (by decide))
  · refine Region.Disjoint.sub_left ?_ (Offset.sub s₀.sp (d := 16) (n := 8) (e := 0) (k := 32) (by decide) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dWA.symm
    · exact (stkAll_mem hstk.2.2 (r := args s₀ 4) (by simp)).symm

/-- The entry of `open_bitsliced`, and `tag_len` in `s8`. -/
theorem openBsEntry_wp {s₀ : State} (h : openBsPre s₀) :
    WP isa (.block (openEntryWithB true false)) s₀ fun s₂ =>
      SO1 (stackArg s₀ 3) (stackArg s₀ 0) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 1 := by
  have wa := h.opre.wa
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, ft, fW, fsp, -,
    hstk, -⟩ := hh
  obtain hW : Covers [⟨stackArg s₀ 3, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dA : (args s₀ 4).Disjoint (oneR (stackArg s₀ 3)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 3)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 4 by decide))
  obtain hLd : (⟨s₀.sp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 3)) := by
    obtain hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8) (n := 8) (k := 32) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  show WP isa (.block (oneEntry 24 ++ ([.load .d .s8 .t1 8] : List Instr))) s₀ _
  refine WP.block_append (WP.mono (one1At_wp (off := 24) (tagO := 0) (W := stackArg s₀ 3) (T := stackArg s₀ 0)
    (by decide) (.inl rfl) hW wa hstk.1 (args_in hA (by decide) (i := 3) (by decide)) rfl
    (args_in hA (by decide) (i := 0) (by decide)) rfl hTd) fun s₁ h1 => ?_)
  -- `tag_len` into `s8`
  obtain hi : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 8) 8 := by
    rw [h1.keeps.rd, h1.keeps.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  obtain hv : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 := by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine Steps.wp_ld (off := 8) (a := s₀.sp + BitVec.ofNat 64 8) (by decide) (by rw [h1.t1])
    (Spill.al8 (by have := hstk.1; omega_using [this]) (by decide)) hi fun s₂ u₂ => WP.block_nil ?_
  exact ⟨h1.keep (fun r _ hr => u₂.other r hr) ⟨u₂.mem, u₂.rd, u₂.wr, u₂.sp⟩, by rw [u₂.gpr, hv]⟩

theorem openBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : openBsRISCV64.pre s₀) :
    WP isa openBs s₀ fun s' => abiPreserved s₀ s' ∧ openBsRISCV64.post s₀ s' := by
  have h' : openBsPre s₀ := h
  have hp := h'.opre
  have hW : Covers [⟨stackArg s₀ 3, 2560⟩] s₀.wr := hp.w
  refine WP.seq (WP.mono (openBsEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  refine openB_body hp h'.bkpre h2.so2 (by rw [h19]; simp) fun s₅ ⟨h31, _, hsp, hrd, hwr, hsv, _, _, hg, hb⟩ => ?_
  show WP isa (.block restore) s₅ _
  refine WP.mono (restore_ok h31 hp.wa (by rw [hrd, hwr]; exact Covers.right hW) hsv hsp)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out ?_ hm h3⟩
  obtain hres : openRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true ∧ openTagOk s₀ then
      some (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)) else none := by
    simp only [openRes, openResult, decryptWith]
    by_cases hl : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true
    · simp only [hl, ite_true, true_and]
    · simp only [hl, false_and, ite_false, Bool.false_eq_true]
  by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true ∧ openTagOk s₀
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (hg hx).1 (hg hx).2
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (hb hx).1 ((hb hx).2 rfl)

/-! ## Constant time

Once `oneAad` is done,
`bkLoad` reads the stack at a public address, `s7` is the buffer in both
runs (`OneIK`), and the calls take it (`oneTagB_ct`, `oneCryptB_ct`), with
its round keys carried through the frames of the pieces between. -/

/-- The bitsliced round keys, after code whose frame is within the working
space and the stack below `sp`, piece by piece. -/
theorem BkIn.frameInW {kb c W sp : Addr} {R : Nat} {m m' : Mem} {S D : Addr} {n : Nat} {s s' : State}
    (hb : BkIn kb c (W + BitVec.ofNat 64 16) W sp R m S D n s) (L : Lay c (W + BitVec.ofNat 64 16) W)
    (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) (hR : R = 10 ∨ R = 12 ∨ R = 14) {rs : List Region}
    (hf : Frame rs m m') (hj : ∀ r ∈ rs, ∃ r' ∈ wF W sp, Region.Sub r r') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : BkIn kb c (W + BitVec.ofNat 64 16) W sp R m' S D n s' := by
  refine hb.frame hR hf (fun r hr => ?_) (fun r hr => ?_) hrd hwr
  · obtain ⟨r', hr', hs⟩ := hj r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hb.w.sub_right hs
    · exact hb.sk.sub_right hs
  · obtain ⟨r', hr', hs⟩ := hj r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact L.cw'.sub_right hs
    · exact hk.c.sub_right hs

/-- `OneO` with `K` in `s7` and without the nonce (`OneIK`). -/
def OneOK (o : Bool) (c W sp : Addr) (R : Nat) (K Ad A D Ln T TL Dst : BitVec 64) (s : State) : Prop :=
  OneIK c W sp R K Ad A D Ln s ∧ s.gpr .s9 = T ∧ s.gpr .s8 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr) ∧
    OX o c W D Dst Ln s

/-- After `oneAad`: the buffer's address in its stack slot, and its round keys. -/
def BkS (o : Bool) (c W sp : Addr) (R : Nat) (kb D Dst : Addr) (Ln : BitVec 64) (s : State) : Prop :=
  s.mem.readW (sp + BitVec.ofNat 64 (bkOff o)) 64 = kb ∧
    InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 (bkOff o)) 8 ∧
    BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s

section
variable {o : Bool} {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T TL Dst K : BitVec 64}

theorem OneOK.frame {s s' : State} (h : OneOK o c W sp R K Ad A D Ln T TL Dst s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneOK o c W sp R K Ad A D Ln T TL Dst s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf (fun hd => hs ⟨hd.1, by omega_using [hd]⟩),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2.1,
    h.2.2.2.2.frame hrd hwr hsp hf (hs (d := dstO) (by decide))⟩

/-- `OneIK` after a step that changes only `s8` and `s9` among the registers it
pins. -/
theorem OneIK.self {s s' : State} (h : OneIK c W sp R K Ad A D Ln s)
    (hg : ∀ r, r ≠ .s8 → r ≠ .s9 → s'.gpr r = s.gpr r) (hk : Keeps s s') : OneIK c W sp R K Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .s8 → r ≠ .s9 → s'.gpr r = V r := fun r hr h19 h20 =>
    (hg r h19 h20).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he.self' (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) hk,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩
  · rw [q _ (by decide) (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide) (by decide), d]
  · rw [q _ (by decide) (by decide) (by decide), e]
  · rw [q _ (by decide) (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide) (by decide), k]

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool) {kb : Addr}
  (hS : ∀ r ∈ wF W sp, (⟨sp + BitVec.ofNat 64 (bkOff o), 8⟩ : Region).Disjoint r) (hsa : sp.toNat % 16 = 0)
include L hR hTd t1 t16 hS hsa

/-- `openGood_ct`, with the round keys bitsliced. -/
theorem openGoodB_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    CT (fun s => (OneO o c W sp R Np n Ad A D Ln T TL Dst s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n ∧ BkS o c W sp R kb D Dst Ln s) ∧
      WP isa (.seq oneAad (.seq (.block (bkLoad (bkOff o))) (.seq (oneTagB true 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o)) (.block []))))))) s (Res b))
    (.seq oneAad (.seq (.block (bkLoad (bkOff o))) (.seq (oneTagB true 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o))
      (.seq (.ite (.zero .s8) (.block []) (oneCryptB true o)) (.block [mov .a0 .s8])))))))) := by
  obtain h8 : ∀ r ∈ RISCV64.j0Frame (W + BitVec.ofNat 64 16) W sp,
      (⟨sp + BitVec.ofNat 64 (bkOff o), 8⟩ : Region).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hs⟩ := inW_j0 r hr; exact (hS r' hr').sub_right hs
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO o c W sp R Np n Ad A D Ln T TL Dst s ∧ OneAbs c W A s ∧
      BkS o c W sp R kb D Dst Ln s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25, _⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25, k8, i8, hbk⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have hk : StkOk c (W + BitVec.ofNat 64 16) W sp := by rw [← a, ← b, ← d]; exact he.stk'
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ => ?_
    have fr := oa.frame
    rw [b, d] at fr
    exact ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
        (fun hd' => by rw [← d]; exact slot_j0' (L.v a b d) he.stk' hd'),
      ⟨blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩,
      by rw [slot_keep fr h8]; exact k8, by rw [rd, wr]; exact i8,
      hbk.frame hR fr hbk.j0Frame (ctx_j0Frame L hk) rd wr⟩
  -- `bkLoad`
  refine CT.seqG (J := fun s => OneOK o c W sp R kb Ad A D Ln T TL Dst s ∧ OneAbs c W A s ∧
      BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s) ?_ (fun s ⟨hT, hab, k8, i8, hbk⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := bkLoadOff_taint o
    exact CT.taint _ (fun s₁ s₂ ⟨⟨⟨_, _, _, _, _, _, _, _, e₁, _⟩, _⟩, _⟩ ⟨⟨⟨_, _, _, _, _, _, _, _, e₂, _⟩, _⟩, _⟩ =>
      ⟨e₁.sp.trans e₂.sp.symm, by simp⟩) hc
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (bkLoad_ok (s := s) (off := bkOff o) (by cases o <;> decide) (by rw [he.sp]; exact hsa)
      (by cases o <;> decide) (by rw [he.sp]; exact i8)) fun s' ⟨b7, g, kp⟩ => ?_
    rw [he.sp, k8] at b7
    obtain he' := he.set7 b7 (fun r hr h7 => g r (by rintro rfl; exact absurd hr (by decide)) h7) kp.sp kp.rd kp.wr
    refine ⟨⟨⟨setS7 V kb, ?_, ?_, ?_, ?_, by simp only [setS7, ↓reduceIte], ?_, ?_, he', hA.of_eq kp.rd kp.wr kp.sp,
      hD.of_eq kp.rd kp.wr kp.sp, by rw [kp.mem]; exact sa, by rw [kp.mem]; exact sd⟩,
      (g .s9 (by decide) (by decide)).trans hT.2.1, (g .s8 (by decide) (by decide)).trans hT.2.2.1,
      by rw [kp.rd, kp.wr]; exact hT.2.2.2.1,
      ⟨hT.2.2.2.2.1.of_eq kp.rd kp.wr kp.sp, fun ho => by rw [kp.mem]; exact hT.2.2.2.2.2 ho⟩⟩,
      by simp only [OneAbs, kp.mem]; exact hab, by rw [kp.mem]; exact hbk.of_eq kp.rd kp.wr⟩ <;>
      simp only [setS7, reduceCtorEq, ↓reduceIte] <;> with_reducible assumption
  -- `oneTagB true 112`
  refine CT.seqG (J := fun s => OneOK o c W sp R kb Ad A D Ln T TL Dst s ∧
      BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s)
    ((oneTagB_ct L (bs := true) (kb := kb) (S' := D) (D' := Dst) (n' := Ln.toNat) (.inr rfl) hR).mono
      fun s ⟨hT, _, bk⟩ => ⟨hT.1, fun _ => ⟨rfl, bk⟩⟩)
    (fun s ⟨hT, ⟨H, x, hH, hl, hab⟩, hbk⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hT.1
    have hk := he.stk'
    rw [a, b, d] at hk
    refine WP.mono (WP.with_rdwr (oneTagB_ok (L.v a b d) (bs := true) (o := 112) (.inr rfl) (H := H) (a := x) (D := D)
      he e hR (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD)
      (by rw [d]; exact sd) fun _ => by rw [f, a, b, d]; exact hbk))
      fun s' ⟨ot, rd, wr, sp'⟩ => ?_
    have fr := ot.frame
    rw [b, d] at fr
    exact ⟨hT.frame (fun r hr => (he.fr r hr).symm) ot.env rd wr sp' fr (fun hd' => slot_ot112 L hk hd'),
      hbk.frameInW L hk hR fr inW_ot rd wr⟩
  -- `recv`
  refine CT.seqG (J := fun s => OneOK o c W sp R kb Ad A D Ln T TL Dst s ∧
      BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s) ?_ (fun s ⟨hT, hbk⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩, _⟩
      ⟨⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hT.1
    have hk := he.stk'
    rw [a, b, d] at hk
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .s9 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he (by rw [d]; exact L.wal) h19 t1 t16 (by rw [h20]; exact hT.2.2.2.1)
      (by rw [h20, d]; exact hTd))
      fun s' ⟨_, hf', g', k'⟩ => by
        rw [d] at hf'
        exact ⟨hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
          (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
          (fun hd' => slot_at (by decide) (by decide) hd'),
          hbk.frameInW L hk hR hf' (inW_at (by decide)) k'.rd k'.wr⟩
  -- `cmp 112`
  refine CT.seqG (J := fun s => OneOK o c W sp R kb Ad A D Ln T TL Dst s ∧
      BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s) ?_ (fun s ⟨hT, hbk⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _, b₁, _⟩, _⟩
      ⟨⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, _, b₂, _⟩, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hT.1
    have hk := he.stk'
    rw [a, b, d] at hk
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (by rw [d]; exact L.wal) (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, hf', g', k'⟩ => by
        rw [d] at hf'
        exact ⟨hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
          (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
          (fun hd' => slot_at (by decide) (by decide) hd'),
          hbk.frameInW L hk hR hf' (inW_at (by decide)) k'.rd k'.wr⟩
  -- the result into `s8`, and out of place the distance into `s9`
  refine CT.seqG (J := fun s => OneIK c W sp R kb Ad A D Ln s ∧ OD o c W D Dst Ln s ∧
    (o = true → s.gpr .s9 = Dst - D) ∧ BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s) ?_
    (fun s ⟨hT, hbk⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := deltaArg_taint o
    exact CT.taintEq _ (fun _ => W) sp (fun s ⟨⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _⟩, _⟩ =>
      ⟨h₁.sp, by simp [h₁.s0, d₁]⟩) hc
  · obtain ⟨V, a, b, d, e, f, i, k, he, hA, hD, sa, sd⟩ := hT.1
    refine WP.block_append (Steps.wp_mv fun s₁ u₁ => WP.block_nil ?_)
    refine WP.mono (deltaArg_ok (o := o) (δ := Dst - D) (W := W)
      (by rw [u₁.other _ (by decide), he.s0, d]) L.wal
      (by rw [u₁.rd, u₁.wr]; exact in_left (he.perm.wC (show dstO + 8 ≤ 2560 by decide) _ _
        ⟨_, List.mem_singleton_self _, by rw [d]; exact Region.contains_self _ _⟩))
      (fun ho => by rw [u₁.mem]; exact hT.2.2.2.2.2 ho)) fun s' ⟨d', g', k'⟩ => ⟨?_, ?_, d', ?_⟩
    · exact hT.1.self (fun r h8 h9 => by rw [g' r h9, u₁.other r h8])
        ⟨by rw [k'.mem, u₁.mem], by rw [k'.rd, u₁.rd], by rw [k'.wr, u₁.wr], by rw [k'.sp, u₁.sp]⟩
    · exact hT.2.2.2.2.1.of_eq (by rw [k'.rd, u₁.rd]) (by rw [k'.wr, u₁.wr]) (by rw [k'.sp, u₁.sp])
    · rw [k'.mem, u₁.mem]; exact hbk.of_eq (by rw [k'.rd, u₁.rd]) (by rw [k'.wr, u₁.wr])
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, (OneIK c W sp R kb Ad A D Ln s ∧ OD o c W D Dst Ln s ∧ (o = true → s.gpr .s9 = Dst - D) ∧
      BkIn kb c (W + BitVec.ofNat 64 16) W sp R s.mem D Dst Ln.toNat s) ∧
      WP isa (.block []) s (Res b) → isa.eval (.zero .s8) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCryptB_ct L (bs := true) (o := o) (kb := kb) (Dst := Dst) hR).mono
      fun s h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, fun _ => ⟨rfl, h.1.2.2.2⟩⟩)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, i, k, he, hA, hD, sa, sd⟩ := h.1.1
    have hOD := h.1.2.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.s0, d], he.sp⟩) (fun _ => ?_)
    exact WP.mono (oneCryptB_ok (L.v a b' d) (bs := true) he e hR (by rw [a, b', d, k]; exact hOD.1)
      (by rw [b', d, k]; exact hD) (by rw [k]; exact hOD.2)
      (fun ho => by rw [← he.fr .s9 (by decide)]; exact h.1.2.2.1 ho) (by rw [d]; exact sd) rfl
      fun _ => by rw [f, a, b', d, k]; exact h.1.2.2.2)
      fun s' oc => ⟨by rw [oc.env.s0, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .a0 .s8] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem openBs_one {t₀ s : State} (h : openBsPre t₀) (h1 : SO1 (stackArg t₀ 3) (stackArg t₀ 0) t₀ s)
    (h19 : s.gpr .s8 = stackArg t₀ 1) :
    OneO false (t₀.gpr .a0) (stackArg t₀ 3) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 0) (stackArg t₀ 1) (t₀.gpr .a6) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat ∧
      BkS false (t₀.gpr .a0) (stackArg t₀ 3) t₀.sp (t₀.gpr .a1).toNat (stackArg t₀ 2) (t₀.gpr .a6) (t₀.gpr .a6)
        (t₀.gpr .a7) s := by
  have hk₀ := h.opre.stk
  have hb := h.bkpre
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, dbd, dbW, fc, fn, fa, fd, ft, fW, fsp, hR,
    hstk, -⟩ := id h
  have hC : Covers [⟨t₀.gpr .a0, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg t₀ 3, 2560⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .a6, (t₀.gpr .a7).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hDok : DataOk (stackArg t₀ 3 + BitVec.ofNat 64 16) (stackArg t₀ 3) s (t₀.gpr .a6) (t₀.gpr .a7).toNat :=
    ⟨covers_left hDw, (t₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  refine ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    one_env h1 hC hW hk₀, ?_, ?_, hDok, h1.aad, h1.dat⟩, h1.s9, h19, ?_, ⟨⟨hDok, hDw, dcd⟩, rfl⟩, nofun⟩, h1.s4,
    by rw [h1.s5]; exact toN, ?_, ?_, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · rw [slot_keep (h1.frame.sub inW_one) hb.dslot]; exact hb.slot
  · rw [hk₁.rd, hk₁.wr]; exact hb.inr
  · refine hb.bk.frameW hR (h1.frame.sub inW_one) (fun r hr => ?_) hk₁.rd hk₁.wr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dcW
    · exact hk₀.c

theorem openBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa openBsRISCV64.pre openBsRISCV64.pub openBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openBsPre σ₁ := h₁
  have hbk := h₁'.bkpre
  have hsa := h₁'.opre.al
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, _, _, fc, _, _, _, _, fW, _, hR, _, ca, wa, _⟩ := h₁'
  let I₀ : State → Prop := fun s => openBsPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ stackArg s 3 = stackArg σ₁ 3 ∧
    (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qa 3 (by decide)).symm, (qres hR).symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 3) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 1
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openBsEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 3 else σ₁.gpr r
    have hl : openEntryWithB true false =
        [.addSp .t1 0, .load .d .t1 .t1 24] ++ (oneRest ++ ([.load .d .s8 .t1 8] : List Instr)) := by
      simp only [openEntryWithB, ↓reduceIte, Bool.false_eq_true, oneEntry_eq, List.append_assoc]
    show CT I₀ (.block (openEntryWithB true false))
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead24_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, _, ea2, _⟩
      have hA : Covers [args s 4] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := hs.opre.al
      refine WP.mono (oneAg_ok (W := stackArg s 3) (by decide) hsa (args_in hA (by decide) (i := 3) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 3) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 1 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 1).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 1).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW ca wa
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 3 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGoodB_ct (sp := σ₁.sp) (Np := σ₁.gpr .a2) (n := (σ₁.gpr .a3).toNat) (Ad := σ₁.gpr .a4) (A := σ₁.gpr .a5)
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) (o := false) (Dst := σ₁.gpr .a6) (kb := stackArg σ₁ 2) L₀ hR
        (dtW.sub_right (Lay.wSub (by decide))) t1 t16 (openRes σ₁).isSome hbk.dslot hsa)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2b, ea2, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      have o := openBs_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2b, ea2, esp] at o
      refine ⟨o, openB_head hpre.opre hpre.bkpre h4.so2 (by rw [h19₄.trans h19]; simp) hok₀ (T' := .block [])
        fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2b, ea2, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2b, ea2, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · exact Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil
        ⟨by rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea2],
          by rw [u.sp, k.sp, h1.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      exact WP.mono (openB_good hpre.opre hpre.bkpre h4.so2 (by rw [h19₄.trans h19]; simp) hok₀) fun s' oo =>
        ⟨by rw [oo.s0, ea2], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 3) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc


/-! ## The contracts -/

/-- Memory holding the stack arguments at `0x9000`: `tag` (`0x5000`),
`tag_len` 0, `bk` (`0x7000`) and the working space (`0x6000`). -/
def openBsSatMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9011 then 0x70 else
    bif Nat.beq a.toNat 0x9019 then 0x60 else 0

theorem openBsSatMem_zero {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x9001) :
    ∀ i < n, openBsSatMem (p + BitVec.ofNat 64 i) = 0 := fun i hi => by
  obtain e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h, hi]
  obtain hb : ∀ k, 0x9001 ≤ k → Nat.beq (p.toNat + i) k = false := fun k hk => by
    rw [← Bool.not_eq_true, Nat.beq_eq]; omega_using [h, hi, hk]
  simp only [openBsSatMem, e, hb _ (Nat.le_refl _), hb 0x9011 (by decide), hb 0x9019 (by decide), Bool.cond_false]

/-- `openBsPre`, with the buffers at `0x1000` (`ctx`), `0x2000` (no nonce),
`0x3000` (no additional data), `0x4000` (no data), and the stack arguments'. -/
def openBsSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem := openBsSatMem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x7000, 1248⟩, ⟨0x9000, 32⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- As `open_verified`: the postconditions match on `openResult`, and the
public data include the leak, whether it succeeds. -/
theorem openBs_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target openBs (Proof.AesGcm.openBitslicedScratchContract RISCV64.abi 2048) :=
  Verified.of_correct (fun _ hs => openBs_wp hs) openBs_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openBitslicedScratchContract, Proof.AesGcm.openBitslicedScratchSig,
          Spec.Gcm.openBitslicedPre, Spec.Gcm.openPre, openBsRISCV64, openBsPre, onePub, args, rounds, RISCV64.abi,
          RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openBitslicedScratchContract, Proof.AesGcm.openBitslicedScratchSig,
          Proof.AesGcm.openBitslicedRoundsPost, Proof.AesGcm.openRoundsPost, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openBsRISCV64, openRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openBitslicedScratchContract, Proof.AesGcm.openBitslicedScratchSig,
          Spec.Gcm.openBitslicedLeak, Spec.Gcm.openLeak, openBsRISCV64, openBsPre, onePub, args, rounds, RISCV64.abi,
          RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
          · exact a3
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := ⟨openBsSat, by
        sig_pre [Proof.AesGcm.openBitslicedScratchContract, Proof.AesGcm.openBitslicedScratchSig,
          Spec.Gcm.openBitslicedPre, Spec.Gcm.openPre, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr,
          List.getD, List.range, List.range.loop, openBsSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.ctxSlicedRepr_of_zero (openBsSatMem_zero (by decide)) (openBsSatMem_zero (by decide))⟩ }

/-! ## With the working space on the stack

As the plain `open`'s (`Verified.lean`): `tag`, `tag_len` and `bk` arrive
on the stack, which the frame copies, followed by the working space's
address (`Verified.stackScratchArgs`). -/

def openBsFrameSat : State :=
  { openBsSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x7000, 1248⟩, ⟨0x9000, 24⟩],
                   wr := [⟨0x4000, 0⟩] }

theorem openBsFrameSat_pre : ∃ s, (Proof.AesGcm.openBitslicedRoundsContract RISCV64.abi 4640).pre s := by
  refine ⟨openBsFrameSat, ?_⟩
  sig_pre [Proof.AesGcm.openBitslicedRoundsContract, Spec.Gcm.openBitslicedSig, Spec.Gcm.openSig,
    Spec.Gcm.bitslicedParam, Spec.Gcm.openBitslicedPre, Spec.Gcm.openPre, Proof.AesGcm.openBitslicedRoundsPost,
    Spec.Gcm.openBitslicedLeak, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
    List.range.loop, openBsFrameSat, openBsSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.ctxSlicedRepr_of_zero (openBsSatMem_zero (by decide)) (openBsSatMem_zero (by decide))

theorem openBs_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 3 openBs)
      (Proof.AesGcm.openBitslicedRoundsContract RISCV64.abi 4640) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openBitslicedSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openBitslicedPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.openBitslicedRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2592) (m := 3) (leak := some (Spec.Gcm.openBitslicedLeak RISCV64.abi.ptrBits))
    openBs_verified (by decide) (by decide)
    (Proof.AesGcm.openBitslicedPre_local _) (Proof.AesGcm.openBitslicedPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.openBitslicedPostOut_local _ vs m m₁ m₂ r hl)
    openBsFrameSat_pre (hleak := Proof.AesGcm.openBitslicedLeak_local _)

/-! ## Without secret residue

As `seal_bitsliced`'s (`OneBs.lean`). -/

open VG.RISCV64.Scrub

theorem openBsOut :
    PostOut (Spec.Gcm.openBitslicedContract RISCV64.abi 4640) (Spec.Gcm.openBitslicedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.AesGcm.openBitslicedPost_out _)

/-- `vg_aes_gcm_open_bitsliced` as emitted (`Impl.AesGcm.RISCV64.Fn.openBs`) meets its contract in
constant time and returns without secret residue: the theorem its registration binds. -/
theorem openBs_scrubbed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    VerifiedScrubbed target Impl.AesGcm.RISCV64.Fn.openBs
      (Spec.Gcm.openBitslicedContract RISCV64.abi 4640) 32 :=
  verifiedScrubbedSelT (api := Spec.Gcm.openBitslicedApi) (W := 4640)
    { code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 3 Impl.AesGcm.RISCV64.openBs
      verified := Proof.AesGcm.openBitsliced_keyed openBs_framed }
    [(2048, [(0, 256)]), (2048, [(0, 256)]), (144, [(0, 18)])] []
    openBsOut (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.AesGcm.RISCV64
