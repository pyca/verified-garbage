module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
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

/-- `OpenMid`, with the buffer `kb` in `s7`. -/
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

end VG.Proof.AesGcm.RISCV64
