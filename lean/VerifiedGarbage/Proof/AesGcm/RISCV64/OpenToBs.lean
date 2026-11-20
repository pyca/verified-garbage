module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Verified
public import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
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
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenBs
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Verified
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
meta import VerifiedGarbage.Proof.AesGcm.RoundsTo
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
# AES-GCM decryption out of place on RISC-V, with the round keys bitsliced

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to_bitsliced`
is `vg_aes_gcm_open_bitsliced`'s body out of place, with its arguments
(`openToPreR`, `OpenTo/Verified.lean`) and `bk` a stack argument before the
working space's address, through the body `OpenBs.lean` proves for both
(`openB_body`, `openGoodB_ct`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `vg_aes_gcm_open_to_bitsliced` needs: `openToPreR`'s, with `bk` a
stack argument between `tag_len` and the working space, apart from what the
function writes, and the bitsliced form of the key context. -/
def openToBsPreR (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let src : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let dst : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let tag : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
  let bk : Region := ⟨stackArg s 4, 1248⟩
  let scr : Region := ⟨stackArg s 5, 2560⟩
  s.rd = [ctx, nonce, aad, src, tag, bk, args s 6] ∧ s.wr = [dst, scr] ∧
    ctx.Disjoint dst ∧ ctx.Disjoint scr ∧ nonce.Disjoint dst ∧ nonce.Disjoint scr ∧
    aad.Disjoint dst ∧ aad.Disjoint scr ∧ src.Disjoint dst ∧ src.Disjoint scr ∧ dst.Disjoint tag ∧
    dst.Disjoint scr ∧ dst.Disjoint (args s 6) ∧ tag.Disjoint scr ∧ scr.Disjoint (args s 6) ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
    (stackArg s 5).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 48 ≤ 2 ^ 64 ∧ rounds (s.gpr .a1) ∧
    stkOk s [ctx, nonce, aad, src, dst, tag, scr, args s 6, bk] ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 5).toNat % 8 = 0 ∧ (stackArg s 1).toNat = (s.gpr .a7).toNat ∧
    bk.Disjoint dst ∧ bk.Disjoint scr ∧ (stackArg s 4).toNat % 8 = 0 ∧
    Spec.Gcm.CtxSlicedRepr s.mem (stackArg s 4) (s.gpr .a0)

/-- `vg_aes_gcm_open_to_bitsliced`: `vg_aes_gcm_open_to`'s postcondition and leak. -/
def openToBsRISCV64 : Contract isa where
  pre := openToBsPreR
  post := openToRISCV64.post
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ (rounds (s₁.gpr .a1) → (openToRes s₁).isSome = (openToRes s₂).isSome)

/-- What the body needs of `vg_aes_gcm_open_to_bitsliced`'s arguments. -/
theorem openToBsPreR.opre {s₀ : State} (h : openToBsPreR s₀) :
    OPre true s₀ (stackArg s₀ 5) (stackArg s₀ 2) (stackArg s₀ 0) (stackArg s₀ 3).toNat := by
  obtain ⟨hrd, hwr, dcD, dcW, dnD, dnW, daD, daW, dsD, dsW, dDT, dDW, dDA, dtW, dWA, fc, fn, fa, fs, fD, ft, fW, fsp,
    hR, hstk, ca, wa, dl, -⟩ := h
  obtain mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  obtain hD : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₀.wr := by
    rw [hwr, ← dl]; exact covers_mem (List.mem_cons_self ..)
  obtain hb : ∀ r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
      ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩,
      ⟨stackArg s₀ 2, (stackArg s₀ 3).toNat⟩, ⟨stackArg s₀ 5, 2560⟩], r.Disjoint (below s₀.sp 2048) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain m : ∀ {x : Region}, x ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
        ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨stackArg s₀ 0, (stackArg s₀ 1).toNat⟩,
        ⟨stackArg s₀ 2, (stackArg s₀ 3).toNat⟩, ⟨stackArg s₀ 5, 2560⟩, args s₀ 6, ⟨stackArg s₀ 4, 1248⟩] →
        x.Disjoint (below s₀.sp 2048) := fun hx => hstk.buf hx
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m (.head _)
    · exact m (.tail _ (.head _))
    · exact m (.tail _ (.tail _ (.head _)))
    · exact m (.tail _ (.tail _ (.tail _ (.head _))))
    · rw [← dl]; exact m (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · exact m (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    · exact m (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  rw [dl] at dcD dsD dDW fD
  exact ⟨mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp),
    mr (by rw [hrd]; simp), by rw [hwr]; exact covers_mem (by simp), hD, dcW, dnW, daW, dsW, dtW, dDW, dcD, fc,
    fn, fa, fs, fD, fW, (stackArg s₀ 3).isLt, hb, hstk.1, hstk.2.1,
    hR, ca, wa, dsD⟩


/-- What `vg_aes_gcm_open_to_bitsliced`'s precondition says of `bk`. -/
theorem openToBsPreR.bkpre {s₀ : State} (h : openToBsPreR s₀) :
    BkPre true s₀ (stackArg s₀ 5) (stackArg s₀ 0) (stackArg s₀ 4) := by
  obtain ⟨hrd, hwr, dcD, dcW, dnD, dnW, daD, daW, dsD, dsW, dDT, dDW, dDA, dtW, dWA, fc, fn, fa, fs, fD, ft, fW, fsp,
    hR, hstk, ca, wa, dl, dbD, dbW, ba, hsl⟩ := h
  obtain hA : Covers [args s₀ 6] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  obtain db : (⟨stackArg s₀ 4, 960⟩ : Region).Disjoint ⟨stackArg s₀ 5, 2560⟩ :=
    dbW.sub_left (Region.sub_prefix (by decide))
  rw [dl] at dbD
  refine ⟨⟨?_, ba, db.sub_right (Lay.wSub (by decide)), db,
    (stkAll_mem hstk.2.2 (r := ⟨stackArg s₀ 4, 1248⟩) (by simp)).symm.sub_left (Region.sub_prefix (by decide)),
    dbD.sub_left (Region.sub_prefix (by decide)), keysAt_of_sliced hR14 hsl⟩, rfl,
    args_in hA (by decide) (i := 4) (by decide), fun r hr => ?_⟩
  · exact covers_appL (covers_prefix (k := 1248) (covers_mem (by rw [hrd]; simp)) (by decide))
  · refine Region.Disjoint.sub_left ?_ (Offset.sub s₀.sp (d := 32) (n := 8) (e := 0) (k := 48) (by decide) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dWA.symm
    · exact (stkAll_mem hstk.2.2 (r := args s₀ 6) (by simp)).symm

/-- The entry of `vg_aes_gcm_open_to_bitsliced`: `oneEntryAt 40 16`, `tag_len` into
`s8`, and `dst - src` into `W + dstO`. -/
theorem openToBsEntry_wp {s₀ : State} (h : openToBsPreR s₀) :
    WP isa (.block (openEntryWithB true true)) s₀ fun s₂ =>
      SO2 true (stackArg s₀ 5) (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 3 := by
  obtain ⟨hrd, hwr, dcD, dcW, dnD, dnW, daD, daW, dsD, dsW, dDT, dDW, dDA, dtW, dWA, fc, fn, fa, fs, fD, ft, fW, fsp,
    hR, hstk, ca, wa, dl, -⟩ := h
  obtain hW : Covers [⟨stackArg s₀ 5, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 6] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain ain : ∀ i < 6, InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * i)) 8 := fun i hi => by
    have := in_off hA (d := 8 * i) (n := 8) (by omega_using [hi]) (by omega_using [])
    rwa [stackArgAddr_0, add_ofNat_assoc, Nat.zero_add] at this
  obtain dA : (args s₀ 6).Disjoint (oneR (stackArg s₀ 5)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  obtain dAi : ∀ i < 6, (⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (oneR (stackArg s₀ 5)) :=
    fun i hi => by
      obtain hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8 * i) (n := 8) (k := 48) (by omega_using [hi])
      rw [add_ofNat_assoc, Nat.zero_add] at hs
      exact dA.sub_left hs
  obtain spa : s₀.sp.toNat % 8 = 0 := by have := hstk.1; omega_using [this]
  simp only [openEntryWithB, ↓reduceIte]
  refine WP.block_append (WP.mono (WP.keep [.t1, .s0, .s1, .s2, .s3, .s4, .s5, .s7, .s9, .s10, .s11]
    (one1At_wp (off := 40) (tagO := 16) (W := stackArg s₀ 5) (T := stackArg s₀ 2) (by decide) (.inr rfl) hW
      wa hstk.1 (ain 5 (by decide)) rfl (ain 2 (by decide)) rfl (dAi 2 (by decide))) (by rfl) rfl)
    fun s₁ ⟨h1, kp⟩ => ?_)
  have hk₁ := h1.keeps
  obtain hv : ∀ i < 6, s₁.mem.readW (s₀.sp + BitVec.ofNat 64 (8 * i)) 64 = stackArg s₀ i := fun i hi => by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAi i hi) (by decide)]
    rfl
  obtain hv3 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 24) 64 = stackArg s₀ 3 := hv 3 (by decide)
  obtain hv0 : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 0) 64 = stackArg s₀ 0 := hv 0 (by decide)
  obtain in3 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 24) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 3 (by decide)
  obtain in0 : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 0) 8 := by
    rw [hk₁.rd, hk₁.wr]; exact ain 0 (by decide)
  refine Steps.wp_ld (off := 24) (a := s₀.sp + BitVec.ofNat 64 24) (by decide) (by rw [h1.t1])
    (Spill.al8 spa (by decide)) in3 fun s₂ u₂ => ?_
  refine Steps.wp_ld (off := 0) (a := s₀.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [u₂.other _ (by decide), h1.t1]) (Spill.al8 spa (by decide)) (by rw [u₂.rd, u₂.wr]; exact in0)
    fun s₃ u₃ => ?_
  refine Steps.wp_sub fun s₄ u₄ => ?_
  obtain e0 : s₄.gpr .s0 = stackArg s₀ 5 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h1.s0]
  refine Steps.wp_sd (off := dstO) (a := stackArg s₀ 5 + BitVec.ofNat 64 dstO) (by decide) (by rw [e0])
    (Spill.al8 wa (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, hk₁.wr]; exact in_off hW (show dstO + 8 ≤ 2560 by decide) (by decide))
    fun s₅ m₅ => WP.block_nil ?_
  obtain t2 : s₄.gpr .t2 = stackArg s₀ 0 - s₀.gpr .a6 := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), kp.gpr (by decide), u₂.mem, hv0]
  obtain mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain hm : s₅.mem = s₁.mem.writeW (stackArg s₀ 5 + BitVec.ofNat 64 dstO) (stackArg s₀ 0 - s₀.gpr .a6) := by
    rw [m₅.mem, t2, mem₄]
  obtain g : ∀ r, r ≠ .s8 → r ≠ .t2 → s₅.gpr r = s₁.gpr r := fun r h8 h2 => by
    rw [m₅.gpr, u₄.other r h2, u₃.other r h2, u₂.other r h8]
  obtain dS : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 248 →
      (⟨stackArg s₀ 5 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint ⟨stackArg s₀ 5 + BitVec.ofNat 64 dstO, 8⟩ :=
    fun h₁ h₂ => Lay.w_w (.inl (by unfold dstO; omega_using [h₂])) (by omega_using [h₂]) (by decide)
  refine ⟨⟨⟨by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, hk₁.rd], by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, hk₁.wr],
      by rw [m₅.sp, u₄.sp, u₃.sp, u₂.sp, hk₁.sp]⟩, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · rw [hm]
    exact h1.saved.frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  · rw [hm]
    exact (h1.frame.sub inW_one).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))
  · rw [hm, Mem.readW_writeW_sep (Region.Disjoint.sep (dS (by decide) (by decide)) (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide)]
    exact h1.aad
  · rw [hm, Mem.readW_writeW_sep (Region.Disjoint.sep (dS (by decide) (by decide)) (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide)]
    exact h1.dat
  · rw [hm, Mem.readW_writeW_self64]
  · rw [g _ (by decide) (by decide)]; exact h1.s0
  · rw [g _ (by decide) (by decide)]; exact h1.s1
  · rw [g _ (by decide) (by decide)]; exact h1.s2
  · rw [g _ (by decide) (by decide)]; exact h1.s3
  · rw [g _ (by decide) (by decide)]; exact h1.s4
  · rw [g _ (by decide) (by decide)]; exact h1.s5
  · rw [g _ (by decide) (by decide)]; exact h1.s7
  · rw [g _ (by decide) (by decide)]; exact h1.s10
  · rw [g _ (by decide) (by decide)]; exact h1.s11
  · rw [g _ (by decide) (by decide)]; exact h1.s9
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hv3]

theorem openToBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : openToBsRISCV64.pre s₀) :
    WP isa OpenTo.openToBs s₀ fun s' => abiPreserved s₀ s' ∧ openToBsRISCV64.post s₀ s' := by
  have h' : openToBsPreR s₀ := h
  have hp := h'.opre
  have hW : Covers [⟨stackArg s₀ 5, 2560⟩] s₀.wr := hp.w
  unfold OpenTo.openToBs openWithB
  refine WP.seq (WP.mono (openToBsEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  refine openB_body hp h'.bkpre h2 (by rw [h19]; simp) fun s₅ br => ?_
  obtain hres : openToRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧
      OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat then
      some (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)) else none := by
    simp only [openToRes, openResult, decryptWith]
    by_cases hl : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true
    · simp only [hl, ite_true, true_and]
    · simp only [hl, false_and, ite_false, Bool.false_eq_true]
  show WP isa (.seq (.ite (.zero .a0) wipe (.block [])) (.block restore)) s₅ _
  obtain hW₅ : Covers [⟨stackArg s₀ 5, 2560⟩] (s₅.rd ++ s₅.wr) := by rw [br.rd, br.wr]; exact Covers.right hW
  -- the destination zeroed if the result is 0
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => s₆.gpr .s0 = stackArg s₀ 5 ∧ s₆.sp = s₀.sp ∧ s₆.rd = s₀.rd ∧
      s₆.wr = s₀.wr ∧ SavedAt s₆.mem (stackArg s₀ 5) s₀ ∧ s₆.gpr .a0 = s₅.gpr .a0 ∧
      (Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat →
        bytesAt s₆.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat = bytesAt s₅.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat) ∧
      (¬(Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat) →
        bytesAt s₆.mem (stackArg s₀ 0) (s₀.gpr .a7).toNat = List.replicate (s₀.gpr .a7).toNat 0)) ?_
    fun s₆ ⟨h31, hsp, hrd, hwr, hsv, ha0, hg, hb⟩ => ?_)
  · by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat
    · refine WP.ite false (by rw [Steps.eval_zero, (br.good hx).1]; rfl) (fun hf => absurd hf (by decide))
        (fun _ => WP.block_nil ⟨br.s0, br.sp, br.rd, br.wr, br.saved, rfl, fun _ => rfl, fun hn => absurd hx hn⟩)
    · refine WP.ite true (by rw [Steps.eval_zero, (br.bad hx).1]; rfl) (fun _ => ?_) (fun hf => absurd hf (by decide))
      obtain hdw : Covers [⟨stackArg s₀ 0, (s₀.gpr .a7).toNat⟩] s₅.wr := by rw [br.wr]; exact hp.dst
      refine WP.mono (wipe_ok (S := s₀.gpr .a6) br.s0 hp.wa hW₅ br.dat (br.dst rfl) (by rw [br.s11]; simp)
        (s₀.gpr .a7).isLt hp.fD hdw) fun u ⟨pz, fu, gu, rdu, wru, spu⟩ => ?_
      obtain g0 : u.gpr .s0 = stackArg s₀ 5 := by rw [gu _ (by decide) (by decide) (by decide)]; exact br.s0
      obtain ga : u.gpr .a0 = s₅.gpr .a0 := gu _ (by decide) (by decide) (by decide)
      obtain sv : SavedAt u.mem (stackArg s₀ 5) s₀ := br.saved.frame fu fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dDW.sub_right (Lay.wSub (d := 128) (n := 104) (by decide))).symm
      exact ⟨g0, spu.trans br.sp, rdu.trans br.rd, wru.trans br.wr, sv, ga, fun hn => absurd hn hx,
        fun _ => bytesAt_zeros pz⟩
  · refine WP.mono (restore_ok h31 hp.wa (by rw [hrd, hwr]; exact Covers.right hW) hsv hsp)
      fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, ?_⟩
    unfold openToBsRISCV64 openToRISCV64
    dsimp only
    rw [hm, h3, ha0]
    by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 3).toNat = true ∧ OpenTagOk s₀ (stackArg s₀ 2) (stackArg s₀ 3).toNat
    · rw [hres, ite_eq_left_of_eq_true _ _ (eq_true hx)]
      exact ⟨by rw [(br.good hx).1]; rfl, (hg hx).trans (br.good hx).2⟩
    · rw [hres, ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact ⟨by rw [(br.bad hx).1]; rfl, hb hx⟩

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem openToBs_one {t₀ s : State} (h : openToBsPreR t₀)
    (h1 : SO2 true (stackArg t₀ 5) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s) (h19 : s.gpr .s8 = stackArg t₀ 3) :
    OneO true (t₀.gpr .a0) (stackArg t₀ 5) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 2) (stackArg t₀ 3) (stackArg t₀ 0) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat ∧
      BkS true (t₀.gpr .a0) (stackArg t₀ 5) t₀.sp (t₀.gpr .a1).toNat (stackArg t₀ 4) (t₀.gpr .a6) (stackArg t₀ 0)
        (t₀.gpr .a7) s := by
  have hp := h.opre
  have hb := h.bkpre
  have hk₀ := hp.stk
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hN : DataOk (stackArg t₀ 5 + BitVec.ofNat 64 16) (stackArg t₀ 5) s (t₀.gpr .a2) (t₀.gpr .a3).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.nonce, (t₀.gpr .a3).isLt, hp.fn, hp.dnW.sub_right (Lay.wSub (by decide)),
      hp.dnW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hA : DataOk (stackArg t₀ 5 + BitVec.ofNat 64 16) (stackArg t₀ 5) s (t₀.gpr .a4) (t₀.gpr .a5).toNat :=
    ⟨by rw [hk₁.rd, hk₁.wr]; exact hp.aad, (t₀.gpr .a5).isLt, hp.fa, hp.daW.sub_right (Lay.wSub (by decide)),
      hp.daW, by rw [hk₁.sp]; exact hp.bufs _ (by simp)⟩
  have hT : Covers [⟨stackArg t₀ 2, (stackArg t₀ 3).toNat⟩] (s.rd ++ s.wr) := by
    rw [hk₁.rd, hk₁.wr]; exact hp.tag
  exact ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    h1.env hp.ctx hp.w hk₀, hN, hA, hp.dsrc.of_eq hk₁.rd hk₁.wr hk₁.sp, h1.aad, h1.dat⟩, h1.s9, h19, hT,
    ⟨hp.ddst.of_eq hk₁.rd hk₁.wr hk₁.sp, hp.alias⟩, h1.dst⟩, h1.s4, by rw [h1.s5]; exact toN,
    by rw [slot_keep h1.frame hb.dslot]; exact hb.slot, by rw [hk₁.rd, hk₁.wr]; exact hb.inr,
    hb.bk.frameW hp.rounds h1.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dcW
      · exact hk₀.c) hk₁.rd hk₁.wr⟩


theorem openToBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa openToBsRISCV64.pre openToBsRISCV64.pub OpenTo.openToBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openToBsPreR σ₁ := h₁
  have hp₁ := h₁'.opre
  have hbk := h₁'.bkpre
  have hR := hp₁.rounds
  let I₀ : State → Prop := fun s => openToBsPreR s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ stackArg s 3 = stackArg σ₁ 3 ∧
    stackArg s 4 = stackArg σ₁ 4 ∧ stackArg s 5 = stackArg σ₁ 5 ∧ (openToRes s).isSome = (openToRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm,
    q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qa 3 (by decide)).symm, (qa 4 (by decide)).symm,
    (qa 5 (by decide)).symm, (qres hR).symm⟩, ?_⟩
  unfold OpenTo.openToBs openWithB
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO2 true (stackArg t₀ 5) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 3
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openToBsEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 5 else σ₁.gpr r
    have hl : openEntryWithB true true = [.addSp .t1 0, .load .d .t1 .t1 40] ++ (oneRestAt 16 ++
        ([.load .d .s8 .t1 24, .load .d .t2 .t1 0, .sub .t2 .t2 .a6, .store .d .t2 .s0 dstO] : List Instr)) := by
      simp only [openEntryWithB, ↓reduceIte, oneEntryAt_eq, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead40_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, _, _, _, ea4, _⟩
      have hsa : s.sp.toNat % 16 = 0 := hs.opre.al
      obtain ⟨hrd, -⟩ := id hs
      have hA : Covers [args s 6] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
      refine WP.mono (oneAg_ok (W := stackArg s 5) (by decide) hsa (args_in hA (by decide) (i := 5) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea4, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openToRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO2 true (stackArg t₀ 5) (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 3 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 3) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 3).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 3).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := hp₁.lay
  let res := (openToRes σ₁).isSome
  let J₃ : State → Prop := fun s => s.gpr .s0 = stackArg σ₁ 5 ∧ s.sp = σ₁.sp ∧ s.gpr .s11 = σ₁.gpr .a7 ∧
    s.gpr .a0 = BitVec.ofNat 64 (if res then 1 else 0) ∧
    s.mem.readW (stackArg σ₁ 5 + BitVec.ofNat 64 dataO) 64 = σ₁.gpr .a6 ∧
    s.mem.readW (stackArg σ₁ 5 + BitVec.ofNat 64 dstO) 64 = stackArg σ₁ 0 - σ₁.gpr .a6 ∧
    Covers [⟨stackArg σ₁ 5, 2560⟩] (s.rd ++ s.wr) ∧ Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] s.wr
  refine CT.seq (J := J₃) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_)) (fun s hs => ?_) ?_
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
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) (o := true) (Dst := stackArg σ₁ 0) (kb := stackArg σ₁ 4) L₀ hR
        (hp₁.dtW.sub_right (Lay.wSub (by decide))) t1 t16 res hbk.dslot hp₁.al)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4b, ea4, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      have o := openToBs_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea2, ea3, ea4b, ea4, esp] at o
      refine ⟨o, openB_head hpre.opre hpre.bkpre h4 (by rw [h19₄.trans h19]; simp) hok₀ (T' := .block [])
        fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8]
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome = true then 1 else 0)
      rw [← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · -- what both branches leave: the result, which both runs agree on, and the slots `wipe` reads
    obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4b, ea4, eres⟩, h1, h19, g, k, h25⟩ := hs
    have hp := hpre.opre
    have hW₀ : Covers [⟨stackArg σ₁ 5, 2560⟩] (t₀.rd ++ t₀.wr) := by rw [← ea4]; exact Covers.right hp.w
    have hD₀ : Covers [⟨stackArg σ₁ 0, (σ₁.gpr .a7).toNat⟩] t₀.wr := by rw [← ea0, ← e10]; exact hp.dst
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, ea3, ea4b, ea4, eres⟩, h1, h19,
      g, k, h25⟩) (fun ht => ?_) (fun hf => ?_)
    · have hbad : ok = false := by
        cases e : ok
        · rfl
        · simp [e] at ht
      have hres : res = false := by
        show (openToRes σ₁).isSome = false
        simp only [openToRes, Spec.Gcm.openResult]
        rw [show Spec.Gcm.tagLenOk (stackArg σ₁ 3).toNat = false from hbad]
        rfl
      refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea4]
      · rw [u.sp, k.sp, h1.keeps.sp, esp]
      · rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s11, e10]
      · rw [u.gpr, hres]; rfl
      · rw [u.mem, k.mem, ← ea4, h1.dat, e9]
      · rw [u.mem, k.mem, ← ea4, h1.dst rfl, ea0, e9]
      · rw [u.rd, u.wr, k.rd, k.wr, h1.keeps.rd, h1.keeps.wr]; exact hW₀
      · rw [u.wr, k.wr, h1.keeps.wr]; exact hD₀
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 3).toNat = true := by rw [ea3]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so2 h1 g k u
      refine WP.mono (openB_good hp hpre.bkpre h4 (by rw [h19₄.trans h19]; simp) hok₀) fun s' bo =>
        ⟨by rw [bo.s0, ea4], by rw [bo.sp, esp], by rw [bo.s11, e10], ?_, by rw [← ea4, bo.dat, e9],
          by rw [← ea4, bo.dst rfl, ea0, e9], by rw [bo.rd, bo.wr]; exact hW₀, by rw [bo.wr]; exact hD₀⟩
      show _ = BitVec.ofNat 64 (if (openToRes σ₁).isSome then 1 else 0)
      rw [bo.a0, ← eres, openToRes_isSome hok₀]
      by_cases hx : OpenTagOk t₀ (stackArg t₀ 2) (stackArg t₀ 3).toNat
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  -- the end: the destination zeroed if the result is 0, then `restore`
  have ev₀ : ∀ s, J₃ s → isa.eval (.zero .a0) s = some (decide ((if res then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, h3, _⟩ => eval_zero h3 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 5 ∧ s.sp = σ₁.sp)
    (CT.ite _ ev₀ (fun _ => ?_) (fun _ => CT.skip)) (fun s hs => ?_) ?_
  · -- `wipe`: its first block, then its loop on the destination
    let J₄ : State → Prop := fun s => s.sp = σ₁.sp ∧ s.gpr .s0 = stackArg σ₁ 5 ∧ s.gpr .t2 = stackArg σ₁ 0 ∧
      s.gpr .t3 = BitVec.ofNat 64 (σ₁.gpr .a7).toNat
    unfold wipe
    refine CT.seq (J := J₄) ?_ (fun s ⟨h31, hsp, h23, _, hS, hδ, hW, _⟩ => WP.mono
      (wipeArgs_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp))
      fun s' ⟨t2, t3, _, g', k'⟩ => ⟨k'.sp.trans hsp, by rw [g' _ (by decide) (by decide) (by decide), h31], t2, t3⟩) ?_
    · obtain ⟨_, hc⟩ := wipeArgs_taint
      exact CT.taintEq _ (fun r => if r = .s0 then stackArg σ₁ 5 else σ₁.gpr .a7) σ₁.sp
        (fun s ⟨h31, hsp, h23, _⟩ => ⟨hsp, by simp [h31, h23]⟩) hc
    · obtain ⟨_, hc⟩ := wipeLoop_taint
      exact CT.taintEq _ (fun r => if r = .t2 then stackArg σ₁ 0 else BitVec.ofNat 64 (σ₁.gpr .a7).toNat) σ₁.sp
        (fun s ⟨hsp, _, h2, h3⟩ => ⟨hsp, by simp [h2, h3]⟩) hc
  · obtain ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩ := hs
    refine WP.ite _ (ev₀ s ⟨h31, hsp, h23, h3, hS, hδ, hW, hdw⟩) (fun _ => ?_) (fun _ => WP.block_nil ⟨h31, hsp⟩)
    have fD : (stackArg σ₁ 0).toNat + (σ₁.gpr .a7).toNat ≤ 2 ^ 64 := hp₁.fD
    exact WP.mono (wipe_ok h31 hp₁.wa hW hS hδ (n := (σ₁.gpr .a7).toNat) (by rw [h23]; simp) (σ₁.gpr .a7).isLt
      fD hdw) fun u ⟨_, _, gu, _, _, spu⟩ => ⟨by rw [gu _ (by decide) (by decide) (by decide)]; exact h31,
        spu.trans hsp⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

/-! ## The contracts

As `open_to`'s (`RoundsTo.lean`, `OpenTo/Verified.lean`), with the buffer `bk`
as a last argument, which the postcondition and the leak ignore and the
precondition requires to hold the bitsliced form of the key context. -/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- `openToRoundsPost`, which does not depend on `bk`. -/
def openToBitslicedRoundsPost (pb : Nat) : openToBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _bk =>
    openToRoundsPost pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen

def openToBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToBitslicedSig.contract A (pre := openToBitslicedPre A.ptrBits)
    (post := openToBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openToBitslicedLeak A.ptrBits))

theorem openToBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (openToBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.openToBitslicedContract A stack) :=
  h.post_mono fun ctx rounds n nl a al s l d dl t tl _ => openToPost_imp _ ctx rounds n nl a al s l d dl t tl

variable (pb : Nat)

/-- The thirteen words of the `_bitsliced` `open_to`: the plain function's twelve, then `bk`. -/
theorem openTo_words {α : Type} {vs : List α} (hlen : vs.length = 13) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 bk, vs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk] := by
  match vs, hlen with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk], _ =>
    exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk, rfl⟩

theorem openToBitslicedPre_local : ∀ vs m₁ m₂, vs.length = (openToBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs openToBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPre pb) vs m₁ →
      Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk, rfl⟩ := openTo_words hlen
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨RISCV64.OpenTo.openToPre_local pb [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] m₁ m₂ rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h₁, ?_⟩
  simp only [openToBitslicedSig, openToSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  exact ctxSlicedRepr_congr (agree_of hb.2.2.2.2.2.2) (agree_of hb.1) h₂

theorem openToBitslicedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openToBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs openToBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedRoundsPost pb) vs m₁ m' r →
      Curry.apply (openToBitslicedSig.words pb) (openToBitslicedRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk, rfl⟩ := openTo_words hlen
  exact RISCV64.OpenTo.openToPost_local pb [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] m₁ m₂ m' r rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem openToBitslicedPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (openToBitslicedSig.words pb).length →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPre pb) vs m →
    (∀ b ∈ Sig.bufs openToBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedRoundsPost pb) vs m m₁ r →
      Curry.apply (openToBitslicedSig.words pb) (openToBitslicedRoundsPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk, rfl⟩ := openTo_words hlen
  exact RISCV64.OpenTo.openToPostOut_local pb [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] m m₁ m₂ r rfl
    hpre.1 (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm)) h

theorem openToBitslicedLeak_local : ∀ vs m₁ m₂, vs.length = (openToBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs openToBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedLeak pb) vs m₁ =
      Curry.apply (openToBitslicedSig.words pb) (openToBitslicedLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, bk, rfl⟩ := openTo_words hlen
  exact RISCV64.OpenTo.openToLeak_local pb [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] m₁ m₂ rfl
    (fun b hbm => hb b (List.mem_append_left [((⟨bk, 156 * Elem.size .u64⟩ : Region), false)] hbm))

theorem openToBitslicedPost_out : ∀ vs m m₁ m₂ r, vs.length = (openToBitslicedSig.words pb).length →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPre pb) vs m →
    (∀ b ∈ Sig.bufs openToBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPost pb) vs m m₁ r →
      Curry.apply (openToBitslicedSig.words pb) (openToBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  obtain ⟨x0, x1, x2, x3, x4, x5, src, len, dst, dl, x10, x11, bk, rfl⟩ := openTo_words hlen
  simp only [openToBitslicedSig, openToSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openToBitslicedPre pb) _ m at hpre
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openToBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openToBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, openToBitslicedPre, openToPre, ArgWord.ofRaw, IntTy.bits] at hpre
  dsimp only [Curry.apply, openToBitslicedPost, openToPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro key hk
  have := Nat.mod_le dl.toNat (2 ^ pb)
  rw [bytesAt_congr (m₁ := m₁) (m₂ := m₂) (p := dst) (n := (len.setWidth pb).toNat) fun i hi =>
    agree_of hb.2.2.2.2.1 i (by
      rw [← hpre.1.2, BitVec.toNat_setWidth] at hi; omega_using [this, hi])]
  exact h key hk

end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- Memory holding the stack arguments at `0x9000`: `dst` (`0x7000`),
`dst_len` 0, `tag` (`0x5000`), `tag_len` 0, `bk` (`0x800`) and the
working space (`0x6000`). -/
def toBsSatMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x9001 then 0x70 else bif Nat.beq a.toNat 0x9011 then 0x50 else
    bif Nat.beq a.toNat 0x9021 then 0x08 else bif Nat.beq a.toNat 0x9029 then 0x60 else 0

theorem toBsSatMem_zero {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x9001) :
    ∀ i < n, toBsSatMem (p + BitVec.ofNat 64 i) = 0 := fun i hi => by
  obtain e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h, hi]
  obtain hb : ∀ k, 0x9001 ≤ k → Nat.beq (p.toNat + i) k = false := fun k hk => by
    rw [← Bool.not_eq_true, Nat.beq_eq]; omega_using [h, hi, hk]
  simp only [toBsSatMem, e, hb _ (Nat.le_refl _), hb 0x9011 (by decide), hb 0x9021 (by decide),
    hb 0x9029 (by decide), Bool.cond_false]

/-- `openToBsPreR`, with no nonce, additional data, text or tag, and the
stack arguments'. -/
def toBsSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem := toBsSatMem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x800, 1248⟩, ⟨0x9000, 48⟩]
  wr := [⟨0x7000, 0⟩, ⟨0x6000, 2560⟩]

/-- As `openTo_verified`. -/
theorem openToBs_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target OpenTo.openToBs
      (Sig.scratchContract RISCV64.abi Spec.Gcm.openToBitslicedSig "work" .u64 320 (Spec.Gcm.openToBitslicedPre 64)
        (Proof.AesGcm.openToBitslicedRoundsPost 64) true 2048 (some (Spec.Gcm.openToBitslicedLeak 64))) :=
  Verified.of_correct (fun _ hs => openToBs_wp hs) openToBs_ct
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToBitslicedSig, Spec.Gcm.openToSig, Spec.Gcm.bitslicedParam, Spec.Gcm.openToBitslicedPre,
          Spec.Gcm.openToPre, openToBsRISCV64, openToBsPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToBitslicedSig,
          Spec.Gcm.openToSig, Spec.Gcm.bitslicedParam, Proof.AesGcm.openToBitslicedRoundsPost,
          Proof.AesGcm.openToRoundsPost, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop]
        simp only [openToBsRISCV64, openToRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToBitslicedSig,
          Spec.Gcm.openToSig, Spec.Gcm.bitslicedParam, Spec.Gcm.openToBitslicedLeak, Spec.Gcm.openToLeak,
          openToBsRISCV64, openToBsPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi])
            with rfl | rfl | rfl | rfl | rfl | rfl
          exacts [a0, a1, a2, a3, a4, a5]
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := ⟨toBsSat, by
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToBitslicedSig,
          Spec.Gcm.openToSig, Spec.Gcm.bitslicedParam, Spec.Gcm.openToBitslicedPre, Spec.Gcm.openToPre,
          RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop, toBsSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.ctxSlicedRepr_of_zero (toBsSatMem_zero (by decide)) (toBsSatMem_zero (by decide))⟩ }

/-! ## With the working space on the stack -/

def toBsFrameSat : State :=
  { toBsSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x800, 1248⟩,
      ⟨0x9000, 40⟩], wr := [⟨0x7000, 0⟩] }

theorem toBsFrameSat_pre : ∃ s, (Proof.AesGcm.openToBitslicedRoundsContract RISCV64.abi 4656).pre s := by
  refine ⟨toBsFrameSat, ?_⟩
  sig_pre [Proof.AesGcm.openToBitslicedRoundsContract, Spec.Gcm.openToBitslicedSig, Spec.Gcm.openToSig,
    Spec.Gcm.bitslicedParam, Spec.Gcm.openToBitslicedPre, Spec.Gcm.openToPre, Proof.AesGcm.openToBitslicedRoundsPost,
    Spec.Gcm.openToBitslicedLeak, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
    List.range.loop, toBsFrameSat, toBsSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.ctxSlicedRepr_of_zero (toBsSatMem_zero (by decide)) (toBsSatMem_zero (by decide))

theorem openToBs_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2608 5 OpenTo.openToBs)
      (Proof.AesGcm.openToBitslicedRoundsContract RISCV64.abi 4656) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openToBitslicedSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openToBitslicedPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.openToBitslicedRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2608) (m := 5)
    (leak := some (Spec.Gcm.openToBitslicedLeak RISCV64.abi.ptrBits))
    openToBs_verified (by decide) (by decide) (Proof.AesGcm.openToBitslicedPre_local _)
    (Proof.AesGcm.openToBitslicedPost_local _) (Proof.AesGcm.openToBitslicedPostOut_local _) toBsFrameSat_pre
    (hleak := Proof.AesGcm.openToBitslicedLeak_local _)

/-! ## Without secret residue -/

open VG.RISCV64.Scrub

theorem openToBsOut :
    PostOut (Spec.Gcm.openToBitslicedContract RISCV64.abi 4656) (Spec.Gcm.openToBitslicedSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain (Proof.AesGcm.openToBitslicedPost_out _)

/-- `vg_aes_gcm_open_to_bitsliced` as emitted (`Impl.AesGcm.RISCV64.Fn.openToBs`) meets its contract
in constant time and returns without secret residue: the theorem its registration binds. -/
theorem openToBs_scrubbed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    VerifiedScrubbed target Impl.AesGcm.RISCV64.Fn.openToBs
      (Spec.Gcm.openToBitslicedContract RISCV64.abi 4656) 32 :=
  verifiedScrubbedSelT (api := Spec.Gcm.openToBitslicedApi) (W := 4656)
    { code := Impl.StackScratch.RISCV64.withStackScratchArgs 2608 5 Impl.AesGcm.RISCV64.OpenTo.openToBs
      verified := Proof.AesGcm.openToBitsliced_keyed openToBs_framed }
    [(2048, [(0, 256)]), (2048, [(0, 256)]), (160, [(0, 20)])] []
    openToBsOut (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.AesGcm.RISCV64
