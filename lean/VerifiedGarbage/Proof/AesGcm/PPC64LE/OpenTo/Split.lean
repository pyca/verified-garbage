module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.Pass
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_open_split`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_split` is
`open`'s body (`openWith`) with `oneCryptTo` for `oneCrypt`: its arguments
are `open`'s, the data being the source, which it only reads, with the
destination after them on the stack (`splitPre`). Its proof is `open`'s,
`openWith_wp`, from `HeadPre`, with its own decryption (`split_dec`, by
`oneCryptTo_ok`) and postcondition: if the tags are equal, the destination
holds the plaintext, and otherwise it is as it was, which its callers then
zero (`splitPPC64LE`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `vg_aes_gcm_open_split` needs: `(ctx = r3, rounds = r4, nonce = r5,
nonce_len = r6, aad = r7, aad_len = r8, src = r9, len = r10, tag = [sp + 96],
tag_len = [sp + 104], scratch = [sp + 112], dst = [sp + 120])`: what `open`
needs, but the data is only read, with a destination of `len` bytes, apart
from the key context, the source and the working space. -/
def splitPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let src : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let scr : Region := ⟨stackArg s 2, 2560⟩
  let dst : Region := ⟨stackArg s 3, (s.gpr .r10).toNat⟩
  s.rd = [ctx, nonce, aad, src, tag, args s 4] ∧ s.wr = [dst, scr] ∧
    ctx.Disjoint scr ∧ nonce.Disjoint scr ∧ aad.Disjoint scr ∧ src.Disjoint scr ∧ tag.Disjoint scr ∧
    scr.Disjoint (args s 4) ∧ ctx.Disjoint dst ∧ src.Disjoint dst ∧ dst.Disjoint scr ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧ s.sp.toNat + 128 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4)

/-- `vg_aes_gcm_open_split`: the result in the low 32 bits of `r3`, and the
plaintext at `dst` if the tag is right. It may leak whether it succeeds. -/
def splitPPC64LE : Contract isa where
  pre := splitPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (stackArg s 3) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧ (rounds (s₁.gpr .r4) → (openRes s₁).isSome = (openRes s₂).isSome)

theorem HeadPre.of_split {s : State} (h : splitPre s) : HeadPre s := by
  obtain ⟨hrd, hwr, dcW, dnW, daW, ddW, dtW, dWA, _, _, _, fc, fn, fa, fd, ft, fW, _, _, hR⟩ := h
  have r : ∀ x, x ∈ s.rd → Covers [x] (s.rd ++ s.wr) := fun x hx => covers_mem (List.mem_append_left _ hx)
  refine ⟨r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp), r _ (by rw [hrd]; simp),
    r _ (by rw [hrd]; simp), covers_prefix (r (args s 4) (by rw [hrd]; simp)) (by decide),
    by rw [hwr]; exact covers_mem (by simp), dcW, dnW, daW, ddW, dtW,
    dWA.sub_right (Region.sub_prefix (by decide)), fc, fn, fa, fd, ft, fW, hR⟩

/-- What the end of `vg_aes_gcm_open_split` promises, given the result `r3`. -/
def SplitPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r3 = 1 ∧ bytesAt s.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = pt
  | none => s.gpr .r3 = 0

/-- What the end of `vg_aes_gcm_open_split` leaves for `restore`. -/
abbrev SplitOut := OutWith SplitPost

/-- The destination's address, at `sp + 120`, as on entry: it is apart from `W`. -/
theorem dst_at {s₀ s : State} (h : splitPre s₀) (hf : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem) :
    s.mem.readW (s₀.sp + BitVec.ofNat 64 120) 64 = stackArg s₀ 3 := by
  obtain ⟨_, _, _, _, _, _, _, dWA, _⟩ := h
  have hc : (args s₀ 4).Contains (s₀.sp + BitVec.ofNat 64 120) 8 := by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 24) (n := 8) (k := 8 * 4) (by decide) (by decide)
    rwa [stackArgAddr_0, add_ofNat_assoc] at this
  rw [Frame.readW hf hc (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dWA.symm) (by decide)]
  rfl

theorem split_some {s₀ : State} : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 →
    bytesAt s.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = openPt s₀ → SplitPost s₀ s := by
  intro s hr h1 hd; unfold SplitPost; rw [hr]; exact ⟨h1, hd⟩

theorem split_none {s₀ : State} : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
    Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → SplitPost s₀ s := by
  intro s hr h0 _; unfold SplitPost; rw [hr]; exact h0

/-- `vg_aes_gcm_open_split`, once the tag length is allowed, from `s₄` (after
the entry): the additional data hashed, the received tag copied to `W`, the
data decrypted to the destination in one pass with its tag computed, and the
tags compared. -/
theorem pass_good [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s₀ s₄ : State}
    (h : splitPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄) (h19 : s₄.gpr .r19 = stackArg s₀ 1)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    WP isa (.seq oneAad (.seq recv (.seq (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112)))
      (cmp 112)))) s₄ (SplitOut s₀) := by
  have hp := HeadPre.of_split h
  have hh := h
  obtain ⟨hrd, hwr, _, _, _, _, _, _, dcD, dsD, dDW, _, _, _, _, _, _, fD, _, _⟩ := hh
  have dcW := hp.dcW; have dnW := hp.dnW; have daW := hp.daW; have ddW := hp.ddW; have dtW := hp.dtW
  have fn := hp.fn; have fa := hp.fa; have fd := hp.fd; have hR := hp.hR
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have L₀ := oneLay hp.fc hp.fW dcW
  have he₄ := one_env h4 hp.ctx hp.w
  have L := L₀.v h4.r29 h4.r30 h4.r31
  have hk₄ := h4.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  have F₄ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₄.mem := h4.en.frame.sub inW_saved
  -- `oneAad`
  have hN : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₀.gpr .r5) (s₀.gpr .r6).toNat := by
    rw [h4.r30, h4.r31]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact hp.nonce,
      (s₀.gpr .r6).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  have hAd : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₄ (s₄.gpr .r21) (s₄.gpr .r22).toNat := by
    rw [h4.r30, h4.r31, h4.r21, h4.r22]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact hp.aad,
      (s₀.gpr .r8).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.r24 (by rw [h4.r25]; exact toN)
    (by rw [h4.r18]; exact toN) hN hAd)) fun s₅ ⟨oa, rd₅, wr₅, _⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.r30, h4.r31] at f₅
  have F₅ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `recv`
  have h19' : s₄.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; exact toN
  have hTr : Covers [⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩] (s₅.rd ++ s₅.wr) := by
    rw [rd₅, wr₅, hk₄.rd, hk₄.wr, h4.r20]
    exact hp.tag
  have hTd : (⟨s₄.gpr .r20, (stackArg s₀ 1).toNat⟩ : Region).Disjoint ⟨s₄.gpr .r31 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.r20, h4.r31]; exact dtW.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (recv_ok oa.env h19' t1 t16 hTr hTd) fun s₆ ⟨hb₆, hf₆, g₆, k₆⟩ => ?_)
  have he₆ := oa.env.keep (fun r hr => g₆ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₆.sp k₆.rd k₆.wr
  rw [h4.r31] at hf₆ hb₆
  have F₆ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₆.mem := F₅.trans (hf₆.sub (inW_at (by decide)))
  -- what the data and the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat
  let a := bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat
  let tg := bytesAt s₀.mem (stackArg s₀ 0) (stackArg s₀ 1).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat
  let H := ctxH s₀.mem (s₀.gpr .r3)
  let Dst := stackArg s₀ 3
  let W := stackArg s₀ 2
  have hW256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨s₄.gpr .r29, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    rw [h4.r29]; exact dcW.sub_right (Lay.wSub (by decide))
  have hH₄ : blockAt s₄.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [h4.r29]; exact ctxH_keep F₄ dcF
  have hH₆ : blockAt s₆.mem (s₄.gpr .r29 + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame hf₆ (fun r hr => (hW256 r hr).sub_left (Lay.ctxSub (by decide))), oa.hH, hH₄]
  have iv₄ : bytesAt s₄.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat = iv :=
    bytes_W F₄ dnW (by have := (s₀.gpr .r6).isLt; omega_arith)
  have a₄ : bytesAt s₄.mem (s₄.gpr .r21) (s₄.gpr .r22).toNat = a := by
    rw [h4.r21, h4.r22]; exact bytes_W F₄ daW (by have := (s₀.gpr .r8).isLt; omega_arith)
  have ct₆ : bytesAt s₆.mem (s₄.gpr .r27) (s₄.gpr .r23).toNat = ct := by
    rw [h4.r27, h4.r23]; exact bytes_W F₆ ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
  have hc₆ : ciphOf s₆.mem (s₄.gpr .r29) (s₀.gpr .r4).toNat = ciph := by rw [h4.r29]; exact ciph_keep F₆ dcF hR
  have st₆ : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨s₄.gpr .r30 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hdk r hr; simp only [List.mem_singleton] at hr; subst hr
    rw [h4.r30]; exact L₀.st_w hdk (.inr ⟨by decide, by decide⟩)
  have hj₆ : blockAt s₆.mem (s₄.gpr .r30) = j0 H iv := by
    rw [blockAt_frame hf₆ (by simpa using st₆ (d := 0) (k := 16) (by decide)), oa.j, hH₄, iv₄]
  have hcb₆ : blockAt s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame hf₆ (st₆ (by decide)), oa.cb, hH₄, iv₄]
  have hab₆ : Proof.Gcm.Absorbed s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 16) (s₄.gpr .r30 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)) := by
    have hx := oa.abs
    rw [hH₄, a₄] at hx
    refine hx.congr (blockAt_frame hf₆ (st₆ (by decide))) (bytesAt_frame hf₆ (st₆ ?_) (by omega))
    have := Nat.mod_lt (a ++ zeros (padLen a.length)).length (by decide : 0 < 16)
    omega
  have hr₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 1).toNat) := by
    rw [hb₆, h4.r20]; congr 1; exact bytes_W F₅ dtW (by omega_arith)
  have sv₆ : SavedAt s₆.mem W s₀ :=
    ((h4.en.saved.frame f₅ (saved_j0Frame L₀)).frame hf₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide))))
  have hl₂₂ : (s₄.gpr .r22).toNat = a.length := by rw [h4.r22, length_bytesAt]
  have h28 : s₄.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h4.r28]; exact toN
  -- the data and its tag, in one pass
  have mid : WP isa (.ite (.zero .d .r23) (oneTag 112) (.seq passData (finTag 112))) s₆ fun s₇ =>
      Env s₄.gpr s₀.sp s₇ ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr ∧
      bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct ∧
      bytesAt s₇.mem Dst (s₀.gpr .r10).toNat = openPt s₀ ∧
      bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - (stackArg s₀ 1).toNat) ∧
      SavedAt s₇.mem W s₀ := by
    have rd₆ : s₆.rd = s₀.rd := by rw [k₆.rd, rd₅, hk₄.rd]
    have wr₆ : s₆.wr = s₀.wr := by rw [k₆.wr, wr₅, hk₄.wr]
    have hd₆ : DataOk (s₄.gpr .r30) (s₄.gpr .r31) s₆ (s₄.gpr .r27) (s₄.gpr .r23).toNat := by
      rw [h4.r30, h4.r31, h4.r27, h4.r23]
      exact ⟨by rw [rd₆, wr₆]; exact hp.data, (s₀.gpr .r10).isLt, fd,
        ddW.sub_right (Lay.wSub (by decide)), ddW⟩
    have h23 : s₆.gpr .r23 = BitVec.ofNat 64 (s₀.gpr .r10).toNat := by
      rw [he₆.fr .r23 (by decide), h4.r23]; exact toN
    refine WP.ite _ (eval_zero h23 (s₀.gpr .r10).isLt) (fun ht => ?_) (fun hf => ?_)
    · -- no data
      have hz : (s₀.gpr .r10).toNat = 0 := by simpa using ht
      refine WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) he₆ h28 hR hH₆ hl₂₂ hab₆ hd₆))
        fun s₇ ⟨ot, rd₇, wr₇, _⟩ => ?_
      have f₇ := ot.frame
      rw [h4.r30, h4.r31] at f₇
      refine ⟨ot.env, rd₇, wr₇, ?_, ?_, ?_, sv₆.frame f₇ (saved_otFrame L₀ (.inr rfl))⟩
      · have ho := ot.out
        rw [h4.r31, hc₆, hj₆, ct₆, ← Proof.Gcm.fullTag_eq] at ho
        exact ho
      · simp only [hz, bytesAt, List.range_zero, List.map_nil, openPt]
        rw [Proof.Gcm.gctr_eq]; simp [Proof.Gcm.xorKs_nil]
      · rw [bytesAt_frame f₇ (fun r hr => ?_) (by decide)]
        · exact hr₆
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L₀.st_w (a := 0) (n := 48) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm.sub_right
            (by simpa using (Region.sub_prefix (by decide) : Region.Sub (⟨W + BitVec.ofNat 64 16, 48⟩ : Region) _))
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · -- the data, in one pass
      have hz : (s₀.gpr .r10).toNat ≠ 0 := by simpa using hf
      have wi : Pass.WholeIn s₄.gpr s₀.sp (s₀.gpr .r4).toNat Dst s₆ := by
        have hw : Covers [⟨Dst, (s₀.gpr .r10).toNat⟩] s₆.wr := by
          rw [wr₆, hwr]; exact covers_mem (by simp [Dst])
        refine ⟨he₆, h28, hR, hd₆, ?_, ?_, ?_, dst_at h F₆⟩
        · rw [h4.r29, h4.r30, h4.r31, h4.r23]
          exact ⟨⟨covers_left hw, (s₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩
        · rw [h4.r27, h4.r23]; exact dsD
        · rw [rd₆, wr₆]
          have hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
          have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
          rwa [stackArgAddr_0, add_ofNat_assoc] at this
      have hab₆' : Proof.Gcm.Absorbed s₆.mem (s₄.gpr .r30 + BitVec.ofNat 64 16) (s₄.gpr .r30 + BitVec.ofNat 64 32)
          (ctxH s₆.mem (s₄.gpr .r29)) (a ++ zeros (padLen a.length)) := by
        rw [ctxH_eq, hH₆]; exact hab₆
      refine WP.mono (Pass.pass_ok L wi hl₂₂ (by rw [h4.r23]; omega) hab₆') fun s₇ po => ?_
      have hc₆' : ctxCiph s₆.mem (s₄.gpr .r29) (s₀.gpr .r4).toNat = ciph := hc₆
      have hH' : ctxH s₆.mem (s₄.gpr .r29) = H := by rw [ctxH_eq]; exact hH₆
      have pf : ∀ r ∈ Pass.passFrame s₄.gpr Dst, (⟨W + BitVec.ofNat 64 256, 16⟩ : Region).Disjoint r ∧
          (savedR W).Disjoint r := by
        intro r hr
        simp only [Pass.passFrame, h4.r30, h4.r31, h4.r23, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨(dDW.sub_right (Lay.wSub (by decide))).symm, (dDW.sub_right (Lay.wSub (by decide))).symm⟩
        · have := (L₀.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
          exact ⟨by simpa only [BitVec.add_zero] using this, by simpa using L₀.saved_st (d := 0) (k := 80) (by decide)⟩
        · exact ⟨Lay.w_w (.inr (by decide)) (by decide) (by decide), saved_w (by decide) (.inl (by decide))⟩
        · exact ⟨Lay.w_w (.inl (by decide)) (by decide) (by decide), saved_w (by decide) (.inr (by decide))⟩
      refine ⟨po.env, po.rd, po.wr, ?_, ?_, ?_, sv₆.frame po.frame (fun r hr => (pf r hr).2)⟩
      · have ho := po.tag
        rw [h4.r31, hH', hc₆', hj₆, ct₆, ← Proof.Gcm.fullTag_eq] at ho
        exact ho
      · have ho := po.dst
        rw [hc₆', hcb₆, ct₆, h4.r23] at ho
        exact ho
      · rw [bytesAt_frame po.frame (fun r hr => (pf r hr).1) (by decide)]; exact hr₆
  refine WP.seq (WP.mono mid fun s₇ ⟨he₇, rd₇, wr₇, tag₇, dst₇, rcv₇, sv₇⟩ => ?_)
  -- `cmp 112`
  refine WP.mono (cmp_ok he₇ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_
  rw [h4.r31] at hf₈ h3₈
  have he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  let X := (fullTag ciph H iv a ct).take (stackArg s₀ 1).toNat = tg
  have hX : (bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 112) (stackArg s₀ 1).toNat ++
      zeros (16 - (stackArg s₀ 1).toNat) = bytesAt s₇.mem (stackArg s₀ 2 + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, tag₇, rcv₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .r3 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have dst₈ : bytesAt s₈.mem Dst (s₀.gpr .r10).toNat = openPt s₀ := by
    rw [bytesAt_frame hf₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDW.sub_right (Lay.wSub (by decide))) (by have := (s₀.gpr .r10).isLt; omega)]
    exact dst₇
  refine ⟨(he₈.fr .r31 (by decide)).trans h4.r31, he₈.sp, fun r hr => ?_,
    k₈.rd.trans (rd₇.trans (k₆.rd.trans (rd₅.trans hk₄.rd))),
    k₈.wr.trans (wr₇.trans (k₆.wr.trans (wr₅.trans hk₄.wr))),
    sv₇.frame hf₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide))), ?_⟩
  · exact (he₈.fr r (by revert hr; revert r; decide)).trans (h4.en.low r hr)
  · unfold SplitPost
    rw [openRes_eq hok]
    by_cases hx : openTagOk s₀
    · rw [ite_eq_left hx]
      exact ⟨r3₈.trans (ite_eq_left hx), dst₈⟩
    · rw [ite_eq_right hx]
      exact r3₈.trans (ite_eq_right hx)

/-- The contract's postcondition, from `SplitPost`, through `restore`. -/
theorem splitPost_out {s₀ s s' : State} (op : SplitPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .r3 = s.gpr .r3) :
    splitPPC64LE.post s₀ s' := by
  unfold SplitPost at op
  unfold splitPPC64LE
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op
  · exact ⟨by rw [op.1]; rfl, op.2⟩
  · rw [op]; rfl

theorem split_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s₀ : State}
    (h : splitPPC64LE.pre s₀) :
    WP isa openSplit s₀ fun s' => abiPreserved s₀ s' ∧ splitPPC64LE.post s₀ s' := by
  have h' : splitPre s₀ := h
  have hp := HeadPre.of_split h'
  have hW := hp.w
  unfold openSplit
  refine WP.seq (WP.mono (openEntry_wp hp) fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  have h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 1).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have F₂ : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s₂.mem := h2.en.frame.sub inW_saved
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) openPass) s₃ (SplitOut s₀) := by
    refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = false := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · rfl
        · simp [e] at ht
      have h₀ : WP isa (.block [.li .r3 0]) s₃ fun s' => s'.gpr .r3 = 0 ∧
          (∀ r, r ≠ .r3 → s'.gpr r = s₃.gpr r) ∧ Keeps s₃ s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      refine WP.mono h₀ fun s' ⟨z3, g, k⟩ => ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · rw [g _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.r31
      · rw [k.sp, k₃.sp]; exact h2.en.keeps.sp
      · rw [g r (by revert hr; revert r; decide), g₃ r (by revert hr; revert r; decide)
          (by revert hr; revert r; decide)]
        exact h2.en.low r hr
      · rw [k.rd, k₃.rd]; exact h2.en.keeps.rd
      · rw [k.wr, k₃.wr]; exact h2.en.keeps.wr
      · rw [k.mem, k₃.mem]; exact h2.en.saved
      · exact split_none s' (by simp only [openRes, openResult, hbad]; rfl) z3 (by rw [k.mem, k₃.mem]; exact F₂)
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · simp [e] at hf
        · rfl
      unfold openPass
      refine WP.seq (WP.of_runBlock ⟨_, rfl, ?_⟩)
      let s₄ := s₃.write .r25 (s₃.gpr .r18 ||| s₃.gpr .r18)
      have g₄ : ∀ r, r ≠ .r0 → r ≠ .r19 → s₄.gpr r = s₂.gpr r := fun r h0 h19 => by
        by_cases e : r = .r25
        · subst e
          have : s₄.gpr .r25 = s₃.gpr .r18 := by simp [s₄, State.write]
          rw [this, g₃ _ (by decide) (by decide), h2.r18, h2.r25]
        · have : s₄.gpr r = s₃.gpr r := by simp [s₄, State.write, e]
          rw [this, g₃ r h0 e]
      have h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄ := h2.keep g₄ ⟨k₃.mem, k₃.rd, k₃.wr, k₃.sp, k₃.lr⟩
      have e19 : s₄.gpr .r19 = s₃.gpr .r19 := by simp [s₄, State.write]
      exact pass_good h' h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, splitPost_out oo.post hm h3⟩

end VG.Proof.AesGcm.PPC64LE
