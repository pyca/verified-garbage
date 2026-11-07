module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OpenTo.CryptTo
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
destination after them on the stack (`splitPre`). Its entry, and the
computation and comparison of the tags, are `open`'s, by the same proofs
(`openEntry_wp`, `open_head`, from `HeadPre`); if the tags are equal, it
decrypts the source to the destination (`split_tail`, by `oneCryptTo_ok`),
and otherwise it leaves the destination as it was, which its callers then
zero (`splitPPC64LE`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros j0 inc32 gctr decryptWith openResult)

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
structure SplitOut (s₀ s : State) : Prop where
  r31 : s.gpr .r31 = stackArg s₀ 2
  sp : s.sp = s₀.sp
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  post : SplitPost s₀ s

/-- The destination's address, at `sp + 120`, as on entry: it is apart from `W`. -/
theorem dst_at {s₀ s : State} (h : splitPre s₀) (hf : Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem) :
    s.mem.readW (s₀.sp + BitVec.ofNat 64 120) 64 = stackArg s₀ 3 := by
  obtain ⟨_, _, _, _, _, _, _, dWA, _⟩ := h
  have hc : (args s₀ 4).Contains (s₀.sp + BitVec.ofNat 64 120) 8 := by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 24) (n := 8) (k := 8 * 4) (by decide) (by decide)
    rwa [stackArgAddr_0, add_ofNat_assoc] at this
  rw [Frame.readW hf hc (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dWA.symm) (by decide)]
  rfl

/-- `vg_aes_gcm_open_split` from the comparison's result on. -/
theorem split_tail {s₀ s₄ s₉ : State} (h : splitPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) (om : OpenMid s₀ s₄ s₉) :
    WP isa (.seq (.ite (.zero .d .r19) (.block []) oneCryptTo) (.block [mov .r3 .r19])) s₉ (SplitOut s₀) := by
  have hh := h
  obtain ⟨hrd, hwr, dcW, dnW, daW, ddW, dtW, dWA, dcD, dsD, dDW, fc, fn, fa, fd, ft, fW, fD, fsp, hR⟩ := hh
  have L₀ := oneLay fc fW dcW
  have hk₄ := h4.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  have h28 : s₄.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [h4.r28]; exact toN
  let iv := bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat
  let H := ctxH s₀.mem (s₀.gpr .r3)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  have rd₀ : s₉.rd = s₀.rd := rd₉.trans hk₄.rd
  have wr₀ : s₉.wr = s₀.wr := wr₉.trans hk₄.wr
  have dat₉ : bytesAt s₉.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = ct :=
    bytes_W F₉ ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
  have hDst : DataW (s₀.gpr .r3) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₉ (stackArg s₀ 3) (s₀.gpr .r10).toNat := by
    have hw : Covers [⟨(stackArg s₀ 3), (s₀.gpr .r10).toNat⟩] s₉.wr := by rw [wr₀, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hw, (s₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩
  -- the data decrypted to the destination only if the tags are equal
  have mid : WP isa (.ite (.zero .d .r19) (.block []) oneCryptTo) s₉ fun s₁₀ =>
      Env s₉.gpr s₀.sp s₁₀ ∧ SavedAt s₁₀.mem (stackArg s₀ 2) s₀ ∧ s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      ((openTagOk s₀) → bytesAt s₁₀.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = gctr ciph (inc32 (j0 H iv)) ct) := by
    refine WP.ite _ (eval_zero om.r19 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(openTagOk s₀) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨he₉, sv₉, rd₉, wr₉, fun x => absurd x hx⟩
    · have L₉ : Lay (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) := by
        rw [e _ (by decide) (by decide), e _ (by decide) (by decide), e _ (by decide) (by decide), h4.r29, h4.r30,
          h4.r31]
        exact L₀
      have r29 : s₉.gpr .r29 = s₀.gpr .r3 := by rw [e _ (by decide) (by decide), h4.r29]
      have r30 : s₉.gpr .r30 = stackArg s₀ 2 + BitVec.ofNat 64 16 := by rw [e _ (by decide) (by decide), h4.r30]
      have r31 : s₉.gpr .r31 = stackArg s₀ 2 := by rw [e _ (by decide) (by decide), h4.r31]
      have r27 : s₉.gpr .r27 = s₀.gpr .r9 := by rw [e _ (by decide) (by decide), h4.r27]
      have r23 : s₉.gpr .r23 = s₀.gpr .r10 := by rw [e _ (by decide) (by decide), h4.r23]
      have h28₉ : s₉.gpr .r28 = BitVec.ofNat 64 (s₀.gpr .r4).toNat := by rw [e _ (by decide) (by decide)]; exact h28
      have hsrc : DataOk (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
        rw [r30, r31, r27, r23]
        exact ⟨by rw [rd₀, wr₀]; exact (HeadPre.of_split h).data, (s₀.gpr .r10).isLt, fd,
          ddW.sub_right (Lay.wSub (by decide)), ddW⟩
      have hdst : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (stackArg s₀ 3) (s₉.gpr .r23).toNat := by
        rw [r29, r30, r31, r23]; exact hDst
      have hsd : (⟨s₉.gpr .r27, (s₉.gpr .r23).toNat⟩ : Region).Disjoint ⟨(stackArg s₀ 3), (s₉.gpr .r23).toNat⟩ := by
        rw [r27, r23]; exact dsD
      have hi : InRegions (s₉.rd ++ s₉.wr) (s₀.sp + BitVec.ofNat 64 120) 8 := by
        rw [rd₀, wr₀]
        have hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
        have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
        rwa [stackArgAddr_0, add_ofNat_assoc] at this
      have cb₉ : blockAt s₉.mem (s₉.gpr .r30 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [r30]; exact om.cb
      refine WP.mono (WP.with_rdwr (oneCryptTo_ok L₉ he₉ h28₉ hR hsrc hdst hsd hi (dst_at h F₉)
        (icb := inc32 (j0 H iv)))) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [r30, r31, r23] at cf
      refine ⟨oc.env, sv₉.frame cf (saved_crFrame L₀ hDst), rd₁₀.trans rd₉, wr₁₀.trans wr₉, fun _ => ?_⟩
      have ho := oc.out cb₉
      rw [r29, r27, r23, ciph_keep F₉ dcF hR, dat₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨he₁₀, sv₁₀, rd₁₀, wr₁₀, hd₁⟩ => ?_)
  -- the result back into `r3`
  refine WP.of_runBlock ⟨_, rfl, ?_⟩
  have g₁₁ : ∀ r, r ≠ .r3 → (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr r = s₁₀.gpr r := fun r hr => by
    simp [State.write, hr]
  have r3₁₁ : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = if (openTagOk s₀) then 1 else 0 := by
    have : (s₁₀.write .r3 (s₁₀.gpr .r19 ||| s₁₀.gpr .r19)).gpr .r3 = s₁₀.gpr .r19 := by simp [State.write]
    rw [this, he₁₀.fr _ (by decide), om.r19]
    by_cases hx : openTagOk s₀
    · simp only [eq_true hx, ite_true]; rfl
    · simp only [eq_false hx, ite_false]; rfl
  have hres : openRes s₀ = if (openTagOk s₀) then some (gctr ciph (inc32 (j0 H iv)) ct) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]; rfl
  refine ⟨by rw [g₁₁ _ (by decide), he₁₀.fr _ (by decide), e _ (by decide) (by decide), h4.r31],
    by simp only [State.write]; exact he₁₀.sp, fun r hr => ?_, by simp only [State.write]; rw [rd₁₀, hk₄.rd],
    by simp only [State.write]; rw [wr₁₀, hk₄.wr], by simp only [State.write]; exact sv₁₀, ?_⟩
  · have hf : r ∈ frozen := by revert hr; revert r; decide
    rw [g₁₁ r (by revert hr; revert r; decide), he₁₀.fr r hf, e r hf (by revert hr; revert r; decide)]
    exact h4.en.low r hr
  · unfold SplitPost
    by_cases hx : (openTagOk s₀)
    · rw [hres, ite_eq_left hx]
      exact ⟨r3₁₁.trans (ite_eq_left hx), hd₁ hx⟩
    · rw [hres, ite_eq_right hx]
      exact r3₁₁.trans (ite_eq_right hx)

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

theorem split_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ : State} (h : splitPPC64LE.pre s₀) :
    WP isa openSplit s₀ fun s' => abiPreserved s₀ s' ∧ splitPPC64LE.post s₀ s' := by
  have h' : splitPre s₀ := h
  have hp := HeadPre.of_split h'
  have hW := hp.w
  unfold openSplit openWith
  refine WP.seq (WP.mono (openEntry_wp hp) fun s₂ ⟨h2, h19⟩ => ?_)
  -- the tag length
  have h19' : s₂.gpr .r19 = BitVec.ofNat 64 (stackArg s₀ 1).toNat := by rw [h19]; simp
  refine WP.seq (WP.mono (tagLenOk_ok h19' (stackArg s₀ 1).isLt) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  have mid : WP isa (.ite (.zero .d .r25) (.block [.li .r3 0]) (openGoodWith oneCryptTo)) s₃ (SplitOut s₀) := by
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
      · unfold SplitPost
        rw [show openRes s₀ = none by simp only [openRes, openResult, hbad]; rfl]
        exact z3
    · have hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true := by
        cases e : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat
        · simp [e] at hf
        · rfl
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
      exact open_head hp h4 (by rw [e19, g₃ _ (by decide) (by decide)]; exact h19) hok fun _ om =>
        split_tail h' h4 hok om
  refine WP.seq (WP.mono mid fun s₅ oo => ?_)
  refine WP.mono (restore_ok oo.r31 (by rw [oo.rd, oo.wr]; exact Covers.right hW) oo.saved oo.sp oo.low)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, splitPost_out oo.post hm h3⟩

end VG.Proof.AesGcm.PPC64LE
