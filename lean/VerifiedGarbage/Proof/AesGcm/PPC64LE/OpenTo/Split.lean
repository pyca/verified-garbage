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

/-- The decryption of `vg_aes_gcm_open_split`, from the source to the
destination, which then holds the plaintext. -/
theorem split_dec {s₀ s₄ s₉ : State} (h : splitPre s₀) (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄)
    (om : OpenMid s₀ s₄ s₉) :
    WP isa oneCryptTo s₉
      (DecOut s₀ s₄ s₉ fun m => bytesAt m (stackArg s₀ 3) (s₀.gpr .r10).toNat = openPt s₀) := by
  have hp := HeadPre.of_split h
  have hh := h
  obtain ⟨hrd, hwr, dcW, _, _, ddW, _, _, dcD, dsD, dDW, fc, _, _, fd, _, fW, fD, _, hR⟩ := hh
  have M := om.at hp h4
  have hk₄ := h4.en.keeps
  have rd₀ : s₉.rd = s₀.rd := om.rd.trans hk₄.rd
  have wr₀ : s₉.wr = s₀.wr := om.wr.trans hk₄.wr
  have dcF : ∀ r ∈ [(⟨stackArg s₀ 2, 2560⟩ : Region)], (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact dcW
  have dat₉ : bytesAt s₉.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat = bytesAt s₀.mem (s₀.gpr .r9) (s₀.gpr .r10).toNat :=
    bytes_W om.frame ddW (by have := (s₀.gpr .r10).isLt; omega_arith)
  have hDst : DataW (s₀.gpr .r3) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) s₉ (stackArg s₀ 3)
      (s₀.gpr .r10).toNat := by
    have hw : Covers [⟨(stackArg s₀ 3), (s₀.gpr .r10).toNat⟩] s₉.wr := by rw [wr₀, hwr]; exact covers_mem (by simp)
    exact ⟨⟨covers_left hw, (s₀.gpr .r10).isLt, fD, dDW.sub_right (Lay.wSub (by decide)), dDW⟩, hw, dcD⟩
  have hsrc : DataOk (s₉.gpr .r30) (s₉.gpr .r31) s₉ (s₉.gpr .r27) (s₉.gpr .r23).toNat := by
    rw [M.r30, M.r31, M.r27, M.r23]
    exact ⟨by rw [rd₀, wr₀]; exact hp.data, (s₀.gpr .r10).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW⟩
  have hdst : DataW (s₉.gpr .r29) (s₉.gpr .r30) (s₉.gpr .r31) s₉ (stackArg s₀ 3) (s₉.gpr .r23).toNat := by
    rw [M.r29, M.r30, M.r31, M.r23]; exact hDst
  have hsd : (⟨s₉.gpr .r27, (s₉.gpr .r23).toNat⟩ : Region).Disjoint ⟨(stackArg s₀ 3), (s₉.gpr .r23).toNat⟩ := by
    rw [M.r27, M.r23]; exact dsD
  have hi : InRegions (s₉.rd ++ s₉.wr) (s₀.sp + BitVec.ofNat 64 120) 8 := by
    rw [rd₀, wr₀]
    have hA : Covers [args s₀ 4] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
    have := in_off hA (d := 24) (n := 8) (by decide) (by decide)
    rwa [stackArgAddr_0, add_ofNat_assoc] at this
  refine WP.mono (WP.with_rdwr (oneCryptTo_ok M.lay om.env M.r28 hR hsrc hdst hsd hi (dst_at h om.frame) (icb := inc32 (j0 (ctxH s₀.mem (s₀.gpr .r3)) (bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat)))))
    fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
  have cf := oc.frame
  rw [M.r30, M.r31, M.r23] at cf
  refine ⟨oc.env, om.saved.frame cf (saved_crFrame (oneLay fc fW dcW) hDst), rd₁₀.trans om.rd,
    wr₁₀.trans om.wr, ?_⟩
  have ho := oc.out M.cb
  rw [M.r29, M.r27, M.r23, ciph_keep om.frame dcF hR, dat₉] at ho
  exact ho

theorem split_some {s₀ : State} : ∀ s, openRes s₀ = some (openPt s₀) → s.gpr .r3 = 1 →
    bytesAt s.mem (stackArg s₀ 3) (s₀.gpr .r10).toNat = openPt s₀ → SplitPost s₀ s := by
  intro s hr h1 hd; unfold SplitPost; rw [hr]; exact ⟨h1, hd⟩

theorem split_none {s₀ : State} : ∀ s, openRes s₀ = none → s.gpr .r3 = 0 →
    Frame [(⟨stackArg s₀ 2, 2560⟩ : Region)] s₀.mem s.mem → SplitPost s₀ s := by
  intro s hr h0 _; unfold SplitPost; rw [hr]; exact h0

theorem split_good [VG.Proof.Gcm.PPC64LE.GhashLaw] {s₀ s₄ : State} (h : splitPre s₀)
    (h4 : SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₄) (h19 : s₄.gpr .r19 = stackArg s₀ 1)
    (hok : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .r19 .r3])
      (.seq (.ite (.zero .d .r19) (.block []) oneCryptTo) (.block [mov .r3 .r19]))))))) s₄ (SplitOut s₀) :=
  goodWith (HeadPre.of_split h) h4 h19 hok (fun _ om _ => split_dec h h4 om) split_some split_none

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
    WP isa openSplit s₀ fun s' => abiPreserved s₀ s' ∧ splitPPC64LE.post s₀ s' :=
  have h' : splitPre s₀ := h
  openWith_wp (HeadPre.of_split h') (fun _ _ h4 om _ => split_dec h' h4 om) split_some split_none
    (fun _ _ op hm h3 => splitPost_out op hm h3)

end VG.Proof.AesGcm.PPC64LE
