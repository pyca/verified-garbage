module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuildValue
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! # Preserve public candidate bytes and persistent arguments across hashing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pConstruct_ready {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PConstructPublic} {s : State}
    (h : PConstructBefore H pLen qLen p s) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G qLen ((8 * pLen - 1) / (8 * qLen)))
      (Impl.Dsa.AArch64.Generation.pShape qLen ((8 * pLen - 1) / (8 * qLen)) pLen)) s
      (CandidateWorkspaceBefore (pLen / 8) pLen qLen (p.workspace H)) := by
  obtain ⟨⟨W, hw, hs⟩, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have hl : 2 ≤ q.len ∧ q.len ≤ 1024 ∧ q.len = 8 * (q.len / 8) := by
    change 2 ≤ p.plan.len ∧ p.plan.len ≤ 1024 ∧ p.plan.len = 8 * (p.plan.len / 8)
    rcases p.plan.width with h | h | h <;> omega
  have hd' : G.D = q.hash.len := hd.trans hq.symm
  have hv := pBuild_value hG hmatch hsize hd' hs.hash hl.1 hl.2.1 q.hashRoom q.shapedSlot
    hs.shapedWrite q.shapedInput
  have hf := pBuild_ok hG hmatch hsize hd' hs.hash hl.1 hl.2.1 q.hashRoom q.hashCount
    (by simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
    q.shapedSlot hs.shapedWrite q.shapedInput q.shapedHash (Spec.Rsa.os2ip q.qb)
  have step := VG.Proof.Bignum.AArch64.wp_and hv hf
  change WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G p.plan.hash.len p.plan.hash.count)
    (Impl.Dsa.AArch64.Generation.pShape p.plan.hash.len p.plan.hash.count p.plan.len)) s _ at step
  rw [p.plan.hashCount, hp, hq] at step
  refine WP.mono step fun t ⟨bt, _, _, L, ⟨V, R⟩, rd, wr, _, ff⟩ => ?_
  have bt' : Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.plan.hash.W 5) shaped) p.plan.len =
      Spec.Dsa.encodeBE p.plan.len (p.plan.hash.shapedValue H p.plan.len) := by
    simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide), HashPlan.shapedValue,
      HashPlan.digest] using bt
  have sq := source_of_frame hs.qSource ff q.qHash
    (by rw [q.qLength]; have := q.hash.size; omega) rd wr
  refine ⟨?_, hs.scratch.congr wr, ?_, ?_, ?_⟩
  · refine ⟨L.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; exact L.ld (d := 8 * k) (n := 8) (by unfold VG.Impl.RsaOaep.AArch64.frameBytes; omega)
    · exact (R.fr 5 (by decide)).trans (hw 5 (by decide))
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        have hi' : i < p.plan.len := by
          simpa only [PConstructPublic.workspace, VG.Proof.Dsa.encodeBE_length] using hi
        obtain ⟨r, hr, hc⟩ := hs.shapedWrite i hi'
        rw [rd, wr]
        refine ⟨r, List.mem_append_right _ hr, ?_⟩
        simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords,
          hw 5 (by decide)] using hc
      · intro i hi
        simp only [PConstructPublic.workspace] at hi ⊢
        rw [List.getElem_eq_getD (0 : Byte), ← bt']
        have hi' : i < p.plan.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
        simp [Spec.Rsa.bytesAt, VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, hi']
      · intro i hi
        exact p.plan.shapedOutside i (by
          simpa only [PConstructPublic.workspace, VG.Proof.Dsa.encodeBE_length] using hi)
    · simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using sq
    · intro i hi
      have hi' : i < q.len := by
        change i < 8 * (p.plan.len / 8) at hi
        rw [hl.2.2]; exact hi
      rw [wr]
      simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using hs.pWrite i hi'
    · intro i hi
      have hi' : i < q.len := by
        change i < 8 * (p.plan.len / 8) at hi
        rw [hl.2.2]; exact hi
      rw [wr]
      simpa only [PConstructPublic.workspace, q, PConstructPlan.withWords, HashPlan.withWords, hw 5 (by decide)] using hs.exponentWrite i hi'
  · change p.plan.len / 8 = pLen / 8; rw [hp]
  · change (Spec.Dsa.encodeBE p.plan.len _).length = pLen; rw [VG.Proof.Dsa.encodeBE_length, hp]
  · exact p.plan.qLength.trans hq

end VG.Proof.Dsa.AArch64.Generation
