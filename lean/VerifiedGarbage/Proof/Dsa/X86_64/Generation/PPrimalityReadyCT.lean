module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstruct
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Encoding
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Construction preserves the public primality inputs and entropy cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pPrimality_ready {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore n H pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pConstruct G pLen qLen) s (PPrimalityAfter p) := by
  obtain ⟨⟨W, hw, hs, _, hu⟩, hwr, hub, tape, writable, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have step := pConstruct_ok hG hmatch hsize
    (p := q.construct) (hd.trans hq.symm) hs
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
  change WP isa (Impl.Dsa.X86_64.Generation.pConstruct G p.plan.construct.len p.plan.construct.hash.len) s _ at step
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨bt, _, ho, hb, L, ⟨V, R⟩, ws, ptr, ff, rd, wr⟩ => ?_
  have bt' : Spec.Rsa.bytesAt t.mem (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
      p.plan.construct.len = Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value := by
    simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
      PConstructPlan.value, hw.1 5 (by decide)] using bt
  have sq := source_of_frame tape ff q.tapeConstruct p.plan.randMax rd wr
  refine ⟨L, ⟨V, W, R, hw, hu⟩, ws, ?_, bt', ho, hb, ?_, sq, ?_, wr.trans hwr, hub⟩
  · simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
      hw.1 5 (by decide)] using ptr
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.plan.construct.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
      obtain ⟨r, hr, hc⟩ := hs.pWrite i hi'
      rw [rd, wr]
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using hc
    · intro i hi
      rw [List.getElem_eq_getD (0 : Byte), ← bt']
      have hi' : i < p.plan.construct.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
      simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi']
    · intro i hi
      exact p.plan.construct.pOutside i (by simpa only [VG.Proof.Dsa.encodeBE_length] using hi)
  · intro i hi; rw [wr]; exact writable i hi

end VG.Proof.Dsa.X86_64.Generation
