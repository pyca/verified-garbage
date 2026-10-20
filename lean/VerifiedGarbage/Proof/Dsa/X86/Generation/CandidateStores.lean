module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateStore
import VerifiedGarbage.Proof.Mont.Words32

/-! # Persist p and its generator exponent outside the reusable arithmetic workspace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem candidateStores_ok {s : State} {frame base : Addr} {size plen n : Nat} {parent : BitVec 32}
    (F : SearchFrame s frame) (S : Scr s base size) (saved : s.mem.readW (off frame 20) 32 = parent)
    (p4 : 4 ≤ plen) (pWidth : plen ≤ 8 * n) (pWords : plen % 4 = 0)
    (pRoom : candidateP + 8 * n ≤ size) (expRoom : candidateQuotient + 8 * n ≤ size)
    (pFit : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).toNat + plen ≤ 2 ^ 32)
    (eFit : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).toNat + plen ≤ 2 ^ 32)
    (pWrite : ∀ d k, d + k ≤ plen → InRegions s.wr
      (off ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64) d) k)
    (eWrite : ∀ d k, d + k ≤ plen → InRegions s.wr
      (off ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).setWidth 64) d) k)
    (pScratch : Region.Disjoint ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64, plen⟩ ⟨base, size⟩)
    (eScratch : Region.Disjoint ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).setWidth 64, plen⟩ ⟨base, size⟩)
    (pFrame : Region.Disjoint ⟨frame, frameBytes⟩ ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64, plen⟩)
    (pExponent : Region.Disjoint ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64, plen⟩
      ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).setWidth 64, plen⟩) :
    WP isa (candidateStores plen) s fun t =>
      Spec.Rsa.bytesAt t.mem ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64) plen =
        Spec.Dsa.encodeBE plen (wordsVal s.mem base candidateP n) ∧
      Spec.Rsa.bytesAt t.mem ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).setWidth 64) plen =
        Spec.Dsa.encodeBE plen (wordsVal s.mem base candidateQuotient n) ∧
      Frame [⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.p).setWidth 64, plen⟩,
        ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.exponent).setWidth 64, plen⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  unfold candidateStores
  refine WP.seq (WP.mono (bufferPointer_ok F saved .esi _) fun a ⟨si, ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (storePublic_ok (S.of_keeps Ka (by decide)) pRoom p4 pWidth pWords
    (by rw [si]; exact pFit) (by intro d k hk; rw [si, Ka.2.2]; exact pWrite d k hk)
    (by rw [si]; exact pScratch.symm.sub_left (Offset.sub_base _ pRoom))) fun b ⟨pb, Ob, Kb⟩ => ?_)
  rw [si, ma] at pb Ob
  have Fb := (F.keeps Ka (by decide)).keeps Kb (by decide)
  have Fp := copyOutside_frame Ob
  have savedB : b.mem.readW (off frame 20) 32 = parent := by
    rw [Fp.readW (r := ⟨frame, frameBytes⟩) (Offset.contains_base _ (by unfold frameBytes; decide) (by decide))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact pFrame) (by decide), saved]
  have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
  refine WP.seq (WP.mono (bufferPointer_ok Fb savedB .esi _) fun c ⟨ei, mc, Kc⟩ => ?_)
  have Ksc := Ksb.trans (Kc.mono (by decide))
  refine WP.mono (storePublic_ok (S.of_keeps Ksc (by decide)) expRoom p4 pWidth pWords
    (by rw [ei]; exact eFit) (by intro d k hk; rw [ei, Ksc.2.2]; exact eWrite d k hk)
    (by rw [ei]; exact eScratch.symm.sub_left (Offset.sub_base _ expRoom))) fun t ⟨eb, Ot, Kt⟩ => ?_
  rw [ei, mc] at eb Ot
  have Fe := copyOutside_frame Ot
  have exponent : wordsVal b.mem base candidateQuotient n = wordsVal s.mem base candidateQuotient n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply val32_congr
    intro j hj
    exact congrArg BitVec.toNat (Fp.readW (r := ⟨base, size⟩)
      (Offset.contains_base _ (by omega) (by have := S.nowrap; omega))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact pScratch.symm) (by decide))
  rw [exponent] at eb
  refine ⟨?_, eb, (Fp.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans
    (Fe.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)), Ksc.trans (Kt.mono (by decide))⟩
  rw [drawFrame_bytes Fe (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact pExponent)
    (by omega), pb]
end VG.Proof.Dsa.X86.Generation
