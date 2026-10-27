module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Complete p-search iteration, including its public continuation decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem searchIteration_ct_of (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen)
    (hl : 32 * pLen ≤ 12288) (hs : (8 * pLen - 1) / (8 * qLen) + 1 ≤ 12)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi])
      (.block (pSearchAdvanceHead (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))) hc).isSome = true) :
    RelCT isa (Two (SearchBefore n pLen qLen))
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter n pLen qLen)) := by
  unfold pSearchIteration
  simp only [seqs]
  have body : RelCT isa (Two (SearchBefore n pLen qLen)) (pAttempt G1 G256 T.run pLen qLen)
      (Two (SearchBodySized n pLen qLen)) := by
    refine two_post (searchBody_ct G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd) ?_
    intro p s h
    exact WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2.2.2⟩
  refine RelCT.seq body (two_post ((two_map SearchPublic.control (fun _ _ h => searchBody_control h)
    (searchTail_ct (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1) hl hs ht)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => searchIteration_tail h hl hs))

theorem searchIteration_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore n pLen qLen))
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter n pLen qLen)) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact searchIteration_ct_of G1 G256 T n hn H _ _ (by unfold GenerationSizes; decide)
      hG hmatch hsize hhash hseedsize hd (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
