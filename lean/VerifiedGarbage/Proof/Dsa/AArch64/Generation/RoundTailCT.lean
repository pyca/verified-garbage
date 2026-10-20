module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.RoundTail
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Completion branches only on the shared round's public result. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

structure RoundTailPublic where
  prime : PrimeParams
  pass : Bool

def RoundTailState (p : RoundTailPublic) (s : State) : Prop :=
  PrimeGood p.prime s ∧ word s.mem p.prime.B (8 * kFlag) = mask p.pass

def RoundTailTested (p : RoundTailPublic) (s : State) : Prop :=
  s.gpr .x0 = p.prime.B ∧ s.gpr .x3 = mask p.pass

theorem roundTail_test {p : RoundTailPublic} {s : State} (h : RoundTailState p s) :
    WP isa (.block [ldh .x3 kFlag]) s (RoundTailTested p) := by
  have hflagBound : kFlag < 32 := by decide
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask p.pass) (by
    brun [h.1.x0, h.2, hdr_enc (show kFlag < 32 by decide),
      h.1.scr.ld (show 8 * kFlag + 8 ≤ p.prime.Z by have := h.1.h256; omega)]) rfl rfl rfl)
    fun t ⟨h3, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans h.1.x0, h3⟩

theorem roundTail_ct : RelCT isa (Two RoundTailState) Impl.Dsa.AArch64.Generation.roundTail (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.roundTail
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := RoundTailTested) (two_taint [.x0] ?_ (by taint_decide))
    (fun _ _ h => roundTail_test h)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.x0.trans ht.1.x0.symm
  · refine two_ite (fun _ _ _ hs ht => by simp only [eval, State.read, hs.2, ht.2]) ?_ ?_
    all_goals exact two_taint [.x0] (fun _ _ _ hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hs.1.1.trans ht.1.1.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
