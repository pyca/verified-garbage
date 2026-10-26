module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The primality completion policy branches only on the public round result -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Bignum.X86_64

structure RoundTailPublic where
  B : Addr
  Z : Nat
  w : Nat
  pass : Bool

def RoundTailState (p : RoundTailPublic) (s : State) : Prop :=
  (∃ mi, Good s p.B p.Z p.w mi) ∧ slot p.w 8 ≤ p.Z ∧ word s.mem p.B (8 * kFlag) = mask p.pass

def RoundTailTested (p : RoundTailPublic) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ s.zf = some (!p.pass)

theorem roundTail_ct : RelCT isa (Two RoundTailState)
    Impl.Dsa.X86_64.Generation.roundTail (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.roundTail
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := RoundTailTested) (two_taint [.rdi] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.rdi.trans ht.rdi.symm
  · intro p s h
    obtain ⟨mi, hg⟩ := h.1
    exact WP.mono (flagTest_ok hg h.2.1 h.2.2) fun t ⟨hz, _, hk⟩ =>
      ⟨(hk.gpr (by decide)).trans hg.rdi, hz⟩
  · refine two_ite_seq (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    all_goals
      exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hs.1.1.trans ht.1.1.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
