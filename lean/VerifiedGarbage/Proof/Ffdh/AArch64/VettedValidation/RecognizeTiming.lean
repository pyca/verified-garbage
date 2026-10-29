module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.TimingState
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableFrame
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices

/-! The recognizer leaks only the public inputs, with no dependence on scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open Cached

theorem entry_ct : RelCT isa (Two Ready)
    (.block VG.Impl.Ffdh.AArch64.VettedValidation.entry) (fun _ _ =>True) :=
  two_taint [.x3] (fun _ _ _ hs ht r hr =>by
    have same : r= .x3 := by simpa using hr
    subst r
    exact hs.base.trans ht.base.symm) (by taint_decide)

theorem loop_base {q : Public} {s : State} (h : PolicyLoopReady (loopPublic q) s) :
    WP isa (.loop Policy.record (.nonzero .x .x7)) s (fun t =>t.gpr .x0=q.B) := by
  have r:=h.record
  refine WP.mono (policyLoop_ok r.scratch q.room r.base r.source h.records q.shape
    (by have :=q.small;omega) (by have :=q.large;omega) r.domain r.length r.keyLength
    r.width (loopPublic q).fit r.pointer h.count (by simp) (by change 10<2^64;decide)) ?_
  rintro t ⟨_,_,rest⟩
  exact (rest.gpr .x0 (by simp [recordClobbers])).trans r.base

theorem recognize_ct : RelCT isa (Two Ready)
    VG.Impl.Ffdh.AArch64.VettedValidation.recognize (fun _ _ =>True) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.recognize
  refine RelCT.seq (two_post entry_ct (fun _ _ h =>entry_ready h)) ?_
  refine RelCT.seq (two_post (two_map loopPublic (fun _ _ h =>h) policyLoop_ct)
    (fun _ _ h =>loop_base h)) ?_
  exact two_taint [.x0] (fun _ _ _ hs ht r hr =>by
    have same : r= .x0 := by simpa using hr
    subst r
    exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Ffdh.AArch64.VettedValidation
