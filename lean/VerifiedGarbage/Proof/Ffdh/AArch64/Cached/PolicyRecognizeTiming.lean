module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecognizeTimingState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Full group recognition reveals only the public domain, never private entropy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem execAdr (s : State) (r : Reg) (sym : String) :
 exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) :=rfl

theorem policyRecognize_ct : RelCT isa (Two RecognizeReady) Policy.recognize (fun _ _ =>True) := by
 unfold Policy.recognize
 refine RelCT.seq (two_post (Ψ:=RecognizeBound)
  (two_map RecognizePublic.toPolicyBoundPublic (fun _ _ h =>h.toPolicyBoundReady) policyBound_ct)
  (fun _ _ h =>recognize_bound_ok h)) ?_
 refine RelCT.seq (two_piece (Ψ:=fun q s =>PolicyLoopReady (recognizedLoop q) s) []
  (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide) ?_)
  (two_map recognizedLoop (fun _ _ h =>h) policyLoop_ct)
 intro q s h
 refine WP.mono (WP.keep [.x4,.x7] (Q:=fun t =>t.gpr .x4=q.table ∧
  t.gpr .x7=BitVec.ofNat 64 10 ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [execAdr,h.symbol]
 · rintro t ⟨⟨ptr,count,mem⟩,rest⟩
   have records :=h.records.after_mem mem rest
   exact ⟨⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,h.source.of_mem mem rest,records.1,
    mem ▸ h.domain,mem ▸ h.length,mem ▸ h.keyLength,mem ▸ h.width,ptr⟩,records,count⟩

end VG.Proof.Ffdh.AArch64.Cached
