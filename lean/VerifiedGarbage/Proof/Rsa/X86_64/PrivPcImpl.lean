module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCT
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# `vg_rsa_private_checked_precomputed` as a callee

For each implementation `c` of the CRT, `vg_rsa_private_checked_precomputed`
calling it, as `Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it, is a
`PrivPcImpl` (`privPcOf`): correct and constant time under `chkPcContract`,
using its frame and two return addresses of stack, since its callees' callees
use none.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64

/-- An implementation of `vg_rsa_private_checked_precomputed`: its symbol and
code, correct and constant time under `chkPcContract`, writing `rsp` only by
its own frames, which with its calls use at most `stackBytesPc` bytes of
stack. -/
structure PrivPcImpl where
  name : String
  code : Prog isa
  ok : ∀ s, chkPcContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ chkPcContract.post s s'
  ct : ConstantTime isa chkPcContract.pre chkPcContract.pub code
  spSafe : code.all (fun i => !isa.writesSp i) = true
  depth : code.x86_64Depth ≤ stackBytesPc

/-- Its code for `c`, as `Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it. -/
def privPcCode (c : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivCheckedPc.code c.pcrtName c.pcrt c.pubOp.name c.pubOp.code

theorem privPcCode_depth (c : CrtImpl) : (privPcCode c).x86_64Depth ≤ stackBytesPc := by
  simp only [privPcCode, Impl.Rsa.X86_64.PrivCheckedPc.code, Impl.Rsa.X86_64.PrivCheckedPc.body,
    Impl.Rsa.X86_64.PrivCheckedPc.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp c.pcrtNosp, c.pcrtDepth,
    x86_64Depth_noSp c.pubOp.nosp, c.pubOp.depth]
  decide

/-- `vg_rsa_private_checked_precomputed` calling `c`. -/
def privPcOf (c : CrtImpl) : PrivPcImpl where
  name := Spec.Rsa.privateCheckedPrecomputedApi.name ++ c.suffix
  code := privPcCode c
  ok := codeP_correct c _
  ct := codeP_constantTime c _
  spSafe := codeP_spSafe c _
  depth := privPcCode_depth c

end VG.Proof.Rsa.X86_64
