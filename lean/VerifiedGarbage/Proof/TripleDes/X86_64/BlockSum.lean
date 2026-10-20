module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The constant-time analysis of Triple DES's x86-64 block functions, once

OFB, CFB64 and CFB8 call `vg_triple_des_encrypt_block` at a taint that knows the same about memory in all of them: the
scratch buffer (region 2) at `r9` and `rdx`, the schedule's copy at `rdi`
and the block at `rsi`. The analyses of the calls are summaries
(`taint_summary`), which their checks use (`taint_decide_sum`) in place
of the analysis of the block function's 2170 instructions at each call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64

/-- What the modes have public at their calls of the block function (CFB8 has
`rax` and `rcx` too). -/
def τCall : X86_64.Taint.T :=
  { regs := .ofList [.rdx, .rsp, .rsi, .rdi, .r9, .r12, .r13], flags := true,
    lens := [8, 0, 8 * 121], bases := [(.r9, 2, 0), (.rdi, 2, 520), (.rsi, 2, 512), (.rdx, 2, 0)],
    xregs := .ofList [.xmm15] }

taint_summary encSum : taintS τCall (.call "vg_triple_des_encrypt_block" Impl.TripleDes.X86_64.encryptBlock)

end VG.Proof.TripleDes.X86_64
