module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Impl.Sm4.X86.Prepared
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The constant-time analysis of ECB's calls of SM4's x86 core, once

ECB encryption and decryption call `vg_sm4_crypt_prepared` at the same taint
(`τCryptEcb`): inside the frame of its two arguments (region 0, all public,
with the scratch buffer's base at 0), the stack and the scratch buffer's
base public, with the data pointer and the blocks left public at 1448. The
analysis of the call is a summary (`taint_summary`), which ECB's checks use
(`taint_decide_sum`) in place of the analysis of the function in each. The
modes call it at their own taint (`CallSum.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86

/-- What ECB encryption and decryption have public at their calls of
`vg_sm4_crypt_prepared`. -/
def τCryptEcb : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp, .esi, .edi], flags := false, lens := [8, 0, 8 * 184],
    bases := [(.edi, 2, 0), (.esp, 0, 0)], slots := ⟨[0xFF, 0, 0xFF <<< 1448]⟩, wbases := [(0, 0, 2)],
    argLen := 20, argBases := [(8, 1), (16, 2)], stk := [some 8], room := 20 }

taint_summary cryptSumEcb : taint τCryptEcb (.call "vg_sm4_crypt_prepared" Impl.Sm4.X86.cryptPrepared)

end VG.Proof.Sm4.X86
