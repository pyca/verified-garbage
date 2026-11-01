module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Sm4.X86.Lit
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Impl.Sm4.X86.Prepared
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit

/-!
# The constant-time analysis of the x86 modes' calls of SM4, once

Every mode calls `vg_sm4_prepare_keys` at the same taint (`τPrep`): inside
the frame of its four arguments (region 0, all public, with the scratch
buffer's base at 8), the IV's base in `esi` and the scratch buffer's in
`edi`. It calls `vg_sm4_crypt_prepared` at another (`τCrypt`, inside the
frame of its two arguments, with the scratch buffer's base at 0 and the
modes' data pointer and steps left public at 1448), and the flags secret, as
CBC encryption leaves them (the others, which have them public, use it too).
The analyses of the calls are
summaries (`taint_summary`), which the modes' checks use
(`taint_decide_sum`) in place of the analysis of the functions in each.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86

/-- What the modes have public at their call of `vg_sm4_prepare_keys`. -/
def τPrep : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .ecx, .edx, .esp, .esi, .edi], flags := false, lens := [16, 0, 16, 8 * 184],
    bases := [(.edi, 3, 0), (.esi, 2, 0), (.esp, 0, 0)], slots := ⟨[0xFFFF]⟩, wbases := [(0, 8, 3)],
    argLen := 24, argBases := [(12, 1), (8, 2), (20, 3)], stk := [some 16], room := 20 }

taint_summary prepSum : taint τPrep (.call "vg_sm4_prepare_keys" Impl.Sm4.X86.prepareKeys)

/-- What the modes have public at their calls of `vg_sm4_crypt_prepared`. -/
def τCrypt : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp, .esi, .edi], flags := false, lens := [8, 0, 16, 8 * 184],
    bases := [(.edi, 3, 0), (.esp, 0, 0)], slots := ⟨[0xFF, 0, 0, 0xFF <<< 1448]⟩, wbases := [(0, 0, 3)],
    argLen := 24, argBases := [(12, 1), (8, 2), (20, 3)], stk := [some 8], room := 20 }

taint_summary cryptSum : taint τCrypt (.call "vg_sm4_crypt_prepared" Impl.Sm4.X86.cryptPrepared)

end VG.Proof.Sm4.X86
