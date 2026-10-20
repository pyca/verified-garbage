module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Impl.Sm4.X86.Ecb
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Impl.Sm4.X86.Ecb
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The constant-time analysis of SM4's x86 core in ECB, once

ECB's code contains the bitsliced core `crypt8` (the transposes and the
rounds), which encryption and decryption reach at the same taint
(`τCryptEcb`): the stack and the scratch buffer's base public, with the
buffer's word at 1424. The analysis of the core is a summary
(`taint_summary`), which ECB's checks use (`taint_decide_sum`, by the code,
`CodeEq`) in place of the analysis of the core in each. The modes call
`vg_sm4_crypt_prepared` instead.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86

/-- What ECB encryption and decryption have public where they run the core. -/
def τCryptEcb : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .ebp, .esi, .edi], flags := true, lens := [0, 8 * 179],
    bases := [(.edi, 1, 0)], slots := ⟨[0, 0xFF <<< 1424]⟩, argLen := 20, argBases := [(8, 0), (16, 1)] }

taint_summary cryptSumEcb : taint τCryptEcb Impl.Sm4.X86.crypt8

end VG.Proof.Sm4.X86
