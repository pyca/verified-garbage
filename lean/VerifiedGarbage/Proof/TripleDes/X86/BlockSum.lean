module

public import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# The constant-time analysis of Triple DES's x86 encryption block function, once

OFB, CFB64 and CFB8 call `vg_triple_des_encrypt_block` at the same taint
(`τCall`): the arguments' words, their frame, and the bases of the scratch
buffer (at `edi` and `eax`), with its word at 920 public. The analysis of the
call is a summary (`taint_summary`), which their checks use
(`taint_decide_sum`) in place of the analysis of the block function at each
call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86

open VG VG.X86

/-- What OFB, CFB64 and CFB8 have public at their calls of the block function,
inside their frame (region 0, the 12 bytes they push, all public, with the
scratch buffer's base at 8). -/
def τCall : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .ecx, .edx, .esp, .ebp, .esi, .edi], flags := true, lens := [12, 0, 8, 8 * 118],
    bases := [(.edi, 3, 0), (.eax, 3, 0), (.esp, 0, 0)], slots := ⟨[0xFFF, 0, 0, 0xFF <<< 920]⟩,
    wbases := [(0, 8, 3)], argLen := 24, argBases := [(12, 1), (8, 2), (20, 3)], stk := [some 12],
    room := 16 }

taint_summary encSum : taint τCall (.call "vg_triple_des_encrypt_block" Impl.TripleDes.X86.encryptBlock)

end VG.Proof.TripleDes.X86
