module

public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
meta import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# Camellia's loop of pairs of rounds on x86-64, as a summary

ECB, in both directions, and CBC encryption and decryption reach the loop of
pairs of rounds (`pairBody`) with the same taint, with the scratch buffer
their second writable region: so their constant-time checks
(`taint_decide_sum`) all use one analysis of it, `pairSum`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- What is public at the loop of pairs of rounds of ECB and CBC: the
pointers (`rdx` at the tail buffer, `r9` at the scratch buffer, `rsi` at the
round keys, `rdi` at the group's end), the blocks left, the stack pointer,
the flags, and the group's end, the data pointer and the blocks left in
their slots. -/
def pairTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdx, .rsp, .rsi, .rdi, .r8, .r9], flags := true, lens := [0, 8 * slots],
    bases := [(.r9, 1, 0), (.rdx, 1, 8 * tailSlot)],
    slots := [(1, 8 * endSlot, 8), (1, 8 * countSlot, 8), (1, 8 * dataSlot, 8)] }

taint_summary pairSum : taintS pairTaint (.block pairBody)

end VG.Proof.Camellia.X86_64
