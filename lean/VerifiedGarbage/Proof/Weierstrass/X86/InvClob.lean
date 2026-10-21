module
import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.TCB.X86.State
/-! # Registers used by the word divstep kernel -/
@[expose] public section
namespace VG.Proof.Weierstrass.X86.Inv
open VG.X86
def wordClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
end VG.Proof.Weierstrass.X86.Inv
