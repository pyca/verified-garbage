module

public import VerifiedGarbage.Impl.TripleDes.X86.Common
public import VerifiedGarbage.Spec.TripleDes

@[expose] public section

namespace VG.Impl.TripleDes.X86
open VG.X86

def keyPermutation1 : Prog isa :=
  .block (permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx)
def keyPermutation2 : Prog isa :=
  .block (permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx)
end VG.Impl.TripleDes.X86
