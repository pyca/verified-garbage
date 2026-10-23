module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Common
public import VerifiedGarbage.Spec.TripleDes

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

def initialPermutation : Prog isa := .block (permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10)
def finalPermutation : Prog isa := .block (permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10)
def keyPermutation1 : Prog isa := .block (permuteCode Spec.TripleDes.pc1 64 .r9 .r8 .r10 .r11)
def keyPermutation2 : Prog isa := .block (permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11)

end VG.Impl.TripleDes.PPC64LE
