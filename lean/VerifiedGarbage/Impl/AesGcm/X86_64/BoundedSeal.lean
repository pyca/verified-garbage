module
public import VerifiedGarbage.Impl.AesGcm.X86_64.Short

/-! Register setup for entering the shared bounded VAES seal. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86_64.Short
open VG.X86_64

def sameArgs : List Instr := [.mov .rbx (.mem (at_ .r15 dataO)), .mov .r10 (.mem (at_ .r15 lenO)), .mov .r11 (.reg .rbx)]

def boundedSame : Prog isa := .seq (.block sameArgs) (.call bounded.name bounded.code)

end VG.Impl.AesGcm.X86_64.Short
