module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # Native final validity masks for RSA key assembly -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

/-- `e < 2^33` iff the high native word is below two. -/
def exponentUpper : List Instr :=
  [.mov .eax (.mem (sc kEvHi)), .alu .cmp .eax (.imm 2),
    .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm 1), .store (sc kFlag) .eax]

end VG.Impl.RsaKeyGen.X86.Key
