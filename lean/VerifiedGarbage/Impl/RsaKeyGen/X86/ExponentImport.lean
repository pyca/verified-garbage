module

public import VerifiedGarbage.Impl.Bignum.X86.LoadBE

/-! # Load the public exponent's one-to-eight big-endian octets into the native header -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentImport
open VG VG.X86 VG.Impl.Mont.X86

def args : List Instr := [.mov .esi (.mem (sc 12)), .mov .ecx (.mem (sc 16))]

def code : Prog isa :=
  .seq (.block args)
    (VG.Impl.Bignum.X86.loadBE 1 128)

end VG.Impl.RsaKeyGen.X86.ExponentImport
