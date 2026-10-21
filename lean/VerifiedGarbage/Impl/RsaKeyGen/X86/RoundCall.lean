module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Call the shared prepared Miller–Rabin round and retain its result -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Impl.Mont.X86

def args : List Reg := [.edx, .edi]

def call (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push args) (.call name code) (.pop .ecx 2)

def code (name : String) (round : Prog isa) : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .esp 24))]) (call name round)

end VG.Impl.RsaKeyGen.X86.RoundCall
