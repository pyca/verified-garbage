module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape

/-! # Hash and shape a DSA subgroup candidate -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-- Frame slot zero holds the destination for the shaped candidate. -/
def qArgs : List Instr :=
  [.mov .rdi (.mem (sp 0)), .mov .rsi (.mem (sp sScr)), .alu .add .rsi (.imm oDig),
   .mov .rcx (.mem (sp sLabLen)), .mov .rdx (.reg .rcx), .shift .shl .rdx 3]

def qCandidate (sha1 sha256 : Stream) (len : Nat) : Prog isa :=
  .seq (seedHashAt sha1 sha256 len)
    (.seq (.block qArgs) Ffdh.X86_64.ParameterCandidate.shape)

end VG.Impl.Dsa.X86_64.Generation
