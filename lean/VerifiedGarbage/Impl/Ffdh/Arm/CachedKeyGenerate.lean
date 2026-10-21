module

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate

/-! Cached attempts share scalar validation and key finishing with native generation. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

def entry : List Instr := GenerateKey.entry ++
  [.addSp .r12 0, .ldrSp .r3 156, .str .r3 .r12 52]

def body (prepare sample tail : Prog isa) : Prog isa :=
  .seq (.block (prepareArgs 24 ++ domainPointers))
    (SampleKeyGenerate.main prepare sample tail)

def code (prepare sample tail : Prog isa) : Prog isa :=
  framed (.seq (.block entry) (body prepare sample tail))

end VG.Impl.Ffdh.Arm.CachedKeyGenerate
