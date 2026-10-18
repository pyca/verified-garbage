module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape

/-! Hash a seed and construct the subgroup candidate in its preserved byte buffer. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def qArgs : List Instr :=
  [.ldrSp .x2 0, .ldrSp .x12 sScr, .addImm .x .x12 .x12 oDig, .ldrSp .x9 sLabLen]

def qCandidate (sha1 sha256 : Hash) : Prog isa :=
  .seq (seedHash sha1 sha256) (.seq (.block qArgs) qShape)

end VG.Impl.Dsa.AArch64.Generation
