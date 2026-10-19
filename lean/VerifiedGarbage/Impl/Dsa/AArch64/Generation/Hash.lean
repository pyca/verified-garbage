module

public import VerifiedGarbage.Impl.RsaOaep.AArch64

/-! # Hash a DSA seed with the shared streaming hash implementation

Use OAEP's label pointer, length and hash workspace slots. The 20-byte
seed selects SHA-1; the 32-byte seed selects SHA-256. The digest is left
at the existing hash workspace's oDig offset.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def hashTest : List Instr := [.ldrSp .x0 sLabLen, .subImm .x .x0 .x0 20]

def seedHash (sha1 sha256 : Hash) : Prog isa :=
  .seq (.block hashTest)
    (.ite (.zero .x .x0) (hashLabel sha1 oDig) (hashLabel sha256 oDig))

end VG.Impl.Dsa.AArch64.Generation
