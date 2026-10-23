module

public import VerifiedGarbage.Impl.RsaOaep.X86_64

/-! # Seed hashing for DSA parameter generation

Reuse the verified streaming-hash sequence and its workspace layout. The
seed pointer and length occupy the hash sequence's label slots. Each seed
is 20 bytes for SHA-1 or 32 bytes for SHA-256, including the wrapped seeds
used when constructing p. The digest is written at oDig.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def hashTest : List Instr := [.mov .rax (.mem (sp sLabLen)), .alu .cmp .rax (.imm 20)]

def seedHash (sha1 sha256 : Stream) : Prog isa :=
  .seq (.block hashTest)
    (.ite .e (hashLabel sha1 oDig) (hashLabel sha256 oDig))

/-- The generator's reviewed width determines its hash before emission. -/
def seedHashAt (sha1 sha256 : Stream) (len : Nat) : Prog isa :=
  hashLabel (if len = 20 then sha1 else sha256) oDig

end VG.Impl.Dsa.X86_64.Generation
