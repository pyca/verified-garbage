module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape

/-! Construct p and its generator exponent entirely in the native workspace. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def pConstruct (G : Hash) (pLen qLen : Nat) : Prog isa :=
  let count := (8 * pLen - 1) / (8 * qLen)
  .seq (.seq (pHashes G qLen count) (pShape qLen count pLen))
    (seqs [.block workspaceBase, workspace (pLen / 8), candidateFromFrame pLen qLen])

end VG.Impl.Dsa.AArch64.Generation
