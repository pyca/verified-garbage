module

public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Verified

/-!
# Triple DES's batched decryptions on x86-64, without secret residue

`vg_triple_des_cbc_decrypt_chained` and `vg_triple_des_cfb64_decrypt` over
each implementation of the ECB functions they call (`Batch.EcbImpl`),
followed by `Impl.Scrub.X86_64.scrub` with every granule of their stack
wiped (`X86_64.RScrub.withScrubAllM`): their 2128-byte frame, which they no
longer zero themselves, and the 1048 bytes of the ECB call below it. Their
postconditions read the memory on return only within the buffers
(`X86_64.Scrub.PostOut`): the data and the chaining block.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Batch.Scrub

open VG.X86_64 VG.X86_64.Scrub

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.TripleDes.cbcDecryptChainedContract X86_64.abi stack)
      (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcDecChainedPostOut_local _)

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.TripleDes.cfbDecryptContract X86_64.abi stack) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbDecPostOut_local _)

open VG.X86_64.RScrub

/-- `vg_triple_des_cbc_decrypt_chained` over `v`. -/
def cbcDecryptReg (v : EcbImpl) : Registration Spec.TripleDes.cbcDecryptChainedApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2128 .r8
      (Impl.TripleDes.X86_64.Batch.decrypt false (v.name .decrypt) (v.code .decrypt))
    stack := 3176
    verified := cbc_framed v
    spSafe := cbc_spSafe v } (cbcDecryptOut _)

/-- `vg_triple_des_cfb64_decrypt` over `v`. -/
def cfbDecryptReg (v : EcbImpl) : Registration Spec.TripleDes.cfbDecryptApi X86_64.target :=
  withScrubAllM {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2128 .r8
      (Impl.TripleDes.X86_64.Batch.decrypt true (v.name .encrypt) (v.code .encrypt))
    stack := 3176
    verified := cfb_framed v
    spSafe := cfb_spSafe v } (cfbDecryptOut _)

end VG.Proof.TripleDes.X86_64.Batch.Scrub
