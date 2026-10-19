module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch


/-!
# Streaming TDEA-CMAC's `finish` with a larger working space

`finishScratchContract`, with 688 bytes of working space (`absorb`'s) in
place of 640: on x86, `finish` keeps our caller's registers in it after the
working space of the code of `finalize` it runs, as `absorb` does. The
locality of the pre- and postconditions is `finishPost_local`'s, which does
not depend on the working space.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream

open VG.Spec.Cmac

/-- `vg_cmac_triple_des_finish` with `scratch: *mut [u64; 86]`. -/
def finishScratchSig86 : Sig where
  params := [("state", .array true .u64 52), ("count", .int .u64 true),
    ("out", .array true .u8 8), ("scratch", .array true .u64 86)]

/-- `tdesFinishContract`, whatever `scratch` is. -/
def finishScratchContract86 {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSig86.contract A
    (post := fun state count out _scratch => tdesFinishPost A.ptrBits state count out)
    (stack := stack)

end VG.Proof.CmacTripleDes.Stream
