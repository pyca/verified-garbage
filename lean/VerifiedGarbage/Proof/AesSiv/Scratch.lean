import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV's key setup with its working space as an argument

`vg_aes_siv_init` keeps its working space in a frame of its own
(`Verified.stackScratch`), around code proved with the working space as an
argument: `initScratchContract` is the shared contract with a 2560-byte
`scratch` buffer appended, whatever it holds.
-/

namespace VG.Proof.AesSiv

open VG.Spec.Siv

/-- `vg_aes_siv_init` with `scratch: *mut [u64; 320]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 320)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

end VG.Proof.AesSiv
