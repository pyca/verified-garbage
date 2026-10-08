import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA ECB with its working space as an argument

`vg_idea_ecb` keeps its working space in a frame of its own
(`Verified.stackScratch`), around code proved with the working space as an
argument: `ecbScratchContract` is the shared contract with the `scratch`
buffer appended, whatever it holds.
-/

namespace VG.Proof.Idea

open VG.Spec.Idea

/-- `vg_idea_ecb` with `scratch: *mut [u64; 2]`. -/
def ecbScratchSig : Sig where
  params := [("schedule", .array false .u8 104), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u64 2)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbScratchSig.contract A
    (post := fun schedule data n _scratch => ecbPost A.ptrBits schedule data n) (stack := stack)

end VG.Proof.Idea
