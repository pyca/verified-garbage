import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA with a scratch buffer of 32-bit words as an argument

As `Scratch.lean`, for the 32-bit targets, whose functions save more
registers: `vg_idea_invert_key` and `vg_idea_ecb` keep the registers they
save in a frame of their own, around code proved with that buffer of `n`
32-bit words as an argument, whatever it holds.
-/

namespace VG.Proof.Idea

open VG.Spec.Idea

/-- `vg_idea_invert_key` with `scratch: *mut [u32; n]`. -/
def invertKeyScratchSig32 (n : Nat) : Sig where
  params := [("schedule", .array false .u8 104), ("inverse", .array true .u8 104),
    ("scratch", .array true .u32 n)]

/-- `invertKeyContract`, whatever `scratch` is. -/
def invertKeyScratchContract32 {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (invertKeyScratchSig32 n).contract A
    (post := fun schedule inverse _scratch => invertKeyPost A.ptrBits schedule inverse) (stack := stack)

/-- `vg_idea_ecb` with `scratch: *mut [u32; n]`. -/
def ecbScratchSig32 (n : Nat) : Sig where
  params := [("schedule", .array false .u8 104), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u32 n)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbScratchContract32 {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ecbScratchSig32 n).contract A
    (post := fun schedule data len _scratch => ecbPost A.ptrBits schedule data len) (stack := stack)

end VG.Proof.Idea
