module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tail

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous.Standalone
open VG.AArch64

def hashBlocks (c : Callees) : Prog isa := .ite (.zero .x .x3) (.block []) (ghCall c)
/-- The caller's powers pointer remains on the original stack, above this private frame. -/
def encryptUsing (c : Callees) (pwOffset : Nat) (pmull forward : Bool) : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 dataO,.ldr .x .x24 .x19 lenO,.ldr .x .x26 .x19 DirectGather.descO,
    .str .x .x26 .x19 DirectGather.hashO,imm .x25 0]) <|
  .seq (if pmull then DirectGather.batches c forward (Stitch.pwTbl pwOffset) else .block []) <|
  .ite (.zero .x .x24) (.block []) (Contiguous.Tail.aligned c)
abbrev encryptWith (v : Calls) := encryptUsing v.callees (v.pwWn+48) v.pmull
abbrev encrypt (v : Calls) := encryptWith v (!v.stitch)

/-- Absorb full blocks and pad the remaining input directly in the GHASH scratch block. -/
def padded (c : Callees) : Prog isa :=
  .seq (.block (absSeg2 16)) <| .seq (hashBlocks c) <|
  .ite (.zero .x .x24) (.block []) <|
    .seq (.block [mov .x25 .x24]) <| .seq (padSeg 16 [mov .x12 .x23]) (ghCall c)
/-- The final counter encrypts the hash accumulator directly into the caller's tag. -/
def tagArgs : List Instr := [mov .x0 .x21,mov .x1 .x22,mov .x2 .x20,ptr .x3 .x20 16,
    imm .x4 1,ptr .x5 .x19 scrO,.ldr .x .x6 .x19 tlO]

def tagDirect (c : Callees) : Prog isa :=
  .seq (lens c 16 .x26 .x27) (.seq (.block tagArgs) (ctrCallG c true))

def entry : List Instr :=
  oneEntry 16 ++ [.str .x .x7 .x19 DirectGather.descO,.ldrSp .x9 0,.str .x .x9 .x19 lenO] ++ stashArg 8

/-- Reload the final GHASH value and message length for the interleaved tag computation. -/
def tagPrep : List Instr := [ptr .x0 .x21 240] ++ Fast.key ++
  Gcm.AArch64.Pmull.loadRev Gcm.AArch64.Pmull.Y .x20 16 ++ [.ldr .x .x26 .x19 lenO]

def hwReturn : Prog isa :=
  .seq (.block tagPrep) (.seq (Gcm.AArch64.Stitch.byRounds Contiguous.Tag.finish) (.block restore))

def softReturn (c : Callees) : Prog isa :=
  .seq (.block finPrep) (.seq (tagDirect c) (.block restore))

def bodyUsing (c : Callees) (pwOffset : Nat) (pmull forward : Bool) : Prog isa :=
  .seq (.block entry) <|
  .seq (j0 c) <|
  .seq (.block [.ldr .x .x23 .x19 aadO,.ldr .x .x24 .x19 alenO]) <|
  .seq (padded c) <| .seq (encryptUsing c pwOffset pmull forward) <|
  .seq (.block [.ldr .x .x23 .x19 DirectGather.hashO,.sub .x .x24 .x26 .x23]) <|
  .seq (padded c) <| if pmull then hwReturn else softReturn c
abbrev bodyWith (v : Calls) := bodyUsing v.callees (v.pwWn+48) v.pmull
abbrev body (v : Calls) := bodyWith v (!v.stitch)

def clear (v : Calls) : Impl.Scrub.AArch64.Clear := if v.pmull && !v.stitch then .all else Fn.own

def prog (v : Calls) : Prog isa := Impl.Scrub.AArch64.scrubAll (v.pwWn+32) 0 (clear v)
  (Impl.StackScratch.AArch64.withStackArgScratch (v.pwWn+32) 2 (body v))

end VG.Impl.AesGcm.AArch64.Contiguous.Standalone
