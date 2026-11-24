module

public import VerifiedGarbage.Impl.Gcm.AArch64.Forward
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Bounded

/-! The public-length specializations for a 12-byte nonce and at most one
block of AAD. The two-pointer counter and stitched loops admit either layout. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous

open VG.AArch64
open Fast (front hReload padMulT lensTag)
open VG.Impl.Gcm.AArch64.Pmull (loadRev Y)

/-- The incoming stack words are length, tag and powers; the frame adds the
working area as the fourth. The destination is retained across the front. -/
def preparedArgs : List Instr :=
  [mov .x11 .x7, .ldrSp .x7 0] ++ oneEntry 24 ++
  [.str .x .x11 .x19 dstO] ++ stashArg 8

/-- Authenticate complete eight-block groups in the prepared table. x15 reads
plaintext, x23 receives ciphertext. Reload the original source for the tail. -/
def batchCall (forward : Bool) : Prog isa :=
  if forward then VG.Impl.Gcm.AArch64.Stitch.forwardCall else VG.Impl.Gcm.AArch64.Stitch.sealCall

def batches (forward : Bool) : Prog isa :=
  Stitch.stitched [] (Stitch.pwTbl 16) <|
    .seq (.block [mov .x15 .x23,.ldr .x .x23 .x19 dstO]) <|
    .seq (batchCall forward) (.block [.ldr .x .x23 .x19 dataO])

/-- Prepare the two pointers, length and zero keystream cursor of the remainder.
x27 retains the first ciphertext byte still to be hashed. -/
def remainder (fused : Bool) : List Instr :=
  [.ldr .x .x27 .x19 dstO] ++
  (if fused then Stitch.whole ++ [.add .x .x23 .x23 .x9,.add .x .x27 .x27 .x9,.sub .x .x24 .x26 .x9]
   else [mov .x24 .x26]) ++
  [mov .x26 .x27,imm .x25 0]

/-- Hash precisely the remainder encrypted by the two-pointer CTR loop. -/
def authArgs (fused : Bool) : List Instr :=
  [.ldr .x .x26 .x19 lenO,mov .x23 .x27] ++
  (if fused then Stitch.whole ++ [.sub .x .x24 .x26 .x9] else [mov .x24 .x26])

abbrev authRemainder (fused : Bool) := authArgs fused ++ absSeg2 16

/-- Prepared hardware record with the common CTR loop for all tails. -/
def preparedBody (c : Callees) (gh : Fn) (fused forward : Bool) : Prog isa :=
  .seq (.block preparedArgs) <| .seq front <|
  .seq (if fused then batches forward else .block []) <|
  .seq (.block (remainder fused)) <| .seq (DirectGather.aligned c) <|
  .seq (.block (authRemainder fused)) <| .seq (Fast.pwSel c 16 gh) <|
  .seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24,mov .x12 .x23])) <|
  .seq padMulT <| .seq (.block lensTag) <| .seq (ctrCall c) <|
  .seq (.block tagOut) (.block restore)

def preparedFrame (v : Calls) (gh : Fn) (fused : Bool) : Prog isa :=
  Impl.StackScratch.AArch64.withStackArgScratch (v.pwWn+32) 3 (preparedBody v.callees gh fused (!v.stitch))



/-- Clear borrowed vector high halves on the forwarded path. -/
def preparedClear (fused forward : Bool) : Impl.Scrub.AArch64.Clear :=
  if fused && forward then .all else Fn.own

/-- The whole entry branches only on the CPU specialization and public record sizes. -/
def select (v : Calls) (gh : Fn) : Prog isa :=
  let clear := fun n p => Impl.Scrub.AArch64.scrubAll n 0 Fn.own p
  let fallback := clear (v.pwWn+80) (generalFrame v)
  let hardware := fun fused => Impl.Scrub.AArch64.scrubAll (v.pwWn+32) 0
    (preparedClear fused (!v.stitch)) (preparedFrame v gh fused)
  let threshold := if v.stitch then 768 else 4096
  let large := .seq (.block [imm .x9 threshold,.subs .x .x11 .x10 .x9,.sbc .x .x11 .x11 .x11])
    (.ite (.nonzero .x .x11) (hardware false) (hardware true))
  if !v.pmull then fallback else
    .seq (.block standardGuard) <| .ite (.zero .x .x10)
      (.seq (.block [.ldrSp .x10 0,imm .x9 97,.subs .x .x11 .x10 .x9,.sbc .x .x11 .x11 .x11])
        (.ite (.nonzero .x .x11) (clear DirectGather.shortWork shortFrame) large)) fallback

end VG.Impl.AesGcm.AArch64.Contiguous
