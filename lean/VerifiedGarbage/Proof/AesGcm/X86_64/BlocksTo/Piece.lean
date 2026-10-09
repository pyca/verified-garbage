import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM on whole blocks out of place, x86-64: what the interleaved loops need

Untrusted: everything here is checked by Lean. What `BlocksTo.stitchPart`
needs of the out-of-place loops it runs (`PieceTo`, as `Piece` for
`Blocks.stitchPart`), and the loops with their proof for a key context of
kind `M` (`StitchToCode`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

/-- What `BlocksTo.stitchPart` needs of the loops `code` it runs, besides
their contract: no write of `mxcsr` or `rsp`, no calls, and constant time,
from the registers it keeps public (the output in `r10`; with `full`, for
loops that take all the blocks). -/
structure PieceTo (code : Prog isa) (aligned : Bool := false) (full : Bool := false) : Prop where
  mxcsr : code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : code.all (fun i => !X86_64.isa.writesSp i) = true
  nosp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  depth : code.depth = 0
  /-- It uses no stack. -/
  xdepth : code.x86_64Depth = 0
  ct : ∃ hc, ((taint.check (Taint.ofRegs [.r10, .r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (BlocksTo.stitchPart code aligned full) hc).map fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs &&
      (!false || τ'.flags)) = some true

open Gcm.X86_64.Stitch (CtxMode StitchToOkM) in
/-- Out-of-place interleaved loops for a key context of kind `M`, with their
proof; with `full`, they take any number of blocks from 16 on. -/
structure StitchToCode (M : CtxMode) (aligned : Bool := false) where
  enc : Prog isa
  full : Bool
  ok : StitchToOkM M enc (if full then 1 else 16)
  P : PieceTo enc aligned full

/-- Whether the loop of `st`, if any, takes all the blocks. -/
def encFullTo {M : Gcm.X86_64.Stitch.CtxMode} {aligned : Bool} (st : Option (StitchToCode M aligned)) : Bool :=
  st.any (·.full)

end VG.Proof.AesGcm.X86_64
