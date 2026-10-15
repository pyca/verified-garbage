module

public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The prepared loops given the block index: what the variants check

Untrusted: everything here is checked by Lean. The facts a variant states of
its loops given the block index (`PieceRI`), checked where it is registered:
what `Piece` states of loops but their constant time (`PieceS`), and the
taint checks of the code around the load of the index (`DecRIChecks`,
`EncRIChecks`, from which `Iv96Piece.lean` proves them constant time).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)

/-- What `Piece` states of loops but their constant time: no write of
`mxcsr` or `rsp`, no calls, no stack. -/
structure PieceS (code : Prog isa) : Prop where
  mxcsr : code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : code.all (fun i => !X86_64.isa.writesSp i) = true
  nosp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  depth : code.depth = 0
  xdepth : code.x86_64Depth = 0

/-- The registers public where the prepared loops start: `scratch`'s
working space and the arguments. -/
abbrev regsI : List Reg := [.r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

/-- The taint checks of `StitchZH.decR true` around the load of the block
index: the setup from the arguments (`rs` public after it), the constants,
and the rest from `rs` and the index. -/
structure DecRIChecks (rs : List Reg) : Prop where
  rsp : .rsp ∈ rs
  head : ∃ hc, ((taint.check (Taint.ofRegs regsI) Impl.Gcm.X86_64.StitchZH.decRHead hc).map fun τ' =>
    (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  consts : ∃ hc, ((taint.check (Taint.ofRegs rs) (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7)) hc).map
    fun τ' => (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  load : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .r10 (.mem (at_ .rsp 16))]) hc).isSome = true
  rest : ∃ hc, (taint.check (Taint.ofRegs (.r10 :: rs)) Impl.Gcm.X86_64.StitchZH.decRBeRest hc).isSome = true

/-- The taint checks of `StitchZHTo.encR true` around the load of the block
index, as `DecRIChecks`. -/
structure EncRIChecks (rs : List Reg) : Prop where
  rsp : .rsp ∈ rs
  head : ∃ hc, ((taint.check (Taint.ofRegs (.r10 :: regsI)) Impl.Gcm.X86_64.StitchZHTo.encRHead hc).map fun τ' =>
    (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  consts : ∃ hc, ((taint.check (Taint.ofRegs rs) (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7)) hc).map
    fun τ' => (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  load : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .r10 (.mem (at_ .rsp 32))]) hc).isSome = true
  rest : ∃ hc, (taint.check (Taint.ofRegs (.r10 :: rs)) Impl.Gcm.X86_64.StitchZHTo.encRBeRest hc).isSome = true

/-- The facts of the prepared loops given the block index on 512-bit
registers (`StitchZH.decR true`, `StitchZHTo.encR true`), checked where a
variant is registered. -/
structure PieceRI : Type where
  dec : PieceS (Impl.Gcm.X86_64.StitchZH.decR true)
  decChecks : ∃ rs, DecRIChecks rs
  enc : PieceS (Impl.Gcm.X86_64.StitchZHTo.encR true)
  encChecks : ∃ rs, EncRIChecks rs

end VG.Proof.AesGcm.X86_64
