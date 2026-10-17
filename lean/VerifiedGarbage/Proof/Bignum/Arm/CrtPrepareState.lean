module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # State carried from CRT workspace initialization to modulus import -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtPrepareInput (base np : BitVec 32) (size w k : Nat) (nb : List Byte) (s : State) : Prop where
  workspace : Workspace s base size
  context : CrtSetupContext base (workspaceWords w) w s
  storageFits : totalBytes w ≤ size
  source : SavedOperand base np (workspaceWords w) k 8 12 nb s
  stackSeparate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, size⟩
  sourceSeparate : Region.Disjoint ⟨State.addr np, k⟩ ⟨State.addr base, size⟩
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackWrite : InRegions s.wr (off (State.addr s.sp) 8) 4
  saved : s.mem.readW (State.addr s.sp) 32 = base
  ptr : s.gpr .r0 = base
  count : s.gpr .r6 = BitVec.ofNat 32 k
  lengthValid : Spec.Rsa.lenValid k
  width : Spec.Rsa.modulusWords k = w

structure CrtInitialized (base np : BitVec 32) (size w k : Nat) (nb : List Byte) (s : State) : Prop where
  workspace : Workspace s base size
  context : CrtSetupContext base (workspaceWords w) w s
  ready : LayoutFrameReady base (workspaceWords w) w s
  main : CrtMainState base (workspaceWords w) w s.mem
  p : CrtPrimeState (crtP base w) base (workspaceWords w) w s.mem
  q : CrtPrimeState (crtQ base w) base (workspaceWords w) w s.mem
  source : SavedOperand base np (workspaceWords w) k 8 12 nb s
  stackWrite : InRegions s.wr (off (State.addr s.sp) 8) 4
  stackSeparate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, size⟩
  storageFits : totalBytes w ≤ size
  positive : 0 < k
  inputFits : k ≤ 8 * w

end VG.Proof.Bignum.Arm
