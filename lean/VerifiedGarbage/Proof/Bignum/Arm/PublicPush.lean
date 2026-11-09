module

public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Geometry and input preservation across the public RSA stack push -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem public_push_argAddr {s : State} (fit : 56 ≤ s.sp.toNat) :
    off (State.addr (pcPushed s).sp) 56 = State.addr s.sp := by
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' fit
  change State.addr (pcPushed s).sp + BitVec.ofNat 64 56 = State.addr s.sp
  rw [← addr_add (a := (pcPushed s).sp) (k := 56) (by rw [spNat]; have := s.sp.isLt; omega)]
  change State.addr (s.sp - BitVec.ofNat 32 56 + BitVec.ofNat 32 56) = _
  rw [BitVec.sub_add_cancel]

theorem public_push_argOffset {s : State} (fit : 56 ≤ s.sp.toNat) (d : Nat) :
    off (State.addr (pcPushed s).sp) (56 + d) = off (State.addr s.sp) d := by
  change State.addr (pcPushed s).sp + BitVec.ofNat 64 (56 + d) = _
  rw [← Offset.add_add]
  rw [show State.addr (pcPushed s).sp + BitVec.ofNat 64 56 = State.addr s.sp from public_push_argAddr fit]

end VG.Proof.Bignum.Arm
