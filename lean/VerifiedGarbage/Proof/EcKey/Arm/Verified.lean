module

public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.EcKey.Arm.Contract
import VerifiedGarbage.Proof.EcKey.Arm.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
public import VerifiedGarbage.Impl.EcKey.P256.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.EcKey.Arm.Main
meta import VerifiedGarbage.Proof.EcKey.Arm.Contract
meta import VerifiedGarbage.Proof.EcKey.Arm.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
meta import VerifiedGarbage.Impl.EcKey.P256.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# P-256 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for P-256 (`p256_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm Spec.Weierstrass

theorem post_of {u : Bool} {s s' : State} (h : PkPost (p256With u) s s') : pkArm.post s s' := by
  unfold PkPost at h
  show match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = List.replicate 65 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey (p256With u).C (dk (p256With u) s) = pk s.mem (State.addr (s.gpr .r1)) from rfl,
    hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

end VG.Proof.EcKey.Arm
