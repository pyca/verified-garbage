module
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Top

import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Top
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
import VerifiedGarbage.Proof.X25519.AArch64.Verified
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
meta import VerifiedGarbage.Proof.X25519.AArch64.Word.Top
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Top
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
meta import VerifiedGarbage.Proof.X25519.AArch64.Verified
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! The `_alt` ladder: correctness, constant time, and the shared contract. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64
open VG.Proof.X25519.AArch64.Word (localContract)

theorem x25519_ct : ConstantTime isa localContract.pre localContract.pub
    Impl.X25519.AArch64.AltLadder.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => VG.Proof.X25519.AArch64.agree₀ hp) (by taint_decide)

theorem x25519_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target Impl.X25519.AArch64.AltLadder.x25519
      (Spec.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct x25519_ok x25519_ct (by
    sig_implies [Spec.X25519.x25519Contract,Spec.X25519.x25519Sig,AArch64.abi,AArch64.argRegs,
      localContract,Proof.X25519.x25519AArch64] [VG.Proof.X25519.AArch64.sat]
      using VG.Proof.X25519.AArch64.sat)

end VG.Proof.X25519.AArch64.AltLadder
