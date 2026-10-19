module
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Top

import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Top
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Top
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Lit
import VerifiedGarbage.Proof.X25519.AArch64.Verified
meta import VerifiedGarbage.Proof.X25519.AArch64.Verified
import VerifiedGarbage.Proof.Ed25519.AArch64.FieldBound
import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord
import VerifiedGarbage.Proof.Ed25519.AArch64.Sub
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Field64
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Add
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Cmadd
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mux
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sqr
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sub
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ends
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Invert
import VerifiedGarbage.Proof.X25519.AArch64.Main
import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Word.Output
import VerifiedGarbage.Proof.X25519.AArch64.Word.Step
meta import VerifiedGarbage.Proof.Ed25519.AArch64.FieldBound
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Sub
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Field64
meta import VerifiedGarbage.Proof.Ed25519.Scalar
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.Csub
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Add
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Cmadd
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mux
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sqr
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sub
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ends
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Ladder
meta import VerifiedGarbage.Proof.X25519.AArch64.Invert
meta import VerifiedGarbage.Proof.X25519.AArch64.Main
meta import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
meta import VerifiedGarbage.Proof.X25519.AArch64.Word.Output
meta import VerifiedGarbage.Proof.X25519.AArch64.Word.Step

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
