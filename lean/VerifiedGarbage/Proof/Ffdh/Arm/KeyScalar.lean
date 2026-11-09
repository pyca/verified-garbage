module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.TCB.Arm.Isa

/-! The complete native scalar sampler preserves arithmetic storage and the
saved workspace pointer while deriving the shared scalar encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def keyScalarWrites (p : Inputs) (s : State) : List Region :=
  [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩,
    ⟨off (State.addr s.sp) 16, 4⟩, ⟨State.addr p.privateValue, p.k⟩]

end VG.Proof.Ffdh.Arm
