module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import Init.Core
public import VerifiedGarbage.TCB.Arm.Isa

/-! Read-only public environment supplied to a scalar-sampling policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure SampleEnvironment where
  holds : Inputs → State → Prop
  publicRel : State → State → Prop
  stable : ∀ {p : Inputs} {s t : State}, holds p s →
    Frame (keyCallWrites p s) s.mem t.mem → Rest roundClobbers s t →
    t.syms = s.syms → holds p t
  public_stable : ∀ {s t u v : State}, publicRel s t →
    u.syms = s.syms → v.syms = t.syms → publicRel u v

end VG.Proof.Ffdh.Arm
