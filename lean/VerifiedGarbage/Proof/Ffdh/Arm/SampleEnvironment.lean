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

def SampleEnvironment.empty : SampleEnvironment where
  holds := fun _ _ => True
  publicRel := fun _ _ => True
  stable := fun _ _ _ _ => trivial
  public_stable := fun _ _ _ => trivial

theorem SampleEnvironment.after {e : SampleEnvironment} {p : Inputs} {s t : State}
    {code : Prog isa} {trace : List Leak} (h : e.holds p s)
    (frame : Frame (keyCallWrites p s) s.mem t.mem)
    (rest : Rest roundClobbers s t) (run : Exec isa code s trace t) : e.holds p t :=
  e.stable h frame rest (Exec.syms run)

end VG.Proof.Ffdh.Arm
