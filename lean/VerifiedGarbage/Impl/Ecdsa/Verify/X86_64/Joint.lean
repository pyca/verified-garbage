module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64

/-! Public joint verification, with a Jacobian accumulator and an inversion-free final check.
The curve supplies the loop's doubler of the accumulator (`double`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64

namespace Cfg

def jointPoints (c : Impl.Ecdsa.X86_64.Cfg) (j : Joint.Cfg) (double : Prog isa) : Prog isa :=
  .seq (Joint.prep j (c.sl U) (c.sl V)) (Joint.window j double)

def jointTail (c : Impl.Ecdsa.X86_64.Cfg) : Prog isa :=
  .seq (ForwardField.programB c.MP' [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)]) (tail c)

def jointVerify (c : Impl.Ecdsa.X86_64.Cfg) (j : Joint.Cfg) (double : Prog isa) : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.validate c) <|
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (jointPoints c j double) (jointTail c)

end Cfg
end VG.Impl.Ecdsa.Verify.X86_64
