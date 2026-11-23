module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
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

/-- The name of the function of a part of the verification: `vg_ecdsa_<curve>_verify_<part>`,
with `fnSuffix`, the curve named by `checkPoint`. -/
def shareName (c : Impl.Ecdsa.X86_64.Cfg) (part : String) : String :=
  match c.checkPoint with
  | some C => s!"vg_ecdsa_{C.curve}_verify_{part}" ++ c.fnSuffix
  | none => s!"vg_ecdsa_verify_{part}" ++ c.fnSuffix

/-- `b`, as a call of its function (`shareName`) for a curve whose verifications share
their parts (`verifyShared`), else inline. -/
def shareV (c : Impl.Ecdsa.X86_64.Cfg) (part : String) (b : Prog isa) : Prog isa :=
  if c.verifyShared then .call (shareName c part) b else b

/-- Verification by the public joint method, with `pts` for the code of `R = [u]G + [v]Q`;
the parts that do not depend on `pts` and call nothing by `shareV`. -/
def jointVerifyWith (c : Impl.Ecdsa.X86_64.Cfg) (pts : Prog isa) : Prog isa :=
  .seq (.block (args c)) <| .seq (shareV c "setup" (Impl.Ecdh.X86_64.Cfg.prefix' c (some D))) <|
  .seq (.block (loadS c)) <|
  .seq (shareV c "peer" (.block (Impl.Ecdh.X86_64.Cfg.peer c))) <| .seq (Impl.Ecdh.X86_64.Cfg.check c) <|
  .seq (shareV c "scalars" (scalars c)) <| .seq c.nPow <| .seq (shareV c "uv" (uv c)) <|
  .seq pts (shareV c "tail" (jointTail c))

def jointVerify (c : Impl.Ecdsa.X86_64.Cfg) (j : Joint.Cfg) (double : Prog isa) : Prog isa :=
  jointVerifyWith c (jointPoints c j double)

end Cfg
end VG.Impl.Ecdsa.Verify.X86_64
