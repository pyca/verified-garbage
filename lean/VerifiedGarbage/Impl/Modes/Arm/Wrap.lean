module

public import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# A block cipher's ECB function as a call of its core, on ARMv7

`c.wrap`: a call of the core `c` (`Seq.lean`), the ECB function the modes
call, with the arguments as they are, in a frame saving `r4` and `lr`
(8 bytes, keeping the stack 8-byte aligned), with `lr` kept in `r4` across
the call. The public ECB functions are this, so that the core's code, which
the modes call too, is in the crate once.
-/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- A call of `c`'s code, under its name, in a frame saving `r4` and `lr`. -/
def Core.wrap (c : Core) : Prog isa :=
  .frame (.push [.r4, .lr])
    (.seq (.block [.mov .r4 (.reg .lr)]) (.seq (.call c.name c.code) (.block [.mov .lr (.reg .r4)])))
    (.pop .r4 8)

end VG.Impl.Modes.Arm
