module

public import VerifiedGarbage.Impl.Modes.Arm.Seq

@[expose] public section

namespace VG.Impl.Modes.Arm

/-- CTR encrypts a copy of the counter, XORs the data, and increments the
128-bit big-endian counter, returning its next value in the IV. -/
def ctr : Mode :=
  { pre := [.copy .t .o], tgt := .t, post := [.xor .d .t, .inc], finish := true }

end VG.Impl.Modes.Arm
