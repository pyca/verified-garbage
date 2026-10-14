module

public import VerifiedGarbage.Impl.Modes.Ops

/-! # CTR as operations on the three mode areas -/

@[expose] public section

namespace VG.Impl.Modes.Mode

/-- Copy the counter, encipher the copy, XOR it into the data and increment
all 128 bits of the counter. -/
def ctr : Mode where
  pre := copyBlk 4 .buf .chn
  post := xorBlk 4 .dat .dat .buf ++
    [{ inc := true, wide := true, dst := .chn, dOff := 0, src := .chn, sOff := 0 }]
  step := 16
  ivOut := true

end VG.Impl.Modes.Mode
