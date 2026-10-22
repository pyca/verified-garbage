module

public import VerifiedGarbage.Impl.Modes.Ops

/-! # Counter mode with GCM's `inc₃₂` as operations on the three mode areas -/

@[expose] public section

namespace VG.Impl.Modes.Mode

/-- Copy the counter block, encipher the copy, XOR it into the data and
increment the counter block's last 32 bits, big-endian, modulo 2³² (GCM's
`inc₃₂`, NIST SP 800-38D §6.2), leaving its first 96 as they are. -/
def ctr32 : Mode where
  pre := copyBlk 4 .buf .chn
  post := xorBlk 4 .dat .dat .buf ++
    [{ inc32 := true, wide := true, dst := .chn, dOff := 12, src := .chn, sOff := 12 }]
  step := 16
  ivOut := true

end VG.Impl.Modes.Mode
