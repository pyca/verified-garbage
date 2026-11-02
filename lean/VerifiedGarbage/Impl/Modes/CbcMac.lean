module

public import VerifiedGarbage.Impl.Modes.Ops

/-!
# CBC-MAC, one block at a time, for any target

`Mode.cbcMac`: CBC encryption's chaining (SP 800-38A §6.2) without its
output, as CMAC (SP 800-38B §6.2, step 6) chains its blocks: each block of
the data is XORed into the chaining value, which the block cipher then
enciphers, and the data are only read. The chaining value goes back to the
IV at the end (`ivOut`).
-/

@[expose] public section

namespace VG.Impl.Modes.Mode

variable (bw : Nat)

/-- CBC-MAC: `buf := Mⱼ ⊕ C`, and `C := CIPH_K(buf)` to the chaining value;
nothing is written to the data. -/
def cbcMac : Mode where
  pre := xorBlk bw .buf .dat .chn
  post := copyBlk bw .chn .buf
  step := 4 * bw
  ivOut := true

end VG.Impl.Modes.Mode
