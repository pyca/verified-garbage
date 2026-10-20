module

public import VerifiedGarbage.Impl.Dsa.Layout

/-! # DSA workspace on 32-bit ARM

One arithmetic context is reused for p and q, at the base of `scratch`
(`r12`). The saved arguments and the callee-saved registers lie in its
header, within an immediate offset of `r12`; computed big-endian values lie
past its largest footprint, at the shared DSA suffix layout.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Layout
open VG.Impl.Dsa.Layout

/-- Saved pointers and lengths survive all arithmetic operations. -/
def field : Field → Nat
  | .p => 64 | .q => 68 | .g => 72 | .y => 76 | .x => 80
  | .signature => 84 | .nonce => 88 | .digest => 92 | .out => 96
  | .pLen => 100 | .qLen => 104 | .digestLen => 108 | .digestPrefixLen => 112
  | .mask => 116

/-- The saved `r4`–`r11` and `lr`. -/
def saved : Nat := 128

end VG.Impl.Dsa.Arm.Layout
