module

public import VerifiedGarbage.Impl.Dsa.Layout

/-! # DSA workspace on 32-bit x86

One arithmetic context is reused for p and q. Saved arguments and computed
big-endian values lie outside its largest possible footprint. The existing
DSA scratch contract already provides at least 16384 bytes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Layout
open VG.Impl.Dsa.Layout

/-- Saved pointers and lengths survive all arithmetic operations. -/
def field : Field → Nat
  | .p => 8192 | .q => 8196 | .g => 8200 | .y => 8204 | .x => 8208
  | .signature => 8212 | .nonce => 8216 | .digest => 8220 | .out => 8224
  | .pLen => 8228 | .qLen => 8232 | .digestLen => 8236 | .digestPrefixLen => 8240
  | .mask => 8244

/-- Saved ebx, ebp, esi, edi; none overlaps the arithmetic context. -/
def saved : Nat := 8256

/-- Persistent big-endian temporaries use the shared DSA suffix layout. -/
def scalars : List Nat := [r, s, inverse, u, v, z, qMinusTwo]
def wideValues : List Nat := [t, t2]

end VG.Impl.Dsa.X86.Layout
