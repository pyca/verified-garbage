module

public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader

/-! # Memory changed by a DSA validation call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum

def RangeFrame (B : Addr) (o wx : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (∀ r ∈ callRanges arg argLen, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) →
    (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (ofs B x < Field.mask.offset ∨ Field.mask.offset + 8 ≤ ofs B x) → mem' x = mem x

end VG.Proof.Dsa.AArch64
