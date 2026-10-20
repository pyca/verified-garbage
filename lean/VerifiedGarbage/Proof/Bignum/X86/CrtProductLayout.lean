module

import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.WideLoop
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The full product and its multiplier are disjoint from both source slots -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem product_layout {n bytes a b : Nat} (hz : size n ≤ bytes)
    (ha : a < 20) (hb : b < 20) (ha' : a ≠ productSlot) (hb' : b ≠ productSlot) :
    WideLayout (2 * n) bytes (slot n productSlot) (slot n a) (slot n b) multiplierOffset := by
  have ba := slot_bound (n := n) ha
  have bb := slot_bound (n := n) hb
  have bo := slot_bound (n := n) (i := productSlot) (by decide)
  have ao := slot_sep (n := n) ha'
  have bO := slot_sep (n := n) hb'
  have ah := slot_header n a
  have bh := slot_header n b
  have oh := slot_header n productSlot
  simp only [stride] at ba bb bo ao bO
  unfold multiplierOffset
  constructor <;> omega

end VG.Proof.Bignum.X86.Crt
