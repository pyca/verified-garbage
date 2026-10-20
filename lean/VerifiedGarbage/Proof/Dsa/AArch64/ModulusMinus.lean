module

import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.Call

/-! # Encoded p-minus-one and q-minus-two for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Form and encode a modulus-minus constant without changing the modulus. -/
theorem modulusMinus_ok {s : State} {B : Addr} {Z o w wx m k amount : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 16)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 16) (ham : amount ≤ m)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Checks.modulusMinus o amount output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k (m - amount) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have run := resultCall_ok hg child hZ hlo hhi ho output houtp hl hk1 hk' hkw hout hprefix
    (fun _ hc hm => minus_ok hc hm hw hw' ha ham)
  exact run

end VG.Proof.Dsa.AArch64
