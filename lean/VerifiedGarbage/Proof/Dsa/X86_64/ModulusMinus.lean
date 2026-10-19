module

import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.ResultCall
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import Mathlib.Tactic.Set

/-! # Encoded p-minus-one and q-minus-two for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Form and encode a modulus-minus constant without changing the modulus. -/
theorem modulusMinus_ok {s : State} {B : Addr} {Z o w wx m k amount : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m)
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
  change WP isa (.seq (.block ((Core.operand result resultLen output ++ Core.enter o) ++ minusHead amount))
    (.seq (wordLoop 1 minusTail) (seqs Core.finish))) s _
  rw [WP.seq_iff, WP.block_append_iff]
  exact WP.mono (WP.seq_iff.mp run) fun u hu =>
    WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => WP.seq hv

end VG.Proof.Dsa.X86_64
