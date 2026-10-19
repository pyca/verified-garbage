module
public import VerifiedGarbage.Proof.Dsa.X86_64.Call

import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import Mathlib.Tactic.Set

/-! # Streaming reduction in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete streaming reduction call, including empty digest inputs. -/
theorem coreReduce_ok (M : Mont) {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (a output : Operand) (ha : pointerFits a.pointer)
    (houtp : pointerFits output.pointer) {ba : List Byte}
    (has : OperandBytes s B Z a ba) (hal : ba.length < 2 ^ 64)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.reduce M.mm a output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ba % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call2_ok hg child hZ hlo hhi (by decide) a output ha houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  exact reduce_ok M hc hw2 hw48 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) hargs.1 (hargs.2.1.trans has.length)
    (arguments_source hf hk (Nat.le_trans (by decide) hZ) has.source) hal

end VG.Proof.Dsa.X86_64
