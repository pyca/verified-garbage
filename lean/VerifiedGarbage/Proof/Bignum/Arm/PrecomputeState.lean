module
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase

/-! # Public workspace shape and per-execution RSA precomputation invariants -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt wOf Layout)

structure PrecomputeWorkspace (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

structure PrecomputeInput (base src : BitVec 32) (len w k : Nat) (s : State) : Prop extends
    PrecomputeWorkspace base len w s where
  positive : 0 < k
  fits : k ≤ 8 * w
  sourceFits : src.toNat + k ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) k
  separate : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩
  source : s.gpr .r4 = src
  count : s.gpr .r6 = BitVec.ofNat 32 k
  large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1

structure PrecomputeModulus (base : BitVec 32) (len w : Nat) (s : State) : Prop extends
    PrecomputeWorkspace base len w s where
  large : 1 < numAt s.mem (State.addr base) w 0
  odd : numAt s.mem (State.addr base) w 0 % 2 = 1

theorem importModulus_ready_value (s : State) {base src : BitVec 32} {len w k : Nat}
    (h : PrecomputeInput base src len w k s) :
    WP isa importModulus s fun t => PrecomputeModulus base len w t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) := by
  refine WP.mono (importModulus_ok s h.workspace h.layout h.width h.positive h.fits h.sourceFits
    h.readable h.separate h.ptr h.source h.count h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨layout, width, ptr, value, frame, rest⟩
  refine ⟨?_, value⟩
  refine ⟨⟨h.workspace.congr rest.wr, layout, width, ptr, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp
  · rw [value]; exact h.large
  · rw [value]; exact h.odd

theorem importModulus_ready (s : State) {base src : BitVec 32} {len w k : Nat}
    (h : PrecomputeInput base src len w k s) :
    WP isa importModulus s (PrecomputeModulus base len w) :=
  WP.mono (importModulus_ready_value s h) (fun _ j => j.1)

theorem precomputeInverse_ready_value (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrecomputeModulus base len w s) : WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 :=
  WP.mono (precomputeInverse_ok s h.workspace h.layout h.width h.ptr h.odd h.large
    h.stackRead h.stackSep h.saved) (fun _ j => ⟨j.1, j.2.1⟩)


theorem precomputeInverse_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrecomputeModulus base len w s) : WP isa precomputeInverse s (ArithmeticReady base len w) :=
  WP.mono (precomputeInverse_ready_value s h) (fun _ j => j.1)

end VG.Proof.Bignum.Arm
