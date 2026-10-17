module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivGeometry
public import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Disjoint wrapper, callee, saved-register, and argument stack regions -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked
namespace PrivGeometry

theorem Valid.stackBase {g : PrivGeometry} (h : g.Valid) :
    State.addr g.stack = State.addr (g.stack - BitVec.ofNat 32 56) + BitVec.ofNat 64 56 := by
  rw [FrameStack.addr_sub' h.stackLow]
  exact (BitVec.sub_add_cancel _ _).symm

theorem Valid.innerSub {g : PrivGeometry} (h : g.Valid) : g.innerRegion.Sub g.wholeStack := by
  unfold innerRegion wholeStack
  rw [h.stackBase]
  exact Offset.sub_base _ (by decide : 56 + frameBytes ≤ stackBytes)

theorem Valid.savedSub {g : PrivGeometry} (h : g.Valid) : g.savedRegion.Sub g.wholeStack := by
  unfold savedRegion wholeStack
  rw [h.stackBase, Offset.add_add]
  exact Offset.sub_base _ (by decide : (56 + frameBytes) + 56 ≤ stackBytes)

theorem Valid.calleeSub {g : PrivGeometry} (_h : g.Valid) : g.calleeRegion.Sub g.wholeStack :=
  Region.sub_prefix (by decide : 56 ≤ stackBytes)

theorem Valid.calleeInner {g : PrivGeometry} (h : g.Valid) : g.calleeRegion.Disjoint g.innerRegion := by
  unfold calleeRegion FrameStack.belowA innerRegion
  rw [h.stackBase]
  exact (Offset.disjoint_base _ (by decide : 56 ≤ 56) (by decide : 56 + frameBytes ≤ 2 ^ 64)).symm

theorem Valid.innerSaved {g : PrivGeometry} (_h : g.Valid) : g.innerRegion.Disjoint g.savedRegion :=
  (Offset.disjoint_base _ (by decide : frameBytes ≤ frameBytes) (by decide : frameBytes + 56 ≤ 2 ^ 64)).symm

theorem Valid.offsetAddr {g : PrivGeometry} (h : g.Valid) {d : Nat} (fit : d < frameBytes + 56 + 64) :
    State.addr (g.stack + BitVec.ofNat 32 d) = State.addr g.stack + BitVec.ofNat 64 d :=
  addr_add (by have := h.stackHigh; omega)

theorem Valid.offsetNat {g : PrivGeometry} (h : g.Valid) {d : Nat} (fit : d < frameBytes + 56 + 64) :
    (g.stack + BitVec.ofNat 32 d).toNat = g.stack.toNat + d := by
  have sum : g.stack.toNat + d < 2 ^ 32 := by have := h.stackHigh; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt sum]

theorem Valid.temporaryFit {g : PrivGeometry} (h : g.Valid) : g.temporary.toNat + g.length ≤ 2 ^ 32 := by
  rw [temporary, h.offsetNat (by decide)]
  have := h.stackHigh
  have := h.maxLength
  simp only [oM, frameBytes] at *
  omega

theorem Valid.precomputationFit {g : PrivGeometry} (h : g.Valid) :
    g.precomputation.toNat + 16 * Spec.Rsa.modulusWords g.length ≤ 2 ^ 32 := by
  rw [precomputation, h.offsetNat (by decide)]
  have := h.stackHigh
  have := h.maxLength
  simp only [oPre, frameBytes, Spec.Rsa.modulusWords] at *
  omega
end PrivGeometry
end VG.Proof.Rsa.Arm
