module

public import VerifiedGarbage.Proof.Rsa.X86.PrivGeometry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-! # Disjoint wrapper, callee, saved-register, and argument stack regions -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86
namespace PrivGeometry

theorem Valid.stackBase {g : PrivGeometry} (h : g.Valid) :
    byteAddr g.stack = byteAddr (g.stack - BitVec.ofNat 32 24) + BitVec.ofNat 64 24 := by
  change g.stack.setWidth 64 = (g.stack - BitVec.ofNat 32 24).setWidth 64 + BitVec.ofNat 64 24
  rw [VG.X86.Taint.sub_setWidth h.stackLow]
  exact (BitVec.sub_add_cancel _ _).symm

theorem Valid.innerSub {g : PrivGeometry} (h : g.Valid) : g.innerRegion.Sub g.wholeStack := by
  unfold innerRegion wholeStack
  rw [h.stackBase]
  exact Offset.sub_base _ (by decide : 24 + VG.Impl.Rsa.X86.PrivChecked.frameBytes ≤ stackBytes)

theorem Valid.savedSub {g : PrivGeometry} (h : g.Valid) : g.savedRegion.Sub g.wholeStack := by
  unfold savedRegion wholeStack
  rw [h.stackBase, Offset.add_add]
  exact Offset.sub_base _ (by decide : (24 + VG.Impl.Rsa.X86.PrivChecked.frameBytes) + 16 ≤ stackBytes)

theorem Valid.calleeSub {g : PrivGeometry} (_h : g.Valid) : g.calleeRegion.Sub g.wholeStack :=
  Region.sub_prefix (by decide : 24 ≤ stackBytes)

theorem Valid.calleeInner {g : PrivGeometry} (h : g.Valid) : g.calleeRegion.Disjoint g.innerRegion := by
  unfold calleeRegion VG.X86.below innerRegion
  rw [h.stackBase]
  exact (Offset.disjoint_base _ (by decide : 24 ≤ 24) (by decide : 24 + VG.Impl.Rsa.X86.PrivChecked.frameBytes ≤ 2 ^ 64)).symm

theorem Valid.innerSaved {g : PrivGeometry} (_h : g.Valid) : g.innerRegion.Disjoint g.savedRegion :=
  (Offset.disjoint_base _ (by decide : VG.Impl.Rsa.X86.PrivChecked.frameBytes ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes) (by decide : VG.Impl.Rsa.X86.PrivChecked.frameBytes + 16 ≤ 2 ^ 64)).symm

theorem Valid.offsetAddr {g : PrivGeometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80) :
    byteAddr (g.stack + BitVec.ofNat 32 d) = byteAddr g.stack + BitVec.ofNat 64 d :=
  byteAddr_add (by have := h.stackHigh; omega)

theorem Valid.offsetNat {g : PrivGeometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80) :
    (g.stack + BitVec.ofNat 32 d).toNat = g.stack.toNat + d := by
  have sum : g.stack.toNat + d < 2 ^ 32 := by have := h.stackHigh; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt sum]

theorem Valid.temporaryFit {g : PrivGeometry} (h : g.Valid) : g.temporary.toNat + g.length ≤ 2 ^ 32 := by
  rw [temporary, h.offsetNat (by decide)]
  have := h.stackHigh
  have := h.maxLength
  simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes] at *
  omega

theorem Valid.precomputationFit {g : PrivGeometry} (h : g.Valid) :
    g.precomputation.toNat + 16 * Spec.Rsa.modulusWords g.length ≤ 2 ^ 32 := by
  rw [precomputation, h.offsetNat (by decide)]
  have := h.stackHigh
  have := h.maxLength
  simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords] at *
  omega
end PrivGeometry
end VG.Proof.Rsa.X86.PrivChecked
