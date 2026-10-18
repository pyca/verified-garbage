module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptGeometry
public import VerifiedGarbage.Proof.Framework.Offset

/-! # Disjoint wrapper, callee, saved-register, and argument stack regions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt VG.Proof.Bignum.X86
namespace Geometry

theorem Valid.stackBase {g : Geometry} (h : g.Valid) :
    byteAddr g.stack = byteAddr (g.stack - BitVec.ofNat 32 24) + BitVec.ofNat 64 24 := by
  change g.stack.setWidth 64 = (g.stack - BitVec.ofNat 32 24).setWidth 64 + BitVec.ofNat 64 24
  rw [VG.X86.Taint.sub_setWidth h.stackLow]
  exact (BitVec.sub_add_cancel _ _).symm

theorem Valid.innerSub {g : Geometry} (h : g.Valid) : g.innerRegion.Sub g.wholeStack := by
  unfold innerRegion wholeStack
  rw [h.stackBase]
  exact Offset.sub_base _ (by decide : 24 + VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes ≤ encryptStack)

theorem Valid.savedSub {g : Geometry} (h : g.Valid) : g.savedRegion.Sub g.wholeStack := by
  unfold savedRegion wholeStack
  rw [h.stackBase, Offset.add_add]
  exact Offset.sub_base _ (by decide : (24 + VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes) + 16 ≤ encryptStack)

theorem Valid.calleeSub {g : Geometry} (_h : g.Valid) : g.calleeRegion.Sub g.wholeStack :=
  Region.sub_prefix (by decide : 24 ≤ encryptStack)

theorem Valid.calleeInner {g : Geometry} (h : g.Valid) : g.calleeRegion.Disjoint g.innerRegion := by
  unfold calleeRegion VG.X86.below innerRegion
  rw [h.stackBase]
  exact (Offset.disjoint_base _ (by decide : 24 ≤ 24) (by decide : 24 + VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes ≤ 2 ^ 64)).symm

theorem Valid.innerSaved {g : Geometry} (_h : g.Valid) : g.innerRegion.Disjoint g.savedRegion :=
  (Offset.disjoint_base _ (by decide : VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes ≤ VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes) (by decide : VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 16 ≤ 2 ^ 64)).symm

theorem Valid.offsetAddr {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 56) :
    byteAddr (g.stack + BitVec.ofNat 32 d) = byteAddr g.stack + BitVec.ofNat 64 d :=
  byteAddr_add (by have := h.stackHigh; omega)

theorem Valid.offsetNat {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 56) :
    (g.stack + BitVec.ofNat 32 d).toNat = g.stack.toNat + d := by
  have sum : g.stack.toNat + d < 2 ^ 32 := by have := h.stackHigh; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt sum]

theorem Valid.temporaryFit {g : Geometry} (h : g.Valid)  :
    g.temporary.toNat + g.length ≤ 2 ^ 32 := by
  rw [Geometry.temporary, h.offsetNat (by decide)]
  have := h.stackHigh
  have := h.maxLength
  simp only [emOffset, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes] at *
  omega

end Geometry
end VG.Proof.RsaPkcs1Enc.X86.Enc
