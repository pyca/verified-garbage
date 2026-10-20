module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyGeometry
public import VerifiedGarbage.Proof.Framework.Offset

/-! # Disjoint wrapper, callee, saved-register, and argument stack regions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
namespace Geometry

theorem Valid.stackBase {g : Geometry} (h : g.Valid) :
    byteAddr g.stack = byteAddr (g.stack - BitVec.ofNat 32 44) + BitVec.ofNat 64 44 := by
  change g.stack.setWidth 64 = (g.stack - BitVec.ofNat 32 44).setWidth 64 + BitVec.ofNat 64 44
  rw [VG.X86.Taint.sub_setWidth h.stackLow]
  exact (BitVec.sub_add_cancel _ _).symm

theorem Valid.innerSub {g : Geometry} (h : g.Valid) : g.innerRegion.Sub g.wholeStack := by
  unfold innerRegion wholeStack
  rw [h.stackBase]
  exact Offset.sub_base _ (by decide : 44 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ verifyStack)

theorem Valid.savedSub {g : Geometry} (h : g.Valid) : g.savedRegion.Sub g.wholeStack := by
  unfold savedRegion wholeStack
  rw [h.stackBase, Offset.add_add]
  exact Offset.sub_base _ (by decide : (44 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) + 16 ≤ verifyStack)

theorem Valid.calleeSub {g : Geometry} (_h : g.Valid) : g.calleeRegion.Sub g.wholeStack :=
  Region.sub_prefix (by decide : 44 ≤ verifyStack)

theorem Valid.calleeInner {g : Geometry} (h : g.Valid) : g.calleeRegion.Disjoint g.innerRegion := by
  unfold calleeRegion VG.X86.below innerRegion
  rw [h.stackBase]
  exact (Offset.disjoint_base _ (by decide : 44 ≤ 44) (by decide : 44 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ 2 ^ 64)).symm

theorem Valid.innerSaved {g : Geometry} (_h : g.Valid) : g.innerRegion.Disjoint g.savedRegion :=
  (Offset.disjoint_base _ (by decide : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) (by decide : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 16 ≤ 2 ^ 64)).symm

theorem Valid.offsetAddr {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52) :
    byteAddr (g.stack + BitVec.ofNat 32 d) = byteAddr g.stack + BitVec.ofNat 64 d :=
  byteAddr_add (by have := h.stackHigh; omega)

theorem Valid.offsetNat {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52) :
    (g.stack + BitVec.ofNat 32 d).toNat = g.stack.toNat + d := by
  have sum : g.stack.toNat + d < 2 ^ 32 := by have := h.stackHigh; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt sum]

theorem Valid.encodingFit {g : Geometry} (h : g.Valid) {d : Nat} (hd : d + g.length ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) :
    (g.stack + BitVec.ofNat 32 d).toNat + g.length ≤ 2 ^ 32 := by
  rw [h.offsetNat (by omega)]
  have := h.stackHigh
  omega

end Geometry
end VG.Proof.RsaPkcs1Sig.X86.Ver
