module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrivateRegions
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScratch

/-! # Shared separation facts for hash and HMAC calls -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86

def callArgsRegion (g : Geometry) (n : Nat) : Region := ⟨byteAddr g.stack, n⟩

theorem Context.callArgsSub {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (_h : Context g bs s) {n : Nat} (fit : n ≤ 160) : (callArgsRegion g n).Sub g.innerRegion :=
  Region.sub_prefix fit

theorem Context.scratchRegion_pointer {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (start : d < 8448) :
    g.scratch d n = (⟨byteAddr (g.workspace + BitVec.ofNat 32 d), n⟩ : Region) := by
  rw [h.valid.scratchAddress start]
  rfl

theorem Context.calleeScratch {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (fit : d + n ≤ 8448) :
    g.calleeRegion.Disjoint (g.scratch d n) :=
  (h.valid.stackWorkspace.sub_left h.valid.calleeSub).sub_right (h.valid.scratchSub fit)

theorem Context.argsScratch {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {args d n : Nat} (afit : args ≤ 160) (fit : d + n ≤ 8448) :
    (callArgsRegion g args).Disjoint (g.scratch d n) :=
  (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x ((h.callArgsSub afit) x hx))).sub_right
    (h.valid.scratchSub fit)

theorem Context.callStackNat {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : (g.stack - 4).toNat = g.stack.toNat - 4 := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
  exact sub_toNat (by have := h.valid.stackLow; unfold calleeBytes at this; omega)

theorem Context.callBelowSub {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {n : Nat} (fit : n ≤ 3368) :
    (⟨(g.stack - 4).setWidth 64 - BitVec.ofNat 64 n, n⟩ : Region).Sub g.calleeRegion := by
  rw [← VG.X86.Taint.sub_setWidth (by rw [h.callStackNat]; have := h.valid.stackLow; unfold calleeBytes at this; omega : n ≤ (g.stack - 4).toNat)]
  exact VG.X86.below_inner (by unfold calleeBytes; omega : n + 4 ≤ calleeBytes) h.valid.stackLow

theorem Context.returnScratch {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (fit : d + n ≤ 8448) :
    (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Disjoint (g.scratch d n) :=
  (h.calleeScratch fit).sub_left h.retSub

theorem Context.returnArgs {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {n : Nat} (fit : n ≤ 160) :
    (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Disjoint (callArgsRegion g n) :=
  (h.valid.calleeInner.sub_right (h.callArgsSub fit)).sub_left h.retSub

theorem Context.belowScratch {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {bytes d n : Nat} (bound : bytes ≤ 3368) (fit : d + n ≤ 8448) :
    (⟨(g.stack - 4).setWidth 64 - BitVec.ofNat 64 bytes, bytes⟩ : Region).Disjoint (g.scratch d n) :=
  (h.calleeScratch fit).sub_left (h.callBelowSub bound)

theorem Context.belowArgs {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {bytes n : Nat} (bound : bytes ≤ 3368) (fit : n ≤ 160) :
    (⟨(g.stack - 4).setWidth 64 - BitVec.ofNat 64 bytes, bytes⟩ : Region).Disjoint (callArgsRegion g n) :=
  (h.valid.calleeInner.sub_right (h.callArgsSub fit)).sub_left (h.callBelowSub bound)

end VG.Proof.RsaPkcs1Enc.X86.Dec
