module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptContext

/-! # Subregions used by the nested checked RSA call -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86

theorem Context.outgoingSub {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (_h : Context g bs s) : (⟨byteAddr g.stack, 80⟩ : Region).Sub g.innerRegion :=
  Region.sub_prefix (by decide)

theorem Context.outgoingWrite {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.stack) 80 := by
  have W := h.inner.write (d := 0) (n := 80) (by decide)
  simpa only [BitVec.add_zero] using W

theorem Context.retSub {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
  VG.X86.below_sub (by decide : 4 ≤ calleeBytes) h.valid.stackLow

theorem Context.belowSub {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : (⟨(g.stack - 4).setWidth 64 - 3368#64, 3368⟩ : Region).Sub g.calleeRegion := by
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 :=
    sub_toNat (k := 4) (by have := h.valid.stackLow; simp only [calleeBytes] at this; omega)
  rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; simp only [calleeBytes] at this; omega : 3368 ≤ (g.stack - 4).toNat)]
  exact VG.X86.below_inner (by decide : 3368 + 4 ≤ calleeBytes) h.valid.stackLow

end VG.Proof.RsaPkcs1Enc.X86.Dec
