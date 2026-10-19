module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # The two local encodings and the outgoing arguments are separate -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

def localRegion (g : Geometry) (d n : Nat) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 d, n⟩

theorem localSub {g : Geometry} {d n : Nat} (fit : d + n ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) :
    (localRegion g d n).Sub g.innerRegion := Offset.sub_base _ fit

theorem Context.localWrite {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) {d n : Nat} (fit : d + n ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) :
    InRegions s.wr (localRegion g d n).base n := h.inner.write fit

theorem Context.em2Fit {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : g.em2.toNat + g.length ≤ 2 ^ 32 :=
  h.valid.encodingFit (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Context.em1Sub {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact localSub (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Context.em2Sub {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em2, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact localSub (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Context.em1Write {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.em1) g.length := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Context.em2Write {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.em2) g.length := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Context.em1Args {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 40⟩ := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint_base _ (by decide : 40 ≤ em1Offset)
    (by have := h.valid.maxLength; simp only [em1Offset]; omega)

theorem Context.encodingsSeparate {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint ⟨byteAddr g.em2, g.length⟩ := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide), Geometry.em2, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inl (by have := h.valid.maxLength; simp only [em1Offset, em2Offset]; omega))
    (by have := h.valid.maxLength; simp only [em1Offset]; omega)
    (by have := h.valid.maxLength; simp only [em2Offset]; omega)

end VG.Proof.RsaPkcs1Sig.X86.Ver
