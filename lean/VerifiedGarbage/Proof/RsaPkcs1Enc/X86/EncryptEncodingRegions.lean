module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptContext
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeHead
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeMessage

/-! # Permissions and exact frames for the encryption encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem Context.temporarySub {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
  exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [emOffset, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes]; omega)

theorem Context.temporaryWrite {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.temporary) g.length := by
  rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [emOffset, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes]; omega)

theorem Context.buffer {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary) : Buf s g.length := by
  refine ⟨by rw [dst]; exact h.valid.temporaryFit, ?_⟩
  intro i hi
  rw [dst, byteAddr_add (by have := h.valid.temporaryFit; omega)]
  exact CallLay.inRegions_sub (off := i) h.temporaryWrite (by omega) (by have := h.valid.maxLength; omega)

theorem Context.input {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary) (i : Fin 5) :
    MessageSource s (g.sources i) g.length (g.sourceLength i) := by
  refine ⟨(h.sources i).fits, ?_, ?_⟩
  · intro j hj
    rw [byteAddr_add (by have := (h.sources i).fits; omega)]
    exact CallLay.inRegions_sub (off := j) (h.sources i).read (by omega)
      (by have := (h.sources i).fits; omega)
  · intro j hj k hk eq
    rw [byteAddr_add (by have := (h.sources i).fits; omega), dst,
      byteAddr_add (by have := h.valid.temporaryFit; omega)] at eq
    have sep := ((h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (h.temporarySub x hx))).symm
    apply sep (byteAddr (g.sources i) + BitVec.ofNat 64 j)
    · exact Offset.contains_base _ (by omega) (by have := (h.sources i).fits; omega)
    · rw [eq]
      exact Offset.contains_base _ (by omega) (by have := h.valid.maxLength; omega)

theorem Context.afterEncoding {g : Geometry} {bs : Fin 5 → List Byte} {s t : State} {acc : List Byte}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary) (length : acc.length ≤ g.length)
    (w : W s acc t) : Context g bs t ∧ Frame [⟨byteAddr g.temporary, g.length⟩] s.mem t.mem := by
  have F : Frame [⟨byteAddr g.temporary, g.length⟩] s.mem t.mem := by
    rw [w.mem, dst]
    exact writeBytes_frame _ _ _ (by simpa using Offset.contains_base (byteAddr g.temporary) (d := 0) (by omega : 0 + acc.length ≤ g.length) (by decide))
  refine ⟨h.after (F.sub ?_) w.rest (w.rest.1 .esp (by decide)), F⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], h.temporarySub⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
