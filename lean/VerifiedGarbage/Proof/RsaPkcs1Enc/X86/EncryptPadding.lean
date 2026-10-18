module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncoding

/-! # The padding prefix fixes the public destination cursor -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86

theorem padding_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary)
    (src : s.gpr .esi = g.sources 3) (count : s.gpr .ebp = BitVec.ofNat 32 g.paddingLength) :
    WP isa (.seq (.block head) psLoop) s fun t => W s ([0, 2] ++ bs 3) t := by
  have max := h.valid.maxLength
  have min := h.valid.minLength
  have room := h.valid.messageFits
  have padding := h.valid.padding
  have psBytes : Spec.Rsa.bytesAt s.mem (byteAddr (g.sources 3)) g.paddingLength = bs 3 := (h.sources 3).bytes
  have initial : W s [] s := ⟨Keeps.refl _ _, by rw [writeBytes_nil], by simp⟩
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Enc.X86.head_ok (h.buffer dst) (by omega) initial) ?_)
  rintro a ⟨wa, flag, ka⟩
  have psInput : Digest s g.length g.paddingLength := by
    have inp := h.input dst 3
    refine ⟨by rw [src]; exact inp.fit, ?_, ?_⟩
    · intro i hi; rw [src]; exact inp.readable i hi
    · intro i hi j hj; rw [src]; exact inp.separate i hi j hj
  refine WP.mono (psLoop_ok (h.buffer dst) max psInput (by omega) (by simp; omega) wa
    (ka.1 .esi (by decide)) ((ka.1 .ebp (by decide)).trans count)
    (prior := false) (by simpa using flag)) ?_
  rintro t ⟨wt, _⟩
  rw [src, psBytes] at wt
  exact wt

end VG.Proof.RsaPkcs1Enc.X86.Enc
