module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncodeArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeHead
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeMessage

/-! # The complete byte-exact encryption encoding and its padding-validity bit -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem encoding_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary)
    (src : s.gpr .esi = g.sources 3) (count : s.gpr .ebp = BitVec.ofNat 32 g.paddingLength) :
    WP isa encoding s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.temporary, g.length⟩] s.mem t.mem ∧ Keeps clob s t ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = Spec.RsaPkcs1Enc.encode (bs 2) (bs 3) ∧
      t.gpr .ebx = BitVec.ofNat 32 (hasZero (bs 3)).toNat := by
  have max := h.valid.maxLength
  have min := h.valid.minLength
  have room := h.valid.messageFits
  have padding := h.valid.padding
  have psLength : (bs 3).length = g.paddingLength := (h.sources 3).length
  have msgLength : (bs 2).length = g.messageLength := (h.sources 2).length
  have psBytes : Spec.Rsa.bytesAt s.mem (byteAddr (g.sources 3)) g.paddingLength = bs 3 := (h.sources 3).bytes
  have msgBytes : Spec.Rsa.bytesAt s.mem (byteAddr (g.sources 2)) g.messageLength = bs 2 := (h.sources 2).bytes
  have total : (Spec.RsaPkcs1Enc.encode (bs 2) (bs 3)).length = g.length := by
    simp only [Spec.RsaPkcs1Enc.encode, List.length_append, List.length_cons, List.length_nil, psLength, msgLength]
    omega
  have initial : W s [] s := ⟨Keeps.refl _ _, by rw [writeBytes_nil], by simp⟩
  unfold encoding
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Enc.X86.head_ok (h.buffer dst) (by omega) initial) ?_)
  rintro a ⟨wa, flag, ka⟩
  have psInput : Digest s g.length g.paddingLength := by
    have inp := h.input dst 3
    refine ⟨by rw [src]; exact inp.fit, ?_, ?_⟩
    · intro i hi; rw [src]; exact inp.readable i hi
    · intro i hi j hj; rw [src]; exact inp.separate i hi j hj
  refine WP.seq (WP.mono (psLoop_ok (h.buffer dst) max psInput (by omega) (by simp; omega) wa
    ((ka.1 .esi (by decide)).trans rfl) ((ka.1 .ebp (by decide)).trans count)
    (prior := false) (by simpa using flag)) ?_)
  rintro b ⟨wb, fb⟩
  rw [src, psBytes] at wb fb
  simp only [Bool.false_or] at fb
  refine WP.seq (WP.mono (messageArgs_ok h dst (by simp only [List.length_append, List.length_cons, List.length_nil, psLength]; omega) wb) ?_)
  rintro c ⟨wc, sc, cc, fc⟩
  have messageInput : MessageSource s (g.sources 2) g.length g.messageLength := h.input dst 2
  refine WP.mono (message_ok (h.buffer dst) max messageInput
    (by simp only [List.length_append, List.length_cons, List.length_nil, psLength]; omega) wc sc cc) ?_
  rintro t ⟨wt, ft⟩
  rw [msgBytes] at wt
  change W s (Spec.RsaPkcs1Enc.encode (bs 2) (bs 3)) t at wt
  obtain ⟨ht, frame⟩ := h.afterEncoding dst (by rw [total]) wt
  refine ⟨ht, frame, wt.rest, ?_, ft.trans (fc.trans fb)⟩
  rw [wt.mem, dst, ← total]
  exact VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ (by rw [total]; omega)

end VG.Proof.RsaPkcs1Enc.X86.Enc
