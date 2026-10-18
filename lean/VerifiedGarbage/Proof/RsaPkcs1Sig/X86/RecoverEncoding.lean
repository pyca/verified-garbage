module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigestArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-! # Re-encode the trailing digest in a separate buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes

def digestBytes (g : Geometry) (s : State) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr g.digest) g.outputLength

theorem Context.digestRead {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    InRegions (s.rd ++ s.wr) (byteAddr g.digest) g.outputLength := by
  have read : InRegions (s.rd ++ s.wr) (byteAddr g.em1) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em1Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [h.valid.digestAddr]
  exact CallLay.inRegions_sub (off := g.length - g.outputLength) read
    (by have := h.valid.outputFits; omega) (by have := h.valid.maxLength; omega)

theorem encoding_pre {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.em2)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.digest) (count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength) :
    EPre s g.hash g.length := by
  have out32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega
  refine ⟨hash, len, h.valid.maxLength, ⟨by rw [dst]; exact h.em2Fit, ?_⟩, ?_⟩
  · intro i hi
    rw [dst, byteAddr_add (by have := h.em2Fit; omega)]
    exact CallLay.inRegions_sub (off := i) h.em2Write (by omega) (by have := h.valid.maxLength; omega)
  · rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt out32]
    refine ⟨by rw [src]; exact h.valid.digestFit, ?_, ?_⟩
    · intro i hi
      rw [src, byteAddr_add (by have := h.valid.digestFit; omega)]
      exact CallLay.inRegions_sub (off := i) h.digestRead (by omega) (by have := h.valid.outputBound; omega)
    · intro i hi j hj
      rw [src, byteAddr_add (by have := h.valid.digestFit; omega), dst, byteAddr_add (by have := h.em2Fit; omega)]
      exact VG.Proof.RsaPkcs1Sig.ne_of_disjoint
        (h.encodingsSeparate.sub_left h.valid.digestSub)
        (by have := h.valid.outputBound; omega) (by have := h.valid.maxLength; omega) hi hj

def Encoded (g : Geometry) (s : State) : Prop :=
  match encodeId g.hash (digestBytes g s) g.length with
  | none => s.gpr .eax = 0
  | some em => s.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length = em

theorem encoding_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.em2)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.digest) (count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.em2, g.length⟩] s.mem t.mem ∧ Keeps clob s t ∧ Encoded g t := by
  refine WP.mono (encode_ok (encoding_pre h dst len hash src count)) ?_
  rintro t ⟨K, out⟩
  have out32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega
  rw [src, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt out32] at out
  change EOut s t (encodeId g.hash (digestBytes g s) g.length) at out
  have frame : Frame [⟨byteAddr g.em2, g.length⟩] s.mem t.mem := by
    cases e : encodeId g.hash (digestBytes g s) g.length with
    | none => rw [e] at out; rw [out.2]; exact Frame.refl _ _
    | some em =>
      rw [e] at out
      have length : em.length = g.length := by
        unfold encodeId at e
        cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
        | none => simp [id] at e
        | some hv => simp only [id, Option.bind_some] at e; exact encode_length e
      rw [out.2, dst]
      exact writeBytes_frame _ _ _ (by rw [length]; exact Region.contains_self _ _)
  have bytes : digestBytes g t = digestBytes g s :=
    VG.Proof.Rsa.rsa_bytes_frame frame (by have := h.valid.outputBound; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact h.encodingsSeparate.sub_left h.valid.digestSub)
  refine ⟨h.after (frame.sub ?_) K (K.1 .esp (by decide)), frame, K, ?_⟩
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], h.em2Sub⟩
  · unfold Encoded
    rw [bytes]
    cases e : encodeId g.hash (digestBytes g s) g.length with
    | none => rw [e] at out; exact out.1
    | some em =>
      rw [e] at out
      refine ⟨out.1, ?_⟩
      rw [out.2, dst]
      have length : em.length = g.length := by
        unfold encodeId at e
        cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
        | none => simp [id] at e
        | some hv => simp only [id, Option.bind_some] at e; exact encode_length e
      rw [← length]
      exact bytesAt_writeBytes _ _ _ (by rw [length]; have := h.valid.maxLength; omega)

end VG.Proof.RsaPkcs1Sig.X86.Rcv
