module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-! # Encode the digest into the private frame and retain its exact bytes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86.Sign

theorem Context.temporarySub {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
  exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [emOffset, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega)

theorem Context.temporaryWrite {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.temporary) g.length := by
  rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [emOffset, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega)

theorem encoding_pre {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.sources 2) (count : s.gpr .ebp = BitVec.ofNat 32 g.digestLength) :
    EPre s g.hash g.length := by
  have df := h.valid.digestBound
  refine ⟨hash, len, h.valid.maxLength, ⟨by rw [dst]; exact h.valid.temporaryFit, ?_⟩, ?_⟩
  · intro i hi
    rw [dst, byteAddr_add (by have := h.valid.temporaryFit; omega)]
    exact CallLay.inRegions_sub (off := i) h.temporaryWrite (by omega) (by have := h.valid.maxLength; omega)
  · rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt df]
    refine ⟨by rw [src]; exact (h.sources 2).fits, ?_, ?_⟩
    · intro i hi
      rw [src, byteAddr_add (by have := (h.sources 2).fits; change (g.sources 2).toNat + g.digestLength ≤ 2 ^ 32 at this; omega)]
      exact CallLay.inRegions_sub (off := i) (h.sources 2).read (by exact Nat.succ_le_of_lt hi) (by change g.digestLength < 2 ^ 64; omega)
    · intro i hi j hj eq
      rw [src, byteAddr_add (by have := (h.sources 2).fits; change (g.sources 2).toNat + g.digestLength ≤ 2 ^ 32 at this; omega),
        dst, byteAddr_add (by have := h.valid.temporaryFit; omega)] at eq
      have sep := ((h.valid.stackSources 2).sub_left (fun x hx => h.valid.innerSub x (h.temporarySub x hx))).symm
      apply sep (byteAddr (g.sources 2) + BitVec.ofNat 64 i)
      · exact Offset.contains_base _ (by change i + 1 ≤ g.digestLength; omega) (by omega)
      · rw [eq]
        exact Offset.contains_base _ (by omega) (by have := h.valid.maxLength; omega)

def Encoded (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  match encodeId g.hash (bs 2) g.length with
  | none => s.gpr .eax = 0
  | some em => s.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length = em

theorem encoding_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.temporary)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.sources 2) (count : s.gpr .ebp = BitVec.ofNat 32 g.digestLength) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s fun t => Context g bs t ∧
      Frame [g.innerRegion] s.mem t.mem ∧ Keeps clob s t ∧ Encoded g bs t := by
  refine WP.mono (encode_ok (encoding_pre h dst len hash src count)) ?_
  intro t post
  obtain ⟨K, out⟩ := post
  have df := h.valid.digestBound
  rw [src, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt df] at out
  have digestBytes : Spec.Rsa.bytesAt s.mem (byteAddr (g.sources 2)) g.digestLength = bs 2 := (h.sources 2).bytes
  rw [digestBytes] at out
  cases result : encodeId g.hash (bs 2) g.length with
  | none =>
    rw [result] at out
    have F : Frame [g.innerRegion] s.mem t.mem := by rw [out.2]; exact Frame.refl _ _
    refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
    · simp only [Encoded, result]; exact out.1
  | some em =>
    rw [result] at out
    have length : em.length = g.length := by
      unfold encodeId at result
      cases hh : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
      | none => simp [hh] at result
      | some hv => simp only [hh, Option.bind_some] at result; exact encode_length result
    have F : Frame [g.innerRegion] s.mem t.mem := by
      rw [out.2, dst, Geometry.temporary, h.valid.offsetAddr (by decide)]
      exact writeBytes_frame _ _ _ (Offset.contains_base _ (by rw [length]; have := h.valid.maxLength; simp only [emOffset, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega) (by decide))
    refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
    · simp only [Encoded, result]
      refine ⟨out.1, ?_⟩
      rw [out.2, dst, ← length]
      exact bytesAt_writeBytes _ _ _ (by rw [length]; have := h.valid.maxLength; omega)

end VG.Proof.RsaPkcs1Sig.X86.Sgn
