module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverReleaseArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverEncoding
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseBuffer

/-! # Release only an accepted digest, otherwise write zeros, without a branch -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover

def clobbers : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

theorem release_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa release s fun t => Context g bs t ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps clobbers s t ∧ Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax)
        (if accepted g s then some (digestBytes g s) else none) := by
  unfold release
  refine WP.seq (WP.mono (releaseArgs_ok h) ?_)
  rintro a ⟨ha, M, K, status, mask, dst, cnt, src⟩
  have sourceWrite : InRegions a.wr (byteAddr g.digest) g.outputLength := by
    rw [h.valid.digestAddr]
    exact CallLay.inRegions_sub (off := g.length - g.outputLength) ha.em1Write
      (by have := h.valid.outputFits; omega) (by have := h.valid.maxLength; omega)
  have sep : (⟨byteAddr g.digest, g.outputLength⟩ : Region).Disjoint ⟨byteAddr g.output, g.outputLength⟩ :=
    h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x (h.em1Sub x (h.valid.digestSub x hx)))
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.PrivChecked.releaseBuffer_ok a
    h.valid.outputPositive (by have := h.valid.outputBound; omega) h.valid.digestFit h.valid.outputFit
    sourceWrite ha.outputWrite sep src dst cnt mask) ?_)
  rintro b ⟨out, _, F, T⟩
  have kt := (K.mono (by decide : ∀ r ∈ [.eax, .ebx, .edx, .edi, .ecx, .esi], r ∈ clobbers)).trans
    (T.mono (by decide))
  have frame : Frame (bodyWrites g) s.mem b.mem := by
    rw [M] at F
    apply F.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
    · exact ⟨g.innerRegion, by simp [bodyWrites], fun x hx => h.em1Sub x (h.valid.digestSub x hx)⟩
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  have keep := kt.trans (U.keeps.mono (by decide))
  have frameT : Frame (bodyWrites g) s.mem t.mem := by rw [U.mem]; exact frame
  refine ⟨h.after frameT keep (keep.1 .esp (by decide)), frameT, keep, ?_⟩
  have ax : t.gpr .eax = BitVec.ofNat 32 (accepted g s).toNat := by
    rw [U.gpr, T.1 .ebx (by decide), status]
  have bytes : Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.outputLength =
      if accepted g s then digestBytes g s else List.replicate g.outputLength 0 := by
    rw [U.mem, out, M]
    rfl
  cases good : accepted g s <;> simp only [good, Bool.false_eq_true, ite_false, ite_true,
    Spec.Rsa.written, Bool.toNat_false, Bool.toNat_true] at ax bytes ⊢ <;> exact ⟨ax, bytes⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
