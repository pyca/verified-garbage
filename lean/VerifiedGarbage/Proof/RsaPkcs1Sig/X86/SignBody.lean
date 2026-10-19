module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignAfter

/-! # Complete signing body produces the shared PKCS #1 signing outcome -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Impl.RsaPkcs1Sig.X86.Sign
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

theorem body_ok (v : CrtImpl) {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (body (privName v) (privCode v)) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax) (result g bs) ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t := by
  unfold body
  refine WP.seq (WP.mono (encArgs_ok h) ?_)
  rintro a ⟨ha, M, K, dst, len, hash, src, count⟩
  refine WP.seq (WP.mono (encoding_ok ha dst len hash src count) ?_)
  rintro b ⟨hb, Fb, Kb, enc⟩
  refine WP.mono (afterEnc_ok v hb enc) ?_
  rintro t ⟨_, out, Ft, Kt⟩
  have frame : Frame (bodyWrites g) s.mem b.mem := by
    rw [M] at Fb
    apply Fb.sub
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  exact ⟨out, frame.trans Ft, (K.mono (by decide)).trans ((Kb.mono (by decide)).trans Kt)⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
