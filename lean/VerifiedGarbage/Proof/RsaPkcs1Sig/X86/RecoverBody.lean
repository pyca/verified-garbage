module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLength

/-! # The recovery body releases precisely the digest accepted by the shared spec -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover

def Precomputed (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength)

theorem calleeFrame {g : Geometry} {bs : Fin 4 → List Byte} {s : State} {m m' : Mem}
    (h : Context g bs s) (F : Frame (publicWr g ++ [g.calleeRegion]) m m') :
    Frame (bodyWrites g) m m' := F.sub (by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact publicWrites_sub h r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)

theorem body_ok (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (body v.name v.code) s fun t =>
      Context g bs t ∧ Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t ∧
      (Precomputed g bs s → Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax) (recovered g bs)) := by
  unfold body
  refine WP.seq (WP.mono (lengthCheck_ok h) ?_)
  rintro c ⟨hc, Mc, Kc, Z⟩
  by_cases length : g.signatureLength = g.length
  · refine WP.ite false (by simp [eval, Z, length]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (pubArgs_ok hc) ?_)
    rintro a ⟨ha, args, Fa, Ka⟩
    refine WP.seq (WP.mono (public_call v ha args length) ?_)
    rintro b ⟨hb, Fb, Kb, out⟩
    refine WP.mono (afterPub_ok hb) ?_
    rintro t ⟨ht, Ft, Kt, value⟩
    have Fargs : Frame (bodyWrites g) s.mem a.mem := by
      rw [Mc] at Fa
      apply Fa.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
    refine ⟨ht, Fargs.trans ((calleeFrame h Fb).trans Ft),
      (Kc.mono (by decide)).trans ((Ka.mono (by decide)).trans
        ((Kb.mono (by decide)).trans Kt)), ?_⟩
    intro cache
    have words : Spec.Rsa.wordsAt a.mem (byteAddr (g.sources 3)) g.preLength =
        Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength :=
      VG.Proof.Rsa.wordsAt_frame Fargs (by
        have fit := h.valid.sourceFits 3
        change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
        omega) (h.sourceSeparate 3)
    have pre : Precomputed g bs a := by unfold Precomputed at cache ⊢; rw [words]; exact cache
    rw [checkedPublicRecovery_eq hb length (out pre)] at value
    exact value
  · refine WP.ite true (by simp [eval, Z, length]) (fun _ => ?_) (by simp)
    refine WP.mono (zeroOut_ok hc) ?_
    rintro t ⟨ht, bytes, ax, F, K⟩
    refine ⟨ht, ?_, (Kc.mono (by decide)).trans (K.mono (by decide)), ?_⟩
    · rw [Mc] at F
      apply F.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
    · intro _
      rw [recovered_bad h length]
      exact ⟨ax, bytes⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
