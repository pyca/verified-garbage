module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRelease
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverCmpArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverZero

/-! # Compare the reconstructed encoding and release the trailing digest under its mask -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)

def checkedRecovery (g : Geometry) (s : State) : Option (List Byte) :=
  match encodeId g.hash (digestBytes g s) g.length with
  | none => none
  | some em => if (decide (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length = em) && (savedStatus g s).getLsbD 0) then
      some (digestBytes g s) else none

theorem tail_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (enc : Encoded g s) : WP isa tail s fun t => Context g bs t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t ∧
      Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax) (checkedRecovery g s) := by
  unfold tail test0
  refine WP.seq (wp_cmpS rfl fun c C Z => WP.block_nil ?_)
  have hc := h.after (by rw [C.mem]; exact Frame.refl _ _) (C.keeps []) (congrFun C.gpr .esp)
  cases encoded : encodeId g.hash (digestBytes g s) g.length with
  | none =>
    have zero : s.gpr .eax = 0 := by simpa only [Encoded, encoded] using enc
    refine WP.ite true (by simp [eval, Z, zero]) (fun _ => ?_) (by simp)
    refine WP.mono (zeroOut_ok hc) ?_
    rintro t ⟨ht, bytes, ax, F, K⟩
    refine ⟨ht, ?_, (C.keeps clobbers).trans (K.mono (by decide)), ?_⟩
    · rw [C.mem] at F
      apply F.sub
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
    · simp only [checkedRecovery, encoded]
      exact ⟨ax, bytes⟩
  | some em =>
    obtain ⟨one, bytes⟩ : s.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length = em := by
      simpa only [Encoded, encoded] using enc
    refine WP.ite false (by simp [eval, Z, one]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpArgs_ok hc) ?_)
    rintro a ⟨ha, Ma, Ka, src, dst, cnt⟩
    refine WP.seq (WP.mono (compare_ok ha src dst cnt) ?_)
    rintro b ⟨hb, Mb, Kb, equal⟩
    refine WP.mono (release_ok hb) ?_
    rintro t ⟨ht, F, K, out⟩
    have ms : a.mem = s.mem := Ma.trans C.mem
    have mb : b.mem = s.mem := Mb.trans ms
    have decision : decide (b.gpr .ebp = 0) = decide (Spec.Rsa.bytesAt a.mem (byteAddr g.em1) g.length =
        Spec.Rsa.bytesAt a.mem (byteAddr g.em2) g.length) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact equal
    have bit : accepted g b = (decide (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length = em) && (savedStatus g s).getLsbD 0) := by
      unfold accepted savedStatus
      rw [decision, ms, bytes, mb]
    refine ⟨ht, ?_, (C.keeps clobbers).trans ((Ka.mono (by decide)).trans
      ((Kb.mono (by decide)).trans K)), ?_⟩
    · rw [mb] at F
      exact F
    · simp only [checkedRecovery, encoded]
      rw [bit, digestBytes, mb] at out
      exact out

end VG.Proof.RsaPkcs1Sig.X86.Rcv
