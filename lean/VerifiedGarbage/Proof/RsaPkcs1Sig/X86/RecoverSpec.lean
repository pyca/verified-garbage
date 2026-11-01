module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRelease
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverCmpArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverZero
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigestArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
/-! # Re-encoding the trailing digest implements the shared recovery specification -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverTail.lean`, which only this module imported.
section

/-! # Compare the reconstructed encoding and release the trailing digest under its mask -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverAfter.lean`, which only this module imported.
section

/-! # Re-encoding and masked release preserve the public operation's meaning -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (statusOffset em1Offset em2Offset)
open VG.Impl.RsaPkcs1Sig.X86.Recover

def checkedPublicRecovery (g : Geometry) (s : State) : Option (List Byte) :=
  match encodeId g.hash (digestBytes g s) g.length with
  | none => none
  | some em => if (decide (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length = em) && (s.gpr .eax).getLsbD 0) then
      some (digestBytes g s) else none

theorem Context.em1Status {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint (localRegion g statusOffset 4) := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inr (by decide : statusOffset + 4 ≤ em1Offset))
    (by have := h.valid.maxLength; simp only [em1Offset]; omega) (by decide)

theorem Context.statusEm2 {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    (localRegion g statusOffset 4).Disjoint ⟨byteAddr g.em2, g.length⟩ := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inl (by decide : statusOffset + 4 ≤ em2Offset)) (by decide)
    (by have := h.valid.maxLength; simp only [em2Offset]; omega)

theorem afterPub_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa afterPub s fun t => Context g bs t ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps clobbers s t ∧ Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax)
        (checkedPublicRecovery g s) := by
  unfold afterPub
  refine WP.seq (WP.mono (save_ok h) ?_)
  rintro a ⟨ha, saved, Fa, Ka⟩
  refine WP.seq (WP.mono (encArgs_ok ha) ?_)
  rintro b ⟨hb, Mb, Kb, dst, len, hash, count, src⟩
  refine WP.seq (WP.mono (encoding_ok hb dst len hash src count) ?_)
  rintro c ⟨hc, Fc, Kc, enc⟩
  refine WP.mono (tail_ok hc enc) ?_
  rintro t ⟨ht, Ft, Kt, out⟩
  have first : Spec.Rsa.bytesAt a.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length :=
    VG.Proof.Rsa.rsa_bytes_frame Fa (by have := h.valid.maxLength; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.em1Status)
  have next : Spec.Rsa.bytesAt c.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt b.mem (byteAddr g.em1) g.length :=
    VG.Proof.Rsa.rsa_bytes_frame Fc (by have := h.valid.maxLength; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.encodingsSeparate)
  have digestFirst : digestBytes g a = digestBytes g s :=
    VG.Proof.Rsa.rsa_bytes_frame Fa (by have := h.valid.outputBound; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.em1Status.sub_left h.valid.digestSub)
  have digestNext : digestBytes g c = digestBytes g b :=
    VG.Proof.Rsa.rsa_bytes_frame Fc (by have := h.valid.outputBound; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.encodingsSeparate.sub_left h.valid.digestSub)
  have status : savedStatus g c = savedStatus g b :=
    Fc.readW (r := localRegion g statusOffset 4) (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.statusEm2) (by decide)
  have statusS : savedStatus g c = s.gpr .eax := by
    rw [status, savedStatus, Mb]
    exact saved
  have bytesS : Spec.Rsa.bytesAt c.mem (byteAddr g.em1) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length := by rw [next, Mb, first]
  have digestS : digestBytes g c = digestBytes g s := by
    rw [digestNext, digestBytes, Mb]
    exact digestFirst
  have option : checkedRecovery g c = checkedPublicRecovery g s := by
    unfold checkedRecovery checkedPublicRecovery
    rw [digestS, bytesS, statusS]
    rfl
  refine ⟨ht, ?_, (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans
    ((Kc.mono (by decide)).trans Kt)), by rw [← option]; exact out⟩
  have fa : Frame (bodyWrites g) s.mem a.mem := Fa.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], localSub (by decide)⟩)
  have fc : Frame (bodyWrites g) a.mem c.mem := by
    rw [Mb] at Fc
    apply Fc.sub
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], h.em2Sub⟩
  exact fa.trans (fc.trans Ft)

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def recovered (g : Geometry) (bs : Fin 4 → List Byte) : Option (List Byte) :=
  (Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat).bind fun h => Spec.RsaPkcs1Sig.recover (bs 0) (bs 1) h (bs 2)

theorem digestBytes_drop {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    digestBytes g s = (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length).drop (g.length - g.outputLength) := by
  unfold digestBytes
  rw [h.valid.digestAddr, ← VG.Proof.RsaPkcs1Sig.bytesAt_drop]
  rw [Nat.sub_add_cancel h.valid.outputFits]

theorem checkedPublicRecovery_eq {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (siglen : g.signatureLength = g.length)
    (post : Spec.Rsa.written s.mem (byteAddr g.em1) g.length (s.gpr .eax)
      (Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 2))) :
    checkedPublicRecovery g s = recovered g bs := by
  obtain ⟨hash, id, outlen⟩ := h.valid.hashValid
  have nlen : (bs 0).length = g.length := (h.sources 0).length
  have slen : (bs 2).length = g.length := (h.sources 2).length.trans siglen
  unfold recovered
  rw [id, Option.bind_some, VG.Proof.RsaPkcs1Sig.recover_eq_recoverEnc]
  unfold VG.Proof.RsaPkcs1Sig.recoverEnc
  rw [nlen, ite_eq_left slen]
  cases op : Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 2) with
  | none =>
    rw [op] at post
    unfold checkedPublicRecovery
    cases encodeId g.hash (digestBytes g s) g.length with
    | none => rfl
    | some expected =>
      dsimp only
      rw [post.1]
      simp only [show ((0 : BitVec 32).getLsbD 0) = false from rfl, Bool.and_false, Bool.false_eq_true, ite_false]
  | some em =>
    rw [op] at post
    have digest : digestBytes g s = em.drop (g.length - hash.len) := by
      rw [digestBytes_drop h, post.2, outlen]
    unfold checkedPublicRecovery encodeId
    rw [id, Option.bind_some, digest, post.1, post.2]
    simp only [show ((1 : BitVec 32).getLsbD 0) = true from rfl, Bool.and_true]
    cases encoding : Spec.RsaPkcs1Sig.encode hash (em.drop (g.length - hash.len)) g.length with
    | none => simp
    | some expected =>
      by_cases eq : em = expected
      · subst expected
        simp only [decide_true, ite_true]
      · simp only [decide_eq_false eq, Bool.false_eq_true, ite_false,
          Option.some.injEq, Ne.symm eq]

end VG.Proof.RsaPkcs1Sig.X86.Rcv
