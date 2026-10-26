module
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRelease
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverTail
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigestArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset

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
