module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocal
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Compare

/-! # Compare the public RSA result against the separately encoded digest -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (lea em1Offset em2Offset incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover (cmpArgs)

theorem cmpArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block cmpArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi, .edi, .ecx] s t ∧ t.gpr .esi = g.em1 ∧ t.gpr .edi = g.em2 ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length := by
  unfold cmpArgs lea incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_movS rfl fun c C _ => ?_
  refine wp_addS rfl fun d D _ => ?_
  have K : Keeps [.esi, .edi, .ecx] s d := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide))))
  have M : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have hd := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 3 < 13)) fun t T => WP.block_nil ?_
  have kt := K.trans (T.keeps.mono (by decide))
  have mt := T.mem.trans M
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_, ?_, ?_⟩
  · rw [T.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [T.other .edi (by decide), D.gpr, C.gpr, B.other .esp (by decide), A.other .esp (by decide), h.sp]
    rfl
  · rw [T.gpr, hd.argumentValue (by decide : 3 < 13)]
    rfl

theorem compare_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s)
    (src : s.gpr .esi = g.em1) (dst : s.gpr .edi = g.em2) (cnt : s.gpr .ecx = BitVec.ofNat 32 g.length) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.compare s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s t ∧
      (t.gpr .ebp = 0 ↔ Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length =
        Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length) := by
  have em1Fit := h.valid.encodingFit (d := em1Offset)
    (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)
  have read1 : InRegions (s.rd ++ s.wr) (byteAddr g.em1) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em1Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have read2 : InRegions (s.rd ++ s.wr) (byteAddr g.em2) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em2Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.compare_ok s
    (by have := h.valid.minLength; omega) (by have := h.valid.maxLength; omega)
    em1Fit h.em2Fit read1 read2 src dst cnt) ?_
  rintro t ⟨eq, M, K⟩
  exact ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, eq⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
