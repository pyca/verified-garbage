module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeSized
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeDispatch
public import VerifiedGarbage.Proof.Bignum.X86.PublicControls
public import VerifiedGarbage.Proof.Bignum.ModulusCheckMath

/-! # Dispatch validated moduli to their precomputation width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

def PrecomputePost (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (mem : Mem) (t : State) : Prop :=
  (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len) with
  | some ws => t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (byteAddr (args 0)) (2 * Spec.Rsa.modulusWords len) = ws
  | none => t.gpr .eax = 0 ∧ Spec.Rsa.wordsAt t.mem (byteAddr (args 0)) (2 * Spec.Rsa.modulusWords len) =
      List.replicate (2 * Spec.Rsa.modulusWords len) 0) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), 16 * Spec.Rsa.modulusWords len⟩] mem t.mem

theorem precomputeValid_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PrecomputeFn.valid s fun t => PrecomputePost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
  unfold PrecomputeFn.valid
  refine WP.seq (WP.mono (widthArgs_ok h.upper
    (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc)) fun u ⟨W, M, K⟩ => ?_)
  refine precomputeDispatch_ok PublicFn.widths (publicWidths_member h.lower h.upper) ?_ W ?_
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    have := List.mem_range.mp hi
    omega
  · intro v Kv Mv
    have Ks : Keeps [.eax] s v := K.trans (Kv.mono (by decide))
    have Ms : v.mem = s.mem := Mv.trans M
    have hv := h.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
    refine WP.mono (precomputeSized_ok hv.scratch dims.1 dims.2.1 h.space
      (by have := h.lower; omega) dims.2.2 (hv.stack 2 (by decide))
      (by rw [← h.nLen]; exact hv.stack 3 (by decide)) (hv.stack 0 (by decide)) h.nFit hv.nRead h.nApart
      h.outFit hv.outWrite h.outApart (by rw [Ms]; exact facts.2.1) (by rw [Ms]; exact facts.1))
      fun t ⟨B, V, F, T⟩ => ?_
    refine ⟨⟨?_, ?_⟩, (Ks.mono (by decide)).trans T⟩
    · simp only [Spec.Rsa.publicPrecompute, bytesAt_length, valid, ite_true]
      exact ⟨B, by simpa only [Ms] using V⟩
    · simpa only [Ms] using F

end VG.Proof.Bignum.X86.PublicContext
