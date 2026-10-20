module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedImport
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Load the packed key while retaining the call header -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedKey_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) :
    WP isa (PrecomputedFn.importKey (Spec.Rsa.modulusWords len)) s fun t =>
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 0) (Spec.Rsa.modulusWords len) =
        wv s.mem (byteAddr (args 2)) 0 (Spec.Rsa.modulusWords len) ∧
      wordsVal t.mem base (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 5) (Spec.Rsa.modulusWords len) =
        wv s.mem (byteAddr (args 2)) (8 * Spec.Rsa.modulusWords len) (Spec.Rsa.modulusWords len) ∧
      Outside base 256 (bytes - 256) s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have sz := h.space
  have nw := h.scratch.nowrap
  have b0 := slot_bound (n := Spec.Rsa.modulusWords len) (i := 0) (by decide)
  have b5 := slot_bound (n := Spec.Rsa.modulusWords len) (i := 5) (by decide)
  have d0 := slot_header (Spec.Rsa.modulusWords len) 0
  have d5 := slot_header (Spec.Rsa.modulusWords len) 5
  simp only [stride] at b0 b5
  unfold PrecomputedFn.importKey
  refine WP.seq (wp_movS (h.stack 2 (by decide)).readSrc fun u U _ => WP.block_nil ?_)
  refine WP.mono (precomputedImport_ok (h.scratch.of_keeps U.keeps (by decide)) h.dimensions.1 h.space
    h.preFit (by rw [U.rd, U.wr]; exact h.preRead) h.preApart U.gpr) fun t ⟨N, R, F, K⟩ => ?_
  refine ⟨by simpa only [U.mem] using N, by simpa only [U.mem] using R, ?_, (U.keeps.mono (by decide)).trans K⟩
  rw [U.mem] at F
  apply frame_outside (F.sub ?_) (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩

end VG.Proof.Bignum.X86.PublicContext
