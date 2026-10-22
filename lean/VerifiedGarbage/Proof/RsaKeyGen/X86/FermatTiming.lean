module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Coprimality with 65537 uses only public frame and candidate addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FermatExponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.FermatExponent VG.Proof.RsaKeyGen.X86.Sieve

theorem init_control {g : Geometry} {s : State} (S : ReadControl g 0 s) :
    WP isa (.block init) s (ReadControl g 0) := by
  unfold init
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .esi, .ebp] s t := ((A.keeps.mono (by decide)).widen B.keeps).widen T.keeps
  exact ⟨S.stack.keep K (by decide),
    fun i index => by rw [K.2.1, K.2.2]; exact S.candidateRead i index,
    by rw [T.mem, B.mem, A.mem]; exact S.ending,
    (K.1 .edi (by decide)).trans S.pointer⟩

theorem init_trace {g : Geometry} :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (.block init)
      (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := ((checkedBlockInvariant (τ := τr [.esp, .edi]) (code := init) rfl rfl)
    _ _ _ _ _ _ (S.agree T) E G).1
  exact ⟨trace, wp_result (init_control S) E, wp_result (init_control T) G⟩

theorem code_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (code 4)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq init_trace (RelCT.seq (divisor_trace v) (checkedBlockInvariant rfl rfl))

theorem code_trace_bounded {g : Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 64)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (code 4)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq init_trace (RelCT.seq (divisor_trace_bounded positive (by omega) candidateFit)
    (checkedBlockInvariant rfl rfl))

end VG.Proof.RsaKeyGen.X86.FermatExponent
