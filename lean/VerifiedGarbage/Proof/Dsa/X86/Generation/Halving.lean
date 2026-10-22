module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingInit
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingLoop

/-! Native factor-of-two extraction reuses RSA's reviewed splitting arithmetic. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving {L : Lay} {s : State} {base : Addr} {bytes len count value : Nat}
    (h : RtWs L s base bytes len count) (arrays : 2 ≤ count)
    (current : num s.mem base (kw len) 0 = value) (positive : 0 < value)
    (bits : 32 * kw len ≤ 16384) :
    WP isa (Impl.Dsa.X86.Generation.halving L) s fun t =>
      HalvingState L base bytes len count (Spec.Rsa.splitTwos value).2 (Spec.Rsa.splitTwos value).1 0 t ∧
      Keep base (kw len) [0, 1] [28, 20, 56] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fit : value < 2 ^ (32 * kw len) := by rw [← current]; exact val32_lt _ _ _ _
  have nonempty : 0 < 32 * kw len := by have := h.ws.wpos; omega
  unfold Impl.Dsa.X86.Generation.halving
  refine WP.seq (WP.mono (halving_init h (by omega) current) ?_)
  rintro u ⟨hu, F, K⟩
  have I : HalvingLoopInv L base bytes len count value (32 * kw len) 0 s u :=
    ⟨hu, F.mono (by simp) (by simp), K.mono (by decide)⟩
  refine WP.mono (halving_loop I arrays nonempty bits) ?_
  intro t J
  have done := VG.Proof.Rsa.halve_done positive fit
  have state := J.state
  rw [halvingValues, done, Nat.sub_self] at state
  exact ⟨state, J.frame, J.keeps⟩

end VG.Proof.Dsa.X86.Generation
