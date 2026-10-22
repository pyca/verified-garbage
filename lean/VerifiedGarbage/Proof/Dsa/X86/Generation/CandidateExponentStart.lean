module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word

/-! Save a candidate and form its even predecessor using the existing low-bit clear. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem candidate_exponent_start {L : Lay} {s : State} {base : Addr} {bytes len count candidate : Nat}
    (h : RtWs L s base bytes len count) (arrays : 3 ≤ count)
    (current : num s.mem base (kw len) 0 = candidate) :
    WP isa (Impl.Dsa.X86.Generation.candidateExponentStart L) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0, 2] [] s.mem t.mem ∧
      num t.mem base (kw len) 0 = 2 * (candidate / 2) ∧ num t.mem base (kw len) 2 = candidate ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.candidateExponentStart
  refine WP.seq (WP.mono (copy_ok h (o := 2) (a := 0) (by omega) (by omega) (by decide)) ?_)
  rintro a ⟨ha, F, saved, K, _⟩
  rw [current] at saved
  have ca := (F.num (j := 0) (by simp) (by simp) (h.ws.fit64 (by omega))).trans current
  refine WP.mono (clrLow_ok ha (j := 0) (by omega)) ?_
  rintro t ⟨ht, F', even, K', _⟩
  rw [ca] at even
  exact ⟨ht, F.join F', even,
    (F'.num (j := 2) (by simp) (by simp) (h.ws.fit64 (by omega))).trans saved,
    K.trans (K'.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
