module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ReduceSubtract
public import VerifiedGarbage.Proof.Dsa.X86.Generation.DoubleArray
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Exact native p-candidate and generator exponent from the shared reduction formula -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num arr slot)
open VG.Impl.Rsa.X86.KeyRt (Lay sCy sQb)

theorem reduction_tail {L : Lay} {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : ReductionState L base bytes len count x q s) (hc : 6 ≤ count) (positive : 0 < q) :
    WP isa (.seq (Impl.Rsa.X86.KeyRt.sub3 L 5 4 1)
      (.seq (.block (Impl.Rsa.X86.KeyRt.addLow L 5 Impl.Dsa.X86.Generation.reductionOne))
        (Impl.Dsa.X86.Generation.doubleArray L 0))) s fun t =>
      RtWs L t base bytes len count ∧ num t.mem base (kw len) 5 = x + 1 - x % (2 * q) ∧
      num t.mem base (kw len) 0 = 2 * (x / (2 * q)) ∧
      Keep base (kw len) [0, 5] [] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (reduction_subtract h hc) ?_)
  rintro u ⟨hu, f₁, K₁⟩
  refine WP.seq (WP.mono (reduction_increment hu hc) ?_)
  rintro v ⟨hv, f₂, candidate, quotient, K₂⟩
  have bound : 2 * num v.mem base (kw len) 0 < 2 ^ (32 * kw len) := by
    rw [quotient]
    have smaller : 2 * (x / (2 * q)) ≤ 2 * q * (x / (2 * q)) :=
      Nat.mul_le_mul_right _ (by omega)
    have le := Nat.mul_div_le x (2 * q)
    have xBound := h.bound
    omega
  refine WP.mono (double_array hv (j := 0) (by omega) bound) ?_
  rintro t ⟨ht, f₃, exponent, K₃⟩
  rw [quotient] at exponent
  exact ⟨ht, (f₃.num (j := 5) (by simp) (by simp) (h.workspace.ws.fit64 (by omega))).trans candidate,
    exponent, (f₁.trans f₂).join (js := [0, 5]) (ds := []) f₃, (K₁.trans (K₂.mono (by decide))).trans K₃⟩

theorem reduce_candidate {L : Lay} {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : RtWs L s base bytes len count) (hc : 6 ≤ count) (positive : 0 < q)
    (candidate : num s.mem base (kw len) 0 = x) (divisor : num s.mem base (kw len) 2 = 2 * q)
    (top : w32 s.mem base (arr (kw len) 2 + 4 * kw len) = 0)
    (one : slot s.mem base Impl.Dsa.X86.Generation.reductionOne = 1) :
    WP isa (Impl.Dsa.X86.Generation.reduceCandidate L) s fun t =>
      RtWs L t base bytes len count ∧ num t.mem base (kw len) 5 = x + 1 - x % (2 * q) ∧
      num t.mem base (kw len) 0 = 2 * (x / (2 * q)) ∧
      Keep base (kw len) [0, 1, 3, 4, 5] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold Impl.Dsa.X86.Generation.reduceCandidate
  apply WP.assoc
  refine WP.seq (WP.mono (reduction_division h hc positive candidate divisor top one) ?_)
  rintro u ⟨hu, F, K⟩
  refine WP.mono (reduction_tail hu hc positive) ?_
  rintro t ⟨ht, p, e, F', K'⟩
  exact ⟨ht, p, e, F.join F', K.trans (K'.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
