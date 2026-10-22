module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
public import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! # Reuse RSA's quotient and remainder while retaining the shaped candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num arr S slot)
open VG.Impl.Rsa.X86.KeyRt (Lay sCy sQb)

structure ReductionState (L : Lay) (base : Addr) (bytes len count x q : Nat) (s : State) : Prop where
  workspace : RtWs L s base bytes len count
  quotient : num s.mem base (kw len) 0 = x / (2 * q)
  remainder : num s.mem base (kw len) 1 = x % (2 * q)
  saved : num s.mem base (kw len) 4 = x
  one : slot s.mem base Impl.Dsa.X86.Generation.reductionOne = 1
  bound : x < 2 ^ (32 * kw len)

theorem reduction_division {L : Lay} {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : RtWs L s base bytes len count) (hc : 6 ≤ count) (positive : 0 < q)
    (candidate : num s.mem base (kw len) 0 = x) (divisor : num s.mem base (kw len) 2 = 2 * q)
    (top : w32 s.mem base (arr (kw len) 2 + 4 * kw len) = 0)
    (one : slot s.mem base Impl.Dsa.X86.Generation.reductionOne = 1) :
    WP isa (.seq (Impl.Rsa.X86.KeyRt.copy L 4 0) (Impl.Rsa.X86.KeyRt.div L 0 1 2 3)) s fun t =>
      ReductionState L base bytes len count x q t ∧
      Keep base (kw len) [0, 1, 3, 4] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have bound : x < 2 ^ (32 * kw len) := by
    rw [← candidate]
    exact val32_lt _ _ _ _
  refine WP.seq (WP.mono (copy_ok h (o := 4) (a := 0) (by omega) (by omega) (by decide)) ?_)
  rintro u ⟨hu, copyFrame, saved, copyK, _⟩
  have candidateU := (copyFrame.num (j := 0) (by simp) (by simp) (h.ws.fit64 (by omega))).trans candidate
  have divisorU := (copyFrame.num (j := 2) (by simp) (by simp) (h.ws.fit64 (by omega))).trans divisor
  have topU := (copyFrame.word (j := 2) (i := kw len) (by simp only [S]; omega)
    (by simp) (by simp) (h.ws.fit64 (by omega))).trans top
  have savedU := saved.trans candidate
  have oneU := (copyFrame.slot (by decide : Impl.Dsa.X86.Generation.reductionOne + 4 ≤ Impl.Rsa.X86.Keys.hdr)
    (by simp)).trans one
  refine WP.mono (div_ok hu (q := 0) (r := 1) (d := 2) (t := 3) (by omega) (by omega) (by omega)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) topU) ?_
  rintro t ⟨ht, frame, K, quotientRem⟩
  obtain ⟨quotient, remainder⟩ := quotientRem (by rw [divisorU]; omega)
  rw [candidateU, divisorU] at quotient remainder
  have savedT := (frame.num (j := 4) (by simp) (by simp; decide) (h.ws.fit64 (by omega))).trans savedU
  have oneT := (frame.slot (by decide : Impl.Dsa.X86.Generation.reductionOne + 4 ≤ Impl.Rsa.X86.Keys.hdr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> decide)).trans oneU
  exact ⟨⟨ht, quotient, remainder, savedT, oneT, bound⟩, copyFrame.join frame,
    (copyK.mono (by decide)).trans K⟩

end VG.Proof.Dsa.X86.Generation
