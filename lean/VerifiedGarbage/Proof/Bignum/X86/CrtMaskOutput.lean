module

public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Rejected RSA representatives produce zero without a secret branch -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem maskOutput_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes)
    (accept : Bool) (mask : s.gpr .ecx = if accept then BitVec.allOnes 32 else 0) :
    WP isa (maskOutput n) s fun t =>
      wordsVal t.mem base (slot n resultSlot) n =
        (if accept then wordsVal s.mem base (slot n resultSlot) n else 0) ∧
      Outs base [(slot n 5, 8 * n), (slot n resultSlot, 8 * n)] s.mem t.mem ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b7 := slot_bound (n := n) (i := resultSlot) (by decide)
  have sep := slot_le (n := n) (i := 5) (j := resultSlot) (by decide)
  simp only [stride] at b5 b7 sep
  unfold maskOutput
  refine WP.seq (WP.mono (zerosW_ok hs (k := 2 * n) (by omega) (by omega))
    fun u ⟨O, Z, K⟩ => ?_)
  have hsu := hs.of_keeps K (by decide)
  refine WP.mono (selectsW_ok hsu accept (by rw [K.1 .ecx (by decide), mask])
    (by omega) (by omega) (by omega) (by omega) (.inr (.inr (by omega))) (.inl rfl))
    fun t ⟨Ot, V, Kt⟩ => ?_
  refine ⟨?_, ?_, (K.mono (by decide)).trans Kt⟩
  · rw [wordsVal_eq_val32, V]
    cases accept
    · exact Z
    · change val32 u.mem base (slot n resultSlot) (2 * n) = wordsVal s.mem base (slot n resultSlot) n
      rw [O.val32 (.inr (by omega)) (by have := hs.nowrap; omega), ← wordsVal_eq_val32]
  · have O' : Outside base (slot n 5) (8 * n) s.mem u.mem := by
      simpa only [show 4 * (2 * n) = 8 * n by omega] using O
    have Ot' : Outside base (slot n resultSlot) (8 * n) u.mem t.mem := by
      simpa only [show 4 * (2 * n) = 8 * n by omega] using Ot
    exact (Outs.of_outside O' (by simp)).trans (Outs.of_outside Ot' (by simp))

end VG.Proof.Bignum.X86.Crt
