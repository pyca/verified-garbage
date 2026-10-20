module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundTests
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundMinus

/-! # Complete a prepared exponentiation with the specified Miller–Rabin result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def roundFinishWrites (n : Nat) : List (Nat × Nat) := roundWrites n ++ [(slot n 8, 8 * n)]

theorem roundFinish_ok {base : Addr} {n m size k : Nat} {s : State} (C : Context n m base size s)
    (width : n ≤ 48) (room : roundStatus + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m)
    (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (roundFinish n) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (roundAnswer m k (wordsVal s.mem base (slot n 6) n)).toNat ∧
      Outs base (roundFinishWrites n) s.mem t.mem ∧ Keeps clob s t := by
  unfold roundFinish
  refine WP.seq (WP.mono (roundMinusOne_ok C one) fun a ⟨Ca, minus, Oa, Ka⟩ => ?_)
  have val (j : Nat) (hj : j < 8) : wordsVal a.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    have sep := slot_sep (n := n) (i := j) (j := 8) (by omega)
    have before := slot_bound (n := n) (by omega : j < 9)
    have upto : slot n j ≤ slot n 8 := by unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have fit := C.size_le
    have nw := C.scr.nowrap
    simp only [stride] at sep before
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact Oa.val32 (by omega) (by omega)
  have counta : a.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k := by
    have same : a.mem.readW (off base roundCount) 32 = s.mem.readW (off base roundCount) 32 := by
      apply BitVec.eq_of_toNat_eq
      exact Oa.w32 (by simp only [slot, stride, roundCount]; omega) (by decide)
    exact same.trans count
  have Ra : RoundReady base n m size a := ⟨Ca, width, room,
    (val 3 (by decide)).trans one, (val 4 (by decide)).trans r2, minus⟩
  refine WP.mono (roundTests_ok Ra bound counta) fun t ⟨value, Ot, Kt⟩ => ?_
  refine ⟨by rw [value, val 6 (by decide)], ?_, (Ka.mono (by decide)).trans Kt⟩
  exact (Outs.of_outside Oa (by simp [roundFinishWrites])).trans
    (Ot.mono (by intro r hr; exact List.mem_append_left _ hr))
end VG.Proof.Dsa.X86.Generation
