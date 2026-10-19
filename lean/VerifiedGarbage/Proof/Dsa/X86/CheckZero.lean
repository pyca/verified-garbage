module
public import VerifiedGarbage.Proof.Dsa.X86.Checks

import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Zero and nonzero checks with accumulated acceptance masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem checkZero_ok {s : State} {base : Addr} {size n a flag : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (hf : flag + 4 ≤ size)
    (wantNonzero : Bool) :
    WP isa (checkZero n a flag wantNonzero) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (if wantNonzero then wordsVal s.mem base a n ≠ 0 else wordsVal s.mem base a n = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkZero
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.nonzero_ok n hs hn ha) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  cases wantNonzero with
  | true =>
    simp only [ite_true, List.nil_append]
    refine WP.mono (andFlag_ok flag (hs.of_keeps Ku (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
    exact ⟨by rw [Vt, Vu]; simp only [flagW, Mu], (Ku.mono (by decide)).widen Kt, Mu ▸ Ot⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.singleton_append]
    refine wp_logicS (.inr rfl) rfl fun v uv => ?_
    have Kv := Ku.widen uv.keeps
    refine WP.mono (andFlag_ok flag (hs.of_keeps Kv (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
    refine ⟨?_, (Kv.mono (by decide)).widen Kt, ?_⟩
    · rw [Vt, uv.gpr, Vu]
      simp only [reduceCtorEq, ite_false, mask_not, ne_eq, not_not, flagW, uv.mem, Mu]
    · rw [uv.mem, Mu] at Ot
      exact Ot

end VG.Proof.Dsa.X86
