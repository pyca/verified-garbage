module

public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Accumulating validation results into the DSA acceptance mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem accumulateEqual_ok {s : State} {base : Addr} {size n a b flag : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (hb : b + 8 * n ≤ size)
    (hf : flag + 4 ≤ size) :
    WP isa (.seq (equal n a b) (.block (andFlag flag))) s fun t =>
      flagW base flag t = flagW base flag s &&& mask32 (wordsVal s.mem base a n = wordsVal s.mem base b n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ Outside base flag 4 s.mem t.mem := by
  refine WP.seq (WP.mono (equal_ok n hs hn ha hb) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  refine WP.mono (andFlag_ok flag (hs.of_keeps Ku (by decide)) hf) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, Ku.widen Kt, Mu ▸ Ot⟩
  rw [Vt, Vu]
  simp only [flagW, Mu]

end VG.Proof.Dsa.X86
