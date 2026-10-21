module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassWord
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A single masked pass halves or retains the complete native exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * n ≤ size)
    (sep : src = out ∨ src + 4 * (n + 1) ≤ out ∨ out + 4 * n ≤ src)
    (top : w32 s.mem base (src + 4 * n) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (code n src out) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if choice then val32 s.mem base src n / 2 else val32 s.mem base src n) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  let P (j : Nat) (t : State) : Prop :=
    Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base out (4 * j) s.mem t.mem ∧
    ∀ i < j, w32 t.mem base (out + 4 * i) =
      if choice then w32 s.mem base (src + 4 * i) / 2 +
        2 ^ 31 * (w32 s.mem base (src + 4 * i + 4) % 2) else w32 s.mem base (src + 4 * i)
  refine wordLoop_ok P positive (by have := scratch.size_lt; omega)
    (fun j t u ⟨K, O, V⟩ ⟨M, rd, wr, regs⟩ =>
      ⟨⟨fun r hr => (regs r (by simp_all) (by simp_all)).trans (K.1 r hr), rd.trans K.2.1, wr.trans K.2.2⟩,
        M ▸ O, M ▸ V⟩)
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · intro j hj t ⟨K, O, V⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine WP.mono (step_ok (choice := choice) St pointer (by omega) (by omega) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Ku⟩ => ?_
    have sameLo : w32 t.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O.w32 (by rcases sep with h | h | h <;> omega) (by have := scratch.nowrap; omega)
    have sameHi : w32 t.mem base (src + 4 * j + 4) = w32 s.mem base (src + 4 * j + 4) :=
      O.w32 (by rcases sep with h | h | h <;> omega) (by have := scratch.nowrap; omega)
    refine ⟨⟨K.widen Ku, (O.mono (by omega) (by omega)).trans (Ou.mono (by omega) (by omega)), ?_⟩,
      Ku.1 .ebp (by decide), Ku.1 .edi (by decide)⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega) (by have := scratch.nowrap; omega)]
      exact V i before
    · rw [value, sameLo, sameHi]
  · intro t ⟨K, O, V⟩
    refine ⟨O, ?_, K⟩
    cases choice
    · exact val32_congr_at s.mem t.mem base n src out V
    · apply val32_halve_at s.mem t.mem base n src out
      intro i hi
      rw [V i hi, show src + 4 * i + 4 = src + 4 * (i + 1) by omega]
      by_cases last : i + 1 = n
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

end VG.Proof.RsaKeyGen.X86.HalfPass
