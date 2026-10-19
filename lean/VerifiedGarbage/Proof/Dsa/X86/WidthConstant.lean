module

public import VerifiedGarbage.Impl.Dsa.X86.Width
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.WordConst

/-! # Comparing a loaded DSA component with a fixed threshold -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem lessThanConstant_ok {s : State} {base : Addr} {size n a tmp value : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hv : value < 2 ^ (64 * n)) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (lessThanConstant n a tmp value) s fun t =>
      t.gpr .eax = mask32 (wordsVal s.mem base a n < value) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold lessThanConstant
  refine WP.seq (WP.mono (setConstW_ok hs (k := 2 * n) (o := tmp) (x := value) (by omega) (by omega)
    (by rw [show 32 * (2 * n) = 64 * n by omega]; exact hv))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.mono (VG.Proof.Dsa.X86.lessThan_ok n (hs.of_keeps Ku (by decide)) hn ha ht)
    fun t ⟨Vt, Kt, Mt⟩ => ?_
  rw [show 4 * (2 * n) = 8 * n by omega] at Ou
  refine ⟨?_, (Ku.mono (by decide)).trans Kt, Mt ▸ Ou⟩
  rw [Vt, wordsVal_eq_val32 u.mem base tmp, Vu, Ou.wordsVal hsep (by have := hs.nowrap; omega)]

theorem mask_not (p : Prop) [Decidable p] : mask32 p ^^^ BitVec.allOnes 32 = mask32 (¬ p) := by
  by_cases hp : p <;> simp only [mask32, hp, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> decide

end VG.Proof.Dsa.X86
