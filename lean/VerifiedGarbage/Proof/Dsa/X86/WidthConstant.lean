module

public import VerifiedGarbage.Impl.Dsa.X86.Width
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-! # Comparing a loaded DSA component with a fixed threshold -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem lessThanConstant_ok {s : State} {base : Addr} {size n a tmp value : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size)
    (hv : value < 2 ^ (64 * n)) (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (.block (lessThanConstant n a tmp value)) s fun t =>
      t.gpr .eax = mask32 (wordsVal s.mem base a n < value) ∧
      Keeps [.eax, .edx] s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold lessThanConstant
  refine WP.block_append (WP.mono (VG.Proof.Weierstrass.X86.setConst_ok hs ht hv)
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.mono (VG.Proof.Dsa.X86.lessThan_ok n (hs.of_keeps Ku (by decide)) hn ha ht)
    fun t ⟨Vt, Kt, Mt⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).trans Kt, Mt ▸ Ou⟩
  rw [Vt, Vu, Ou.wordsVal hsep (by have := hs.nowrap; omega)]

theorem mask_not (p : Prop) [Decidable p] : mask32 p ^^^ BitVec.allOnes 32 = mask32 (¬ p) := by
  by_cases hp : p <;> simp only [mask32, hp, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> decide

end VG.Proof.Dsa.X86
