module

public import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Framework.Omega

/-! # Modular subtraction for a runtime modulus on x86, by loops

`subW_ok`: `m - [b]` into the temporary area, then `add_ok` of `[a]` and it. -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `[o] = [a] - [b] mod m`, for `[a]` and `[b]` below `m` and apart from the temporary area. -/
theorem subW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hat : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a) (hbt : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (subW M acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hb := hL.b_le; have ha := hL.a_le
  have hmo := hM.mo; have htmp := hM.tmp; have hn0 := hM.n0; have hsep := hM.sep
  unfold subW
  rw [hNw]
  refine WP.seq (WP.mono (chainSubW_ok hs (o := M.tmp) (a := M.mo) (b := b) (k := N) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₁ ⟨O₁, ⟨c, _, V₁⟩, K₁⟩ => ?_)
  have hm : val32 s.mem base M.mo N = m := by rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hbv : val32 s.mem base b N = wordsVal s.mem base b M.n := by rw [hN2, ← wordsVal_eq_val32]
  have hlt := val32_lt s₁.mem base M.tmp N
  have hc : c = false := by
    cases c
    · rfl
    · simp only [Bool.toNat_true, Nat.mul_one] at V₁; omega
  subst hc
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at V₁
  have T₁ : wordsVal s₁.mem base M.tmp M.n = m - wordsVal s.mem base b M.n := by
    rw [wordsVal_eq_val32, ← hN2]; omega
  have A₁ : wordsVal s₁.mem base a M.n = wordsVal s.mem base a M.n :=
    O₁.wordsVal (by omega) (by omega)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have hM₁ : Modulus M size m s₁.mem base :=
    ⟨hn0, hmo, htmp, hsep, by rw [O₁.wordsVal (by omega) (by omega)]; exact hM.val⟩
  have hL₁ : OpLay M size acc o a M.tmp :=
    ⟨hL.acc_le, hL.o_le, hL.a_le, htmp, hL.acc_o, hL.acc_a, hL.acc_tmp, hL.acc_mo, hL.acc_tmp, hL.o_tmp⟩
  refine WP.mono (add_ok hs₁ hM₁ hL₁ (by rw [A₁, T₁]; omega)) fun u ⟨K, V, _, _⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => (K.gpr r hr).trans (K₁.1 r fun h => hr (by simp_all [clob])),
      K.rd.trans K₁.2.1, K.wr.trans K₁.2.2, ?_⟩
    rw [show 4 * N = 8 * M.n by omega] at O₁
    exact (Outs.of_outside O₁ (by simp)).trans K.mem
  · rw [V, A₁, T₁]
    congr 1
    omega

end VG.Proof.Mont.X86.Dynamic
