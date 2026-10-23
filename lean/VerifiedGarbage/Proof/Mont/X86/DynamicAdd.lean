module

public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Modular addition for a runtime modulus on x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (addW M acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m ∧
      Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, 4 * (words M + 1))] s.mem s'.mem ∧
      s'.gpr .ebx = s.gpr .ebx := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le
  have := hM.mo; have := hM.tmp; have := hM.n0; have := hM.sep
  have l₁ := hL.acc_a; have l₂ := hL.acc_b; have l₃ := hL.acc_mo; have l₄ := hL.acc_tmp
  have l₅ := hL.acc_o; have l₆ := hL.o_tmp
  unfold addW
  rw [hNw]
  refine WP.seq (WP.mono (chainAddW_ok hs (o := acc) (a := a) (b := b) (k := N) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (wp_movS rfl fun s₂ u₂ _ => wp_subS rfl fun s₃ u₃ _ => ?_)
  have k₃ : Keeps [.eax, .ecx, .edx, .ebp] s s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine wp_storeS (hs₃.ea (d := acc + 4 * N) (by omega_arith))
    (hs₃.write (d := acc + 4 * N) (n := 4) (by omega_arith)) fun s₄ m₄ => WP.block_nil ?_
  have hs₄ := hs₃.of_keeps (m₄.keeps []) (by decide)
  have O₄ : Outside base acc (4 * N + 4) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, u₂.mem]
    exact (O₁.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have hsum : val32 s₄.mem base acc (N + 1) =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by
    rw [val32_succ, m₄.mem, u₃.mem, u₂.mem, (writeW32_outside _ _ _ (by omega_arith)).val32 (by omega_arith) (by omega_arith),
      w32_write_self, u₃.gpr, u₂.gpr, u₂.other _ (by decide), hc, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, ← V₁]
    have : ((0 : BitVec 32) - cmask c).toNat = c.toNat := by cases c <;> rfl
    rw [this]
  have hm₄ : val32 s₄.mem base M.mo N = m := by
    rw [O₄.val32 (by omega_arith) (by omega_arith), hN2, ← wordsVal_eq_val32]; exact hM.val
  refine WP.mono (csubW_ok hs₄ hNw (src := acc) (o := o) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hm₄
        (by rw [hsum]; exact hAB))
    fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_, ?_⟩
  · refine OpKeep.of (((k₃.mono (rs' := clob) (by decide)).widen (m₄.keeps [])).widen K) (by decide) ?_
    have O₄' : Outside base acc (accLen M) s.mem s₄.mem := O₄.mono (Nat.le_refl _) (by omega_arith)
    refine (Outs.of_outside O₄' (by simp)).trans ?_
    rw [show 4 * N = 8 * M.n by omega_arith] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, V, hsum]
  · refine (Outs.of_outside (O₄.mono (o' := acc) (n' := 4 * (words M + 1)) (Nat.le_refl _) (by rw [hNw]; omega_arith))
      (by simp [hNw])).trans ?_
    rw [show 4 * N = 8 * M.n by omega_arith] at O
    exact O.mono (by simp)
  · rw [K.1 _ (by decide), m₄.gpr, k₃.1 _ (by decide)]

end VG.Proof.Mont.X86.Dynamic
