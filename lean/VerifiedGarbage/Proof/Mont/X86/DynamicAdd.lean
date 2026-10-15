module

public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Csub

/-! # Modular addition for a runtime modulus on x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M acc o a b)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le
  have := hM.mo; have := hM.tmp; have := hM.n0
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega_using [hN2, this]⟩
  simp only [add, chain_eq, hNw, hk, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (chainAdd_ok hs (acc := acc) (a := a) (b := b) k (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := hL.acc_a; omega_using [hN2, hacc, hk, this]) (by have := hL.acc_b; omega_using [hN2, hacc, hk, this]))
    fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS rfl fun s₂ u₂ cf₂ => ?_
  refine wp_adcS rfl (by rw [cf₂]; exact hc) fun s₃ u₃ _ => ?_
  have k₃ : Keeps [.eax] s s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine wp_storeS (hs₃.ea (d := acc + 4 * (k + 1)) (by omega_arith))
    (hs₃.write (d := acc + 4 * (k + 1)) (n := 4) (by omega_arith)) fun s₄ m₄ => ?_
  have hs₄ := hs₃.of_keeps (m₄.keeps []) (by decide)
  have O₄ : Outside base acc (4 * (k + 1) + 4) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, u₂.mem]
    exact (O₁.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_using []) (by omega_using []))
  have hsum : val32 s₄.mem base acc (k + 1 + 1) =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by
    rw [val32_succ, m₄.mem, u₃.mem, u₂.mem, (writeW32_outside _ _ _ (by omega_arith)).val32 (by omega_using []) (by omega_arith),
      w32_write_self, u₃.gpr, u₂.gpr, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, hk, ← V₁]
    have : ((0 : BitVec 32) + 0 + (BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
    rw [this]
  have hm₄ : val32 s₄.mem base M.mo (k + 1) = m := by
    rw [O₄.val32 (by have := hL.acc_mo; omega_using [hN2, hacc, hk, this]) (by omega_arith), ← hk, hN2, ← wordsVal_eq_val32]; exact hM.val
  refine WP.mono (csub_ok hs₄ (hNw.trans hk) (src := acc) (o := o) (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := hL.acc_tmp; omega_using [hN2, hacc, hk, this]) (by have := hM.sep; omega_using [hN2, hk, this])
    (by have := hL.acc_o; omega_using [hN2, hacc, hk, this]) (by have := hL.o_tmp; omega_using [hN2, hk, this]) hm₄
        (by rw [hsum]; exact hAB))
    fun u ⟨O, V, K⟩ => ⟨?_, ?_⟩
  · refine OpKeep.of (((k₃.mono (rs' := clob) (by decide)).widen (m₄.keeps [])).widen K) (by decide) ?_
    have O₄' : Outside base acc (accLen M) s.mem s₄.mem := O₄.mono (Nat.le_refl _) (by omega_using [hacc, hk])
    refine (Outs.of_outside O₄' (by simp)).trans ?_
    rw [show 4 * (k + 1) = 8 * M.n by omega_using [hN2, hk]] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, hk, V, hsum]

end VG.Proof.Mont.X86.Dynamic
