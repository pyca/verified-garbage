module

public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Modular subtraction for a runtime modulus -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem runtimeSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M acc o a b)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le
  have := hM.mo; have := hM.tmp; have := hM.n0
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega_using [hN2, this]⟩
  simp only [sub, chain_eq, masked_eq, hNw, hk, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (chainSub_ok hs (acc := acc) (a := a) (b := b) k (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := hL.acc_a; omega_using [hN2, hacc, hk, this]) (by have := hL.acc_b; omega_using [hN2, hacc, hk, this]))
    fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_sbbS rfl hc fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .edx] s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mask : s₂.gpr .eax = if c then BitVec.allOnes 32 else 0 := by rw [u₂.gpr, borrow_mask]
  refine WP.block_append (WP.mono (masked_ok hs₂ c mask (k + 1) (mo := M.mo) (tmp := M.tmp) (by omega_arith)
    (by omega_arith) (by have := hM.sep; omega_using [hN2, hk, this])) fun s₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have k₃ : Keeps [.eax, .edx] s s₃ := k₂.widen K₃
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine WP.mono (chainAdd_ok hs₃ (acc := o) (a := acc) (b := M.tmp) k (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := hL.acc_o; omega_using [hN2, hacc, hk, this]) (by have := hL.o_tmp; omega_using [hN2, hk, this]))
    fun u ⟨O, ⟨c', _, V⟩, K⟩ => ⟨?_, ?_⟩
  · refine OpKeep.of (k₃.widen K) (by decide) ?_
    have O₁' : Outside base acc (accLen M) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega_using [hacc, hk])
    rw [u₂.mem] at O₃
    rw [show 4 * (k + 1) = 8 * M.n by omega_using [hN2, hk]] at O₃ O
    exact ((Outs.of_outside O₁' (by simp)).trans (Outs.of_outside O₃ (by simp))).trans
      (Outs.of_outside O (by simp))
  · have hacc₃ : val32 s₃.mem base acc (k + 1) = val32 s₁.mem base acc (k + 1) := by
      rw [O₃.val32 (by have := hL.acc_tmp; omega_using [hN2, hacc, hk, this]) (by omega_arith), u₂.mem]
    have hmo : val32 s₁.mem base M.mo (k + 1) = m := by
      rw [O₁.val32 (by have := hL.acc_mo; omega_using [hN2, hacc, hk, this]) (by omega_arith), ← hk, hN2, ← wordsVal_eq_val32]; exact hM.val
    rw [hacc₃, V₃, u₂.mem, hmo] at V
    have e : 2 * M.n = k + 1 := by omega_using [hN2, hk]
    have hA' : val32 s.mem base a (k + 1) < m := by rw [← e, ← wordsVal_eq_val32]; exact hA
    have hB' : val32 s.mem base b (k + 1) < m := by rw [← e, ← wordsVal_eq_val32]; exact hB
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, e]
    exact sub_arith hA' hB' (val32_lt _ _ _ _) (val32_lt _ _ _ _) V₁ V

end VG.Proof.Bignum.X86
