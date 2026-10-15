module

public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Mont.X86.Csub

/-! # Runtime-modulus Montgomery multiplication on 32-bit x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- Workspace geometry and the runtime modulus. No fixed inverse or
special-form modulus is required. -/
structure Modulus (M : Mod) (size m : Nat) (mem : Mem) (base : Addr) : Prop where
  n0 : 0 < M.n
  mo : M.mo + 8 * M.n ≤ size
  tmp : M.tmp + 8 * M.n ≤ size
  sep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  val : wordsVal mem base M.mo M.n = m

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {inv acc o a b : Nat}
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + accLen M ≤ inv)
    (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0) (hL : OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.mul M inv acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le
  have := hM.mo; have := hM.tmp; have := hM.n0
  have hm0 : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_add] at hinv
    contradiction
  have hmv : val32 s.mem base M.mo N = m := by rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b N < m := by rw [hN2, ← wordsVal_eq_val32]; exact hB
  have hML : MulLay N size acc a b M.mo := ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith,
    by have := hL.acc_a; omega_using [hN2, hacc, this], by have := hL.acc_b; omega_using [hN2, hacc, this], by have := hL.acc_mo; omega_using [hN2, hacc, this]⟩
  simp only [VG.Impl.Mont.X86.Dynamic.mul, hNw]
  refine WP.seq (WP.block_append (WP.mono (zeros_ok hs (k := 2 * N + 1) (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_))
  refine wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_
  have k₂ : Keeps clob s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mem₂ : s₂.mem = s₁.mem := u₂.mem
  have O₂ : Outside base acc (4 * (2 * N + 1)) s.mem s₂.mem := mem₂ ▸ O₁
  have hm₂ : val32 s₂.mem base M.mo N = m := by rw [O₂.val32 (by have := hL.acc_mo; omega_using [hN2, hacc, this]) (by omega_arith), hmv]
  have hB₂ : val32 s₂.mem base b N < m := by rw [O₂.val32 (by have := hL.acc_b; omega_using [hN2, hacc, this]) (by omega_arith)]; exact hBv
  have I₀ : LoopInv base N acc a b m 0 s₂ s₂ := by
    refine ⟨?_, VG.Proof.Mont.Outside.refl _ _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [u₂.gpr, u₂.other _ (by decide), K₁.1 _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; omega_using [hB₂]
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; simp [val32]
  have hinv₂ : (m * w32 s₂.mem base inv + 1) % 2 ^ 32 = 0 := by
    rw [O₂.w32 (by omega_using [hsepInv, hacc]) (by omega_arith)]; exact hinv
  refine WP.seq (WP.mono (loop_ok hs₂ hML hv (by omega_using [hsepInv, hacc])
    (by omega_using [hN2, this]) hm₂ hinv₂ hB₂ I₀) fun t I => ?_)
  have ht := hs₂.of_keeps I.keeps (by decide)
  have hmt : val32 t.mem base M.mo N = m := by rw [I.out.val32 (by have := hL.acc_mo; omega_using [hN2, hacc, this]) (by omega_arith), hm₂]
  have hlt := I.lt
  rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hlt
  refine WP.mono (csub_ok ht hNw (src := acc + 4 * N) (o := o) (by omega_using [hN2, this]) (by omega_arith)
      (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := hL.acc_tmp; omega_using [hacc, this]) (by have := hM.sep; omega_using [hN2, this])
    (by have := hL.acc_o; omega_using [hacc, this]) (by have := hL.o_tmp; omega_using [hN2, this]) hmt hlt) fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_⟩
  · refine OpKeep.of ((k₂.trans I.keeps).trans (K.mono (by decide))) (by decide) ?_
    have O₂' : Outside base acc (accLen M) s.mem s₂.mem := by rw [hacc]; exact O₂
    have O₃ : Outside base acc (accLen M) s₂.mem t.mem := by rw [hacc]; exact I.out
    refine ((Outs.of_outside O₂' (by simp)).trans (Outs.of_outside O₃ (by simp))).trans ?_
    rw [show 4 * N = 8 * M.n by omega_using [hN2]] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, V,
      show 64 * M.n = 32 * N by omega_using [hN2], ← O₂.val32 (d := a) (by have := hL.acc_a; omega_using [hN2, hacc, this]) (by omega_arith),
      ← O₂.val32 (d := b) (by have := hL.acc_b; omega_using [hN2, hacc, this]) (by omega_arith), Nat.mod_mul_mod, Nat.mul_comm, hU,
      Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Dynamic
