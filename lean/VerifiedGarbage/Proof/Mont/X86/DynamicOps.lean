module

public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

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

/-- `[o] = [a] [b] R⁻¹ mod m`. The rows keep their multiplier in the first
word of `[M.tmp]`, so `[a]`, `[b]` and the inverse are apart from it. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {inv acc o a b : Nat}
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + accLen M ≤ inv)
    (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0) (hL : OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m)
    (hta : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 4 ≤ a) (htb : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 4 ≤ b)
    (hti : inv + 4 ≤ M.tmp ∨ M.tmp + 4 ≤ inv) :
    WP isa (VG.Impl.Mont.X86.Dynamic.mul M inv acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  -- Each side condition is solved from the facts it needs: `omega` on the
  -- whole context case-splits on every disjunction of the layout.
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have aL := hL.acc_le; have oL := hL.o_le; have aaL := hL.a_le; have bL := hL.b_le
  have moL := hM.mo; have tL := hM.tmp; have n0 := hM.n0; have mt := hM.sep
  have l₁ := hL.acc_a; have l₂ := hL.acc_b; have l₃ := hL.acc_mo; have l₄ := hL.acc_tmp
  have l₅ := hL.acc_o; have l₆ := hL.o_tmp
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun hz => by
    simp only [hz, Nat.zero_mul, Nat.zero_add] at hinv
    contradiction
  simp only [VG.Impl.Mont.X86.Dynamic.mul, hNw]
  have hmv : val32 s.mem base M.mo N = m := by
    rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b N < m := by
    rw [hN2, ← wordsVal_eq_val32]; exact hB
  have hML : MulLay N size acc a b M.mo := ⟨by omega_using [aL, hacc], by omega_using [aaL, hN2],
    by omega_using [bL, hN2], by omega_using [moL, hN2], by omega_using [l₁, hN2, hacc],
    by omega_using [l₂, hN2, hacc], by omega_using [l₃, hN2, hacc]⟩
  have hX : MultLay N size acc a b M.mo inv M.tmp := ⟨by omega_using [tL, n0], by omega_using [l₄, hacc, n0],
    by omega_using [hta, hN2], by omega_using [htb, hN2], by omega_using [mt, hN2, n0], hti⟩
  have hsi : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv := hacc ▸ hsepInv
  refine WP.seq (WP.mono (zerosW_ok hs (k := 2 * N + 1) (by omega_using []) (by omega_using [aL, hacc]))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine WP.seq (wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have k₂ : Keeps clobW s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mem₂ : s₂.mem = s₁.mem := u₂.mem
  have O₂ : Outside base acc (4 * (2 * N + 1)) s.mem s₂.mem := mem₂ ▸ O₁
  have hm₂ : val32 s₂.mem base M.mo N = m := by
    rw [O₂.val32 (by omega_using [l₃, hN2, hacc]) (by omega_using [moL, hN2, hn]), hmv]
  have hB₂ : val32 s₂.mem base b N < m := by
    rw [O₂.val32 (by omega_using [l₂, hN2, hacc]) (by omega_using [bL, hN2, hn])]; exact hBv
  have I₀ : LoopInvW base N acc a b m M.tmp 0 s₂ s₂ := by
    refine ⟨?_, Outs.refl _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [u₂.gpr, u₂.other _ (by decide), K₁.1 _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; omega_using [hB₂]
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; simp [val32]
  have hinv₂ : (m * w32 s₂.mem base inv + 1) % 2 ^ 32 = 0 := by
    rw [O₂.w32 hsi (by omega_using [hv, hn])]; exact hinv
  refine WP.seq (WP.mono (loop_ok hs₂ hML hX hv hsi (by omega_using [hN2, n0]) (by omega_using [hN2]) hm₂ hinv₂
    hB₂ I₀) fun t I => ?_)
  have ht := hs₂.of_keeps I.keeps (by decide)
  have hmt : val32 t.mem base M.mo N = m := by
    rw [outs2_val32 I.out (by omega_using [l₃, hN2, hacc]) (by omega_using [mt, hN2, n0])
      (by omega_using [moL, hN2, hn]), hm₂]
  have hlt := I.lt
  rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hlt
  refine WP.mono (csubW_ok ht hNw (src := acc + 4 * N) (o := o) (by omega_using [hN2, n0])
      (by omega_using [aL, hacc]) (by omega_using [oL, hN2]) (by omega_using [tL, hN2]) (by omega_using [moL, hN2])
      (by omega_using [l₄, hacc, hN2]) (by omega_using [mt, hN2]) (by omega_using [l₅, hacc, hN2])
      (by omega_using [l₆, hN2]) hmt hlt) fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [K.2.1, I.keeps.2.1, k₂.2.1],
      by rw [K.2.2, I.keeps.2.2, k₂.2.2], ?_⟩
    · rw [K.1 r (fun h => hr (by simp_all [clob])), I.keeps.1 r (by simp_all [clobW, clob]),
        k₂.1 r (by simp_all [clobW, clob])]
    · have O₂' : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem s₂.mem :=
        Outs.of_outside (hacc ▸ O₂) (by simp)
      have It : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s₂.mem t.mem := fun x hx =>
        I.out x (by
          have h₁ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          have h₂ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl)
          · simp only at h₁ ⊢; omega_using [h₁, hacc]
          · simp only at h₂ ⊢; omega_using [h₂, n0])
      refine (O₂'.trans It).trans ?_
      rw [show 4 * N = 8 * M.n by omega_using [hN2]] at O
      exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, V,
      show 64 * M.n = 32 * N by omega_using [hN2],
      ← O₂.val32 (d := a) (by omega_using [l₁, hN2, hacc]) (by omega_using [aaL, hN2, hn]),
      ← O₂.val32 (d := b) (by omega_using [l₂, hN2, hacc]) (by omega_using [bL, hN2, hn]), Nat.mod_mul_mod,
      Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Dynamic
