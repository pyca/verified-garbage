import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Csub

/-!
# Montgomery arithmetic on x86 (32-bit): the operations

For a modulus `m` in the working space (`ModOk`) and an accumulator of
`accLen M` bytes at `acc` apart from the numbers (`OpLay`): `mul acc o a b`
writes `[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes
`[a] + [b] mod m` (`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`),
for `[a]`, `[b]` below `m`, in the shape of the other targets' operations
(`n` 64-bit words). Each changes only the registers `clob`, the result, the
temporary area and the accumulator (`OpKeep`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The bytes of the accumulator: `2N + 1` words. -/
def accLen (M : Mod) : Nat := 4 * (2 * words M + 1)

/-- Where the operations' numbers are: in the working space, and the
accumulator apart from them, from the modulus and from the temporary area,
which `[o]` is apart from too. -/
structure OpLay (M : Mod) (size acc o a b : Nat) : Prop where
  acc_le : acc + accLen M ≤ size
  o_le : o + 8 * M.n ≤ size
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  acc_o : acc + accLen M ≤ o ∨ o + 8 * M.n ≤ acc
  acc_a : acc + accLen M ≤ a ∨ a + 8 * M.n ≤ acc
  acc_b : acc + accLen M ≤ b ∨ b + 8 * M.n ≤ acc
  acc_mo : acc + accLen M ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc
  acc_tmp : acc + accLen M ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc
  o_tmp : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, and the memory but `[o]`, the temporary area and the accumulator. -/
structure OpKeep (M : Mod) (base : Addr) (acc o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem s'.mem

theorem OpKeep.of {M : Mod} {base : Addr} {acc o : Nat} {s s' : State} {rs : List Reg} (h : Keeps rs s s')
    (hr : ∀ r ∈ rs, r ∈ clob := by decide)
    (hm : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem s'.mem) : OpKeep M base acc o s s' :=
  ⟨fun r h' => h.1 r fun h'' => h' (hr r h''), h.2.1, h.2.2, hm⟩

/-- `k` stores of `eax = 0` from `[acc]`. -/
theorem stores0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (heax : s.gpr .eax = 0)
    {acc : Nat} : ∀ k, acc + 4 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store (sc (acc + 4 * j)) .eax)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ val32 u.mem base acc k = 0 ∧ Keeps [] s u
  | 0, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (stores0_ok hs heax k (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_storeS (hs₁.ea (d := acc + 4 * k) (by omega)) (hs₁.write (d := acc + 4 * k) (n := 4) (by omega))
      fun u m => WP.block_nil ⟨?_, ?_, K₁.trans (m.keeps _)⟩
    · rw [m.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · rw [val32_succ, m.mem, (writeW32_outside _ _ _ (by omega)).val32 (by omega) (by omega), V₁,
        w32_write_self, K₁.1 _ (by decide), heax]
      rfl

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc k : Nat}
    (hk : acc + 4 * k ≤ size) :
    WP isa (.block (zeros acc k)) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ val32 u.mem base acc k = 0 ∧ Keeps [.eax] s u := by
  simp only [zeros]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine WP.mono (stores0_ok (hs.of_keeps u₁.keeps (by decide)) u₁.gpr k hk) fun u ⟨O, V, K⟩ =>
    ⟨u₁.mem ▸ O, V, u₁.keeps.trans (K.mono (by decide))⟩

theorem m_pos_of_inv {m : Nat} {minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mul M acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo N = m := by rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b N < m := by rw [hN2, ← wordsVal_eq_val32]; exact hB
  have hML : MulLay N size acc a b M.mo := ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp only [mul, hNw]
  refine WP.seq (WP.block_append (WP.mono (zeros_ok hs (k := 2 * N + 1) (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_))
  refine wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_
  have k₂ : Keeps clob s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mem₂ : s₂.mem = s₁.mem := u₂.mem
  have O₂ : Outside base acc (4 * (2 * N + 1)) s.mem s₂.mem := mem₂ ▸ O₁
  have hm₂ : val32 s₂.mem base M.mo N = m := by rw [O₂.val32 (by omega) (by omega), hmv]
  have hB₂ : val32 s₂.mem base b N < m := by rw [O₂.val32 (by omega) (by omega)]; exact hBv
  have I₀ : LoopInv base N acc a b m 0 s₂ s₂ := by
    refine ⟨?_, VG.Proof.Mont.Outside.refl _ _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [u₂.gpr, u₂.other _ (by decide), K₁.1 _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; omega
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; simp [val32]
  refine WP.seq (WP.mono (loop_ok hs₂ hNw hML (by omega) hm₂ (minv32_inv hM.inv) hB₂ I₀) fun t I => ?_)
  have ht := hs₂.of_keeps I.keeps (by decide)
  have hmt : val32 t.mem base M.mo N = m := by rw [I.out.val32 (by omega) (by omega), hm₂]
  have hlt := I.lt
  rw [show 2 * N + 1 - N = N + 1 by omega] at hlt
  refine WP.mono (csub_ok ht hNw (src := acc + 4 * N) (o := o) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hmt hlt) fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_⟩
  · refine OpKeep.of ((k₂.trans I.keeps).trans (K.mono (by decide))) (by decide) ?_
    have O₂' : Outside base acc (accLen M) s.mem s₂.mem := by rw [hacc]; exact O₂
    have O₃ : Outside base acc (accLen M) s₂.mem t.mem := by rw [hacc]; exact I.out
    refine ((Outs.of_outside O₂' (by simp)).trans (Outs.of_outside O₃ (by simp))).trans ?_
    rw [show 4 * N = 8 * M.n by omega] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hN2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [show 2 * N + 1 - N = N + 1 by omega] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, V,
      show 64 * M.n = 32 * N by omega, ← O₂.val32 (d := a) (by omega) (by omega),
      ← O₂.val32 (d := b) (by omega) (by omega), Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86
