module

public import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Montgomery arithmetic on x86 (32-bit): the operations

For a modulus `m` in the working space (`ModOkW`), an accumulator of
`accLen M` bytes at `acc` apart from the numbers (`OpLay`), and what an
operation changes: only the registers `clob`, the result, the temporary
area and the accumulator (`OpKeep`). Clearing the accumulator
(`zeros_ok`).
-/

@[expose] public section

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
    refine WP.block_append (WP.mono (stores0_ok hs heax k (by omega_using [hk])) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_storeS (hs₁.ea (d := acc + 4 * k) (by omega_using [hk])) (hs₁.write (d := acc + 4 * k) (n := 4) (by omega_using [hk]))
      fun u m => WP.block_nil ⟨?_, ?_, K₁.trans (m.keeps _)⟩
    · rw [m.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [hk, hn])).mono (by omega_using []) (by omega_using []))
    · rw [val32_succ, m.mem, (writeW32_outside _ _ _ (by omega_using [hk, hn])).val32 (by omega_using []) (by omega_using [hk, hn]), V₁,
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

end VG.Proof.Mont.X86
