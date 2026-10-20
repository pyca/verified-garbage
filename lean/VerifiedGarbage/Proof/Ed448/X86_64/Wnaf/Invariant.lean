module

public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Step
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
import VerifiedGarbage.Proof.X448.X86_64.Bits

/-! The recoder changes only its bounded digit array. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (residual)

structure RecInv (base : Addr) (dst k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  carry : ∃ c ≤ 32, s.gpr .rcx = BitVec.ofNat 64 c ∧ residual k n + 16 = k / 2 ^ n + c
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base dst 461 s₀.mem s.mem
  digits : ∀ i < n, s.mem (off base (dst + i)) = Enc k i

theorem RecInv.advance {base : Addr} {dst k n : Nat} {s₀ s u : State}
    (h : RecInv base dst k s₀ n s) (hn : n < 461) (hbound : dst + 461 ≤ 8192)
    (g : StepOut base dst k n s u) : RecInv base dst k s₀ (n + 1) u := by
  refine ⟨⟨(g.gpr _ (by decide)).trans h.scr.rdi, g.wr ▸ h.scr.wr, h.scr.nowrap⟩,
    g.rbx, g.carry, fun r hr => (g.gpr r hr).trans (h.gpr r hr), g.rd.trans h.rd, g.wr.trans h.wr, ?_, ?_⟩
  · intro p hp
    rw [g.mem, writeW8_outside _ base _ (by omega) (by rcases hp with hp | hp <;> omega)]
    exact h.mem p hp
  · intro i hi
    rw [g.mem, writeW8_apply]
    simp only [off_eq_iff base (d := dst + i) (e := dst + n) (by omega) (by omega)]
    by_cases he : i = n
    · subst i; simp only [ite_true]
    · rw [ite_eq_right (by omega)]
      exact h.digits i (by omega)

theorem RecInv.bits {base : Addr} {dst k n src : Nat} {s₀ s : State}
    (h : RecInv base dst k s₀ n s) (hsrc : 1 ≤ src) (hsep : src + 460 ≤ dst) (hb : dst + 461 ≤ 8192)
    (bs : Window.Bits base src k s₀) : Window.Bits base src k s := by
  intro t ht
  rw [h.mem _ (Or.inl (by rw [ofs_off' base (by omega)]; omega))]
  exact bs t ht

theorem RecInv.keeps {base : Addr} {dst k n : Nat} {s₀ s u : State}
    (h : RecInv base dst k s₀ n s) (g : Keeps [] s u) : RecInv base dst k s₀ n u := by
  refine ⟨h.scr.of_keeps g (by decide), (g.1 _ (by simp)).trans h.rbx, ?_,
    fun r hr => (g.1 r (by simp)).trans (h.gpr r hr), g.2.2.1.trans h.rd, g.2.2.2.trans h.wr, ?_, ?_⟩
  · obtain ⟨c, hc, hr, he⟩ := h.carry
    exact ⟨c, hc, (g.1 _ (by simp)).trans hr, he⟩
  · rw [g.2.1]; exact h.mem
  · rw [g.2.1]; exact h.digits

end VG.Proof.Ed448.X86_64.Wnaf
