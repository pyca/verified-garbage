module

public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: `R² mod p`

`r2Prime_ok`: `Crt.r2Prime`, in a prime's working space of 24 arrays
(`Win.WCtx`), as PPC64LE's `Proof/Bignum/PPC64LE/PreR2Prime.lean`: `x := 1`
in array 1, `64 w + w` doublings (`r2Dbl_ok`) to `2^w R mod p`, then six
Montgomery squares (`sqrTail`, `WCtx.sqr`) to `2^(64 w) R mod p = R² mod p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Win

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

theorem exec_li6 {s : State} {d : Reg} : exec (.li d 6) s = some (s.write d (BitVec.ofNat 64 6)) := by
  rw [exec_li (by decide)]; rfl

theorem count_r2 (w : Nat) :
    BitVec.ofNat 64 w <<< 6 + BitVec.ofNat 64 w = BitVec.ofNat 64 (64 * w + w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

/-- The registers `r2Prime` writes. -/
def r2PRegs : List Reg := [.t3, .s0, .t5, .a1, .s7] ++ dblLoopRegs ++ sqRegs

/-- `r2Prime tmp`, with an odd `N ≥ 2` in array 0 and the bases of arrays
1–3 in `a2`, `a5`, `a6`: `R² mod N = 2^(128 w) mod N` in array 1, changing
only arrays 1–3 and `tmp`. -/
theorem r2Prime_ok {s : State} {B : Addr} {Z w N tmp : Nat} (h : WCtx s B Z w N)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2))
    (h6 : s.gpr .a6 = off B (slot w 3)) (ht4 : 4 ≤ tmp) (ht24 : tmp < 24) (hN : 2 ≤ N)
    (hodd : N % 2 = 1) :
    WP isa (Crt.r2Prime tmp) s fun t =>
      (WCtx t B Z w N ∧ A t.mem B w 1 = 2 ^ (128 * w) % N ∧
        (∀ j < 24, j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ tmp → A t.mem B w j = A s.mem B w j) ∧
        WinO B w s.mem t.mem) ∧ Keep r2PRegs s t := by
  have hn := h.nw
  have hw := h.w2
  have hw' := h.w31
  have hZ := h.hZ
  have e24 := slot24 w
  have s1 := slot_lt (w := w) (show 1 < 4 by decide)
  have s4 := slot_lt (w := w) (show 4 < 24 by decide)
  have e0 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_arith
  have e4 : slot w 4 = slot w 1 + 24 * (w + 2) := by unfold slot; omega_arith
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold Crt.r2Prime
  -- `x := 1`.
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (h.scr.congr k1.2.2) a3 ((k1.gpr (by decide)).trans h.t0) (by omega_arith)
    hw' (slot_al w 1) (by omega_arith)) fun s₂ ⟨⟨_, hz, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hs₂ := h.scr.congr k12.2.2
  refine WP.seq (WP.mono (WP.keep [.s0, .a1] (Q := fun t => t.gpr .a1 = BitVec.ofNat 64 (64 * w + w) ∧
      t.mem = s₂.mem.writeW (off B (slot w 1)) (BitVec.ofNat 64 1))
    (by brun [Pub.pub_li1, (k12.gpr (by decide)).trans h2, (k12.gpr (by decide)).trans h.t0, BitVec.add_zero,
      hs₂.st (d := slot w 1) (n := 8) (by omega_arith), hs₂.al8 (d := slot w 1) (by omega_arith) (slot_al w 1),
      count_r2 w]) (by rfl) (by rfl)) fun s₃ ⟨⟨a1, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have x3 : A s₃.mem B w 1 = 1 := by
    rw [m3]; exact Pub.one_word _ _ _ (by omega_arith) (by omega_arith) hz
  have o3 : Outside B (slot w 1) (8 * w) s.mem s₃.mem := by
    rw [m3]; rw [m1] at o2
    exact o2.trans ((writeW_outside s₂.mem B (d := slot w 1) _ (by omega_arith)).mono (by omega_arith)
      (by omega_arith))
  have O3 : WinO B w s.mem s₃.mem := o3.mono (Nat.le_refl _) (by omega_arith)
  have c3 := h.of k13 (by decide) O3
  -- The doublings.
  refine WP.seq (WP.mono (r2Dbl_ok (N := N) (a := 0) (M := 64 * w + w) c3.scr
    ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans h6) c3.a7 ((k13.gpr (by decide)).trans h2)
    c3.t0 (by omega_arith) hw' (by omega_arith) c3.n (by omega_arith)
    (by show A s₃.mem B w 1 = _; rw [x3, Nat.pow_zero, Nat.mod_eq_of_lt (by omega_arith)]) a1 (by omega_arith) (by omega_arith))
    fun s₄ ⟨x4, o4, k4⟩ => ?_)
  replace x4 : A s₄.mem B w 1 = 2 ^ (0 + (64 * w + w)) % N := x4
  have O4 : WinO B w s₃.mem s₄.mem := o4.mono (Nat.le_refl _) (by omega_arith)
  have c4 := c3.of k4 (by decide) O4
  have f4 : ∀ j < 24, j ≠ 1 → j ≠ 2 → j ≠ 3 → A s₄.mem B w j = A s.mem B w j := by
    intro j hj h1 h2' h3'
    show wordsVal _ B (slot w j) w = wordsVal _ B (slot w j) w
    have := slot_lt (w := w) hj
    rcases Nat.lt_or_ge j 1 with hj0 | hj4
    · obtain rfl : j = 0 := by omega_arith
      rw [Outside.wordsVal o4 (Or.inl (by omega_arith)) (by omega_arith),
        Outside.wordsVal o3 (Or.inl (by omega_arith)) (by omega_arith)]
    · have hj4' : 4 ≤ j := by omega_arith
      have := Nat.mul_le_mul_right (8 * (w + 2)) hj4'
      have es : slot w j = hdrBytes + j * (8 * (w + 2)) := rfl
      have es1 : slot w 1 = hdrBytes + 8 * (w + 2) := by unfold slot; omega_arith
      rw [Outside.wordsVal o4 (Or.inr (by omega_arith)) (by omega_arith),
        Outside.wordsVal o3 (Or.inr (by omega_arith)) (by omega_arith)]
  have k14 := k13.trans k4
  -- Six squares.
  have hN0 : 0 < N := by omega_arith
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 6 ∧ u.mem = s₄.mem)
    (by brun [exec_li6]) (by rfl) (by rfl)) fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_)
  have c5 := c4.regs k5 (by decide) m5
  let Inv : Nat → State → Prop := fun j u =>
    WCtx u B Z w N ∧ A u.mem B w 1 < N ∧ A u.mem B w 1 % N = 2 ^ (w * 2 ^ j) * 2 ^ (64 * w) % N ∧
      (∀ j < 24, j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ tmp → A u.mem B w j = A s.mem B w j) ∧
      WinO B w s.mem u.mem ∧ Keep r2PRegs s u
  refine WP.mono (wp_countdown (cnt := .s7) (N := 6) (by decide) (by decide) Inv
    (fun j _ u ⟨cu, lu, xu, fu, ou, ku⟩ _ => ?_) ⟨c5, ?_, ?_, ?_, ?_, ?_⟩ a7) fun t ⟨ct, lt, xt, ft, ot, kt⟩ => ?_
  · refine WP.seq (WP.mono (cu.sqr (o := 1) (a := 1) (p := tmp) (by decide) (by decide) ht24 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) lu)
      fun u₁ ⟨⟨c1, l1, e1, v1, o1⟩, k1'⟩ => ?_)
    refine WP.mono (dec_ok u₁ .s7) fun u₂ e2 => ?_
    subst e2
    have he : w * 2 ^ (j + 1) = w * 2 ^ j + w * 2 ^ j := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
    refine ⟨⟨c1.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact l1, ?_, ?_,
      by rw [mem_write]; exact ou.trans o1, Keep.trans' ku ((k1'.trans (Keep.write _ _ _)).mono (by decide))⟩, ?_⟩
    · rw [mem_write, he]
      exact mont_pow hR xu xu e1
    · intro j' hj' h1 h2' h3' ht
      rw [mem_write, v1 j' hj' h2' h3' ht h1]
      exact fu j' hj' h1 h2' h3' ht
    · gsimp; rw [k1'.gpr (by decide)]
  · rw [m5, x4]; exact Nat.mod_lt _ hN0
  · rw [m5, x4, Nat.mod_mod, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
  · intro j hj h1 h2' h3' _
    rw [m5]; exact f4 j hj h1 h2' h3'
  · rw [m5]; exact O3.trans O4
  · exact (k14.trans k5).mono (by decide)
  · refine ⟨⟨ct, ?_, ft, ot⟩, kt⟩
    have h6 : w * 2 ^ 6 = 64 * w := by rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]
    rw [← Nat.mod_eq_of_lt lt, xt, h6, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_arith]

end VG.Proof.Bignum.RISCV64.Win
