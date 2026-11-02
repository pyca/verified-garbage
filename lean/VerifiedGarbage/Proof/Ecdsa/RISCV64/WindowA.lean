module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder

/-!
# `[k]Q` by four-bit windows on RISC-V, for any curve: what does not depend on it

The facts the proofs of `Impl/Ecdsa/RISCV64/WindowA.lean`'s `mulFn` for each
curve share:

* the windows' points: `R` before window `j - 1` is `[k >>> 4 j]Q` (`wpt`),
  `16 R + [k_j]Q` is `R` after it (`wstep`), and `O` before the first
  (`wpt_top`);
* `[e + 1]Q = [e]Q + Q` (`mul_succ'`), which the table's entries follow;
* `nibble_ok`: the nibble `k_j` into `t2`, for `j` in `s1`, from the word
  `j >>> 4` of `k` at `K`'s slot.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.WindowA

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.WindowA
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Proof.X25519.RISCV64 (Rest)

/-! ## The points -/

section
variable {C : Spec.Weierstrass.Curve}

/-- `2 P`. -/
abbrev d2 (P : Point C) : Point C := Spec.Weierstrass.add P P

/-- `16 P`, by four doublings. -/
abbrev d16 (P : Point C) : Point C := d2 (d2 (d2 (d2 P)))

/-- `R` before window `j - 1`: `[k >>> 4 j]Q`. -/
abbrev wpt (Q : Point C) (k j : Nat) : Point C := mul (k >>> (4 * j)) Q

theorem shr_four (k j : Nat) : k >>> (4 * j) = 16 * (k >>> (4 * (j + 1))) + (k >>> (4 * j)) % 16 := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (k >>> (4 * j)) 4]
  omega

/-- A window: `16 R + [k_j]Q`, for `R` before it, is `R` after it. -/
theorem wstep (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (k j : Nat) :
    Spec.Weierstrass.add (d16 (wpt Q k (j + 1))) (mul ((k >>> (4 * j)) % 16) Q) = wpt Q k j := by
  have ek := shr_four k j
  simp only [wpt, d16, d2]
  generalize (k >>> (4 * j)) % 16 = a at ek ⊢
  rw [ek]
  generalize k >>> (4 * (j + 1)) = m
  have hX := hL.onCurve_mul hQ m
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  have h8 := hL.onCurve_add h4 h4
  have h16 := hL.onCurve_add h8 h8
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h16 (hL.onCurve_mul hQ _)) (hL.onCurve_mul hQ _)
  rw [hf.add h16 (hL.onCurve_mul hQ _), hf.add h8 h8, hf.add h4 h4, hf.add h2 h2, hf.add hX hX,
    hf.mul hQ, hf.mul hQ, hf.mul hQ]
  have hu : ((16 * m + a : Nat) : Int) = m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + m + a := by
    omega
  rw [hu]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

/-- Before the first window, for `k` of `n` words: `O`. -/
theorem wpt_top (Q : Point C) {n k : Nat} (hk : k < 2 ^ (64 * n)) : wpt Q k (16 * n) = .infinity := by
  rw [wpt, Nat.shiftRight_eq_div_pow, show 4 * (16 * n) = 64 * n by omega, Nat.div_eq_of_lt hk,
    Spec.Weierstrass.mul]; rfl

/-- After the last window: `[k]Q`. -/
theorem wpt_zero (Q : Point C) (k : Nat) : wpt Q k 0 = mul k Q := by
  simp only [wpt, Nat.mul_zero, Nat.shiftRight_zero]

/-- `[n + 1]Q = [n]Q + Q`. -/
theorem mul_succ' (hL : Law C) {Q : Point C} (hQ : onCurve C Q = true) (n : Nat) :
    Spec.Weierstrass.add (mul n Q) Q = mul (n + 1) Q := by
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add (hL.onCurve_mul hQ _) hQ) (hL.onCurve_mul hQ _)
  rw [hf.add (hL.onCurve_mul hQ _) hQ, hf.mul hQ, hf.mul hQ, show ((n + 1 : Nat) : Int) = n + 1 by omega]
  simp only [Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.one_zsmul]

end

/-! ## The nibble -/

theorem four_bits (x : BitVec 64) (u : Nat) {j : Nat}
    (h : ∀ i < 4, x.getLsbD (4 * j % 64 + i) = u.testBit (4 * j + i)) :
    (x >>> (4 * j % 64)) &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 ((u >>> (4 * j)) % 16) := by
  rw [show (u >>> (4 * j)) % 16 = (u >>> (4 * j)) % 2 ^ 4 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, show (BitVec.ofInt 64 15) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h4 : i < 4
  · simp only [h4, decide_true, Bool.and_true, Bool.true_and, hi]
    exact h i h4
  · simp [h4]

/-- The nibble `k_j` into `t2`, for `j` in `s1`, of the `n` words at `K`'s
slot. -/
theorem nibble_ok (c : Cfg) {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 16 * c.n)
    (hK : c.sl K + 8 * c.n ≤ 4096) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.nibble c)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 ((wordsVal s.mem base (c.sl K) c.n >>> (4 * j)) % 16) ∧
      Rest [.t0, .t1, .t2] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : j / 16 < c.n := by omega
  have hK8 : c.sl K % 8 = 0 := by simp only [Cfg.sl, slot, K]; omega
  rw [Cfg.nibble]
  simp only [List.cons_append, List.nil_append]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e₃' : s₃.gpr .t0 = base + BitVec.ofNat 64 (8 * (j / 16)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), hw.s0, h1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : j / 16 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (j / 16) < 18446744073709551616)]
    omega
  have e₃ : ∀ d, s₃.gpr .t0 + BitVec.ofNat 64 d = off base (d + 8 * (j / 16)) := by
    intro d
    rw [e₃', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₃ : Rest [.t0] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldAt (by omega) (e₃ (c.sl K))
    (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base (k := 8192) (by omega) (by omega)⟩
    fun s₄ u₄ => ?_
  refine wp_sll (by decide) fun s₅ u₅ => wp_srlReg fun s₆ u₆ => wp_andi (by decide) fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t1₅ : (s₅.gpr .t1).toNat % 64 = 4 * j % 64 := by
      rw [u₅.gpr, u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp only [Nat.shiftLeft_eq, Nat.reducePow]
      omega
    have hu := four_bits (s₄.gpr .t2) (wordsVal s.mem base (c.sl K) c.n) (j := j) fun i hi => by
      rw [u₄.gpr, m₃, BitVec.getLsbD, show 4 * j % 64 + i = (4 * j + i) % 64 by omega,
        ← testBit_wordsVal s.mem base c.n (c.sl K) (4 * j + i) (by omega),
        show (4 * j + i) / 64 = j / 16 by omega, Nat.add_comm]
    rw [u₇.gpr, u₆.gpr, t1₅, u₅.other .t2 (by decide), hu]
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans (u₇.rest (by decide)))))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

end VG.Proof.Ecdsa.RISCV64.WindowA
