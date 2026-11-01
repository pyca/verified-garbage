module

public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-KEM on RISC-V: common lemmas

What the proofs of the primitives share: the rule for a loop counted down to
zero (`wp_loop_nz`), the counts, and the arithmetic of the reductions modulo
`q` on 64 bits (`fixq`, the value `VG.Impl.MlKem.RISCV64.fixup` computes), as on PPC64LE
(`Proof/MlKem/PPC64LE/Common.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64
open VG.Spec.MlKem

/-! ## Loops -/

/-- A `do … while (r ≠ 0)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `r` zero exactly when it is the last. -/
theorem wp_loop_nz {body : Prog isa} {r : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr r != 0) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.nonzero r)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.nonzero r) s' = some (decide (i + 1 ≠ N)) := by
    show (some (!(s'.gpr r == 0)) : Option Bool) = _
    rw [← hz]; rfl
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩

/-- The count after `addi r, r, -1` from `N - i`. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  rw [show N - i = (N - (i + 1)) + 1 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The count is nonzero exactly when it is not the last iteration. -/
theorem count_nz {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 (N - (i + 1)) != 0) = decide (i + 1 ≠ N) := by
  by_cases h : i + 1 = N
  · subst h; simp
  · have h1 : (BitVec.ofNat 64 (N - (i + 1))).toNat = N - (i + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have : BitVec.ofNat 64 (N - (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega
    rw [bne_iff_ne.mpr this]; simp [h]

/-- A pointer `p` advanced by `k i`, then by `k`. -/
theorem ptr_succ (p : BitVec 64) (k i : Nat) :
    p + BitVec.ofNat 64 (k * i) + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (k * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- A pointer advanced twice. -/
theorem ptr_add (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Two pointers from `p` differ exactly when their offsets do. -/
theorem ptr_ne (p : BitVec 64) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a - (p + BitVec.ofNat 64 b) != 0) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    have : p + BitVec.ofNat 64 a - (p + BitVec.ofNat 64 b) ≠ 0 := fun e => hne (by bv_omega)
    rw [bne_iff_ne.mpr this]; simp [h]

/-- `4 len >> 2`, the count of a block's butterflies. -/
theorem lsr2 {len : Nat} (h : 4 * len < 2 ^ 64) :
    BitVec.ofNat 64 (4 * len) >>> 2 = BitVec.ofNat 64 (len - 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  omega

/-- One more coefficient of an invariant saying which are `out`. -/
theorem coeff_one {m m₀ : Mem} {F : Addr} {out : Nat → BitVec 32} {a : Nat} (ha : a < 256)
    (h : ∀ j < 256, coeffAt m F j = if j < a then out j else coeffAt m₀ F j) {v : BitVec 32}
    (hv : v = out a) :
    ∀ j < 256, coeffAt (m.writeW (coeffAddr F a) v) F j = if j < a + 1 then out j else coeffAt m₀ F j := by
  intro j hj
  rw [coeffAt_writeW _ _ (by rw [n_eq]; exact hj) (by rw [n_eq]; exact ha), h j hj]
  by_cases e : a = j
  · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self a), hv]
  · rw [ite_eq_right e]
    by_cases hj' : j < a
    · rw [ite_eq_left hj', ite_eq_left (by omega)]
    · rw [ite_eq_right hj', ite_eq_right (by omega)]

/-! ## Words -/

/-- A word, zero-extended, as `lwu` loads it. -/
theorem toNat_setWidth64 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := v.isLt; omega)

/-- A word, zero-extended. -/
theorem setWidth64_ofNat {v : Nat} (hv : v < 2 ^ 32) : (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

/-- A doubleword below `2³²`, as `sw` stores it. -/
theorem setWidth32_ofNat {x : BitVec 64} {v : Nat} (h : x.toNat = v) (hv : v < 2 ^ 32) :
    x.setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-! ## Reduction modulo `q` -/

/-- What `fixup` leaves: `u + q` if `u` is negative, `u` otherwise. -/
def fixq (u : BitVec 64) : BitVec 64 := u + (u.sshiftRight 63 &&& 3329)

theorem fixq_toNat {u : BitVec 64} (h : u.toNat < 3329 ∨ 2 ^ 64 - 3329 ≤ u.toNat) :
    (fixq u).toNat = if u.toNat < 3329 then u.toNat else u.toNat + 3329 - 2 ^ 64 := by
  unfold fixq
  cases hm : u.msb
  · have hu : u.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : u >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, BitVec.zero_and]
    split <;> bv_omega
  · have hu : 2 ^ 63 ≤ u.toNat := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : (~~~u) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, BitVec.allOnes_and]
    split <;> bv_omega

/-- `fixq (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixq_add {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixq (a + b - 3329)).toNat = (a.toNat + b.toNat) % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (a - b)`: the difference of reduced values, reduced. -/
theorem fixq_sub {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixq (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixq (x - q)` of `x < 2q`: `x` reduced. -/
theorem fixq_subq {x : BitVec 64} (hx : x.toNat < 2 * q) : (fixq (x - 3329)).toNat = x.toNat % q := by
  rw [q_eq] at *
  rw [fixq_toNat (by bv_omega)]
  split <;> bv_omega

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

end VG.Proof.MlKem.RISCV64
