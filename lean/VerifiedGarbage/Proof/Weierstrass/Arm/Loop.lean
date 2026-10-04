import VerifiedGarbage.Proof.Weierstrass.Arm.Copy

/-!
# Short Weierstrass curves on 32-bit ARM: loops counted down in `r11`

The ladder, the powers and the tables of bits loop with `r11` counting down:
the body starts with `sub r11, r11, #1` (`wp_decCounter`) and ends with
`cmp r11, #0` (`wp_testCounter`), and the loop runs while `r11 ≠ 0`
(`bne`). `countLoop_ok` runs such a loop `n ≥ 1` times from an invariant
indexed by `r11`.
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_dp wp_cmp op2_imm dpVal)

/-- A loop whose body takes the invariant from `j` to `j - 1` and leaves
`Z` set iff `j - 1 = 0`, run from `n ≥ 1`. -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.z = decide (j - 1 = 0))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj]; rfl,
      hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj]; rfl,
      j - 1, by omega, by omega, by omega, hi'⟩

theorem ofNat_pred32 {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 32 j - 1 = BitVec.ofNat 32 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_sub, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `r11 -= 1`. -/
theorem wp_decCounter {j : Nat} (hj : 1 ≤ j) (hb : s.gpr .r11 = BitVec.ofNat 32 j)
    (k : ∀ t, Upd s t .r11 (BitVec.ofNat 32 (j - 1)) → WP isa (.block is) t Q) :
    WP isa (.block (decCounter :: is)) s Q :=
  wp_dp (op2_imm (by decide)) fun t u => k t (by rw [dpVal, hb, ofNat_pred32 hj] at u; exact u)

/-- `cmp r11, #0`. -/
theorem wp_testCounter {j : Nat} (hj : j < 2 ^ 32) (hb : s.gpr .r11 = BitVec.ofNat 32 j)
    (k : ∀ t, Fupd s t → t.z = decide (j = 0) → WP isa (.block is) t Q) :
    WP isa (.block (testCounter :: is)) s Q :=
  wp_cmp (op2_imm (by decide)) fun t f z => k t f (by
    rw [z, hb, show BitVec.ofNat 32 j - 0 = BitVec.ofNat 32 j from BitVec.sub_zero _,
      VG.Proof.X25519.Arm.ofNat_beq_zero hj])

end

/-- `[r + d]` where `r = r12 + k`, in the working space. -/
theorem _root_.VG.Proof.Mont.Arm.Scr.ea_reg {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {r : Reg} {k d : Nat} (hr : s.gpr r = s.gpr .r12 + BitVec.ofNat 32 k) (hd : k + d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 d) = off base (k + d) := by
  rw [hr, Offset.add_add]
  exact hs.ea hd

end VG.Proof.Weierstrass.Arm
