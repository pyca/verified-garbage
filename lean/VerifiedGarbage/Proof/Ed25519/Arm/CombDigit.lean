module

public import VerifiedGarbage.Impl.Ed25519.Arm.Comb
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X25519.Arm.Setup

/-!
# The ARMv7 comb's digits

Digit `i` of the scalar at `p` is the nibble `n` of byte `i / 2` (its high nibble for odd
`i`), `nibAt`; `combDigit` leaves the mask of its sign (all ones for `n < 8`) at byte `SGN`
of the workspace, and in `r1`–`r8` the masks of the magnitudes `1 … 8` of `n - 8`, all ones
exactly for `magOf n` (`combDigit_ok`). The bit arithmetic is checked by `decide` over the
256 bytes, the 16 nibbles and the 9 magnitudes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- Digit `i`'s nibble of the scalar at `p`. -/
def nibAt (m : Mem) (p : Addr) (i : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_lt (m : Mem) (p : Addr) (i : Nat) : nibAt m p i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def magOf (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem magOf_le {n : Nat} (hn : n < 16) : magOf n ≤ 8 := by
  unfold magOf; split <;> omega

/-- All ones for `true`, zero for `false`. -/
def maskB (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

private theorem counter_fact : ∀ i < 64,
    BitVec.ofNat 32 i >>> 1 = BitVec.ofNat 32 (i / 2) ∧
      (BitVec.ofNat 32 i &&& (1 : BitVec 32)) = BitVec.ofNat 32 (i % 2) := by decide

private theorem nibble_fact : ∀ v < 256, ∀ o < 2,
    (BitVec.ofNat 32 v &&& (15 : BitVec 32)) ^^^
        ((BitVec.ofNat 32 v >>> 4 ^^^ (BitVec.ofNat 32 v &&& (15 : BitVec 32))) &&&
          ((0 : BitVec 32) - BitVec.ofNat 32 o)) =
      BitVec.ofNat 32 (v / 16 ^ o % 16) := by decide +kernel

private theorem sign_fact : ∀ n < 16,
    (0 : BitVec 32) - ((BitVec.ofNat 32 n - (8 : BitVec 32)) >>> 31) = maskB (decide (n < 8)) ∧
      ((BitVec.ofNat 32 n - (8 : BitVec 32)) ^^^ maskB (decide (n < 8))) - maskB (decide (n < 8)) =
        BitVec.ofNat 32 (magOf n) := by decide

private theorem mask_fact : ∀ a ≤ 8, ∀ k < 8,
    (0 : BitVec 32) - (((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 (k + 1)) - (1 : BitVec 32)) >>> 31) =
      maskB (decide (a = k + 1)) := by decide

private theorem enc_fact : ∀ k < 8, encodable (BitVec.ofNat 32 (k + 1)) = true := by decide

private theorem maskReg_fact : ∀ k < 8,
    maskReg (k + 1) ≠ .r9 ∧ maskReg (k + 1) ≠ .r10 ∧
      maskReg (k + 1) ∈ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] := by decide

private theorem maskReg_ne : ∀ k < 8, ∀ k' < 8, k' ≠ k → maskReg (k' + 1) ≠ maskReg (k + 1) := by
  decide

/-- The masks of the magnitudes, from the magnitude `a` in `r10` and zero in `r9`. -/
structure MaskInv (s₀ : State) (a : Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s₀ s
  mem : s.mem = s₀.mem
  masks : ∀ k' < k, s.gpr (maskReg (k' + 1)) = maskB (decide (a = k' + 1))

theorem combMasks_ok {s₀ : State} {a : Nat} (ha : a ≤ 8) (h9 : s₀.gpr .r9 = 0)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 32 a) :
    WP isa (.block ((List.range 8).flatMap fun k => combMask (k + 1))) s₀ (MaskInv s₀ a 8) := by
  refine wp_range_flatMap (M := isa) (MaskInv s₀ a) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have m := maskReg_fact k hk
  have g9 : s.gpr .r9 = 0 := (h.rest.gpr _ (by decide)).trans h9
  have g10 : s.gpr .r10 = BitVec.ofNat 32 a := (h.rest.gpr _ (by decide)).trans h10
  unfold combMask
  refine wp_dp (op2_imm (enc_fact k hk)) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have hr : ∀ {t t' : State} {v : BitVec 32}, Upd t t' (maskReg (k + 1)) v →
      Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] t t' := fun u => u.rest m.2.2
  refine ⟨h.rest.trans ((hr u₁).trans ((hr u₂).trans ((hr u₃).trans (hr u₄)))), ?_, fun k' hk' => ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · have ne := maskReg_ne k hk k' (by omega) (by omega)
      rw [u₄.other _ ne, u₃.other _ ne, u₂.other _ ne, u₁.other _ ne]
      exact h.masks k' hk'
    · rw [u₄.gpr, dpVal, u₃.other _ m.1.symm, u₂.other _ m.1.symm, u₁.other _ m.1.symm, g9, u₃.gpr,
        u₂.gpr, dpVal, u₁.gpr, dpVal, g10]
      exact mask_fact a ha k' hk

theorem combDigit_ok {b p : BitVec 32} {s : State} (hc : Ctx b s) {i : Nat} (hi : i < 64)
    (hp : b + BitVec.ofNat 32 SCAL = p)
    (h11 : s.gpr .r11 = BitVec.ofNat 32 i) (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 (i / 2)) 1) :
    WP isa (.block combDigit) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] s t ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 SGN)
        (maskB (decide (nibAt s.mem (State.addr p) i < 8))) ∧
      t.gpr .r9 = 0 ∧ t.gpr .r10 = BitVec.ofNat 32 (magOf (nibAt s.mem (State.addr p) i)) ∧
      ∀ k < 8, t.gpr (maskReg (k + 1)) = maskB (decide (magOf (nibAt s.mem (State.addr p) i) = k + 1)) := by
  have cf := counter_fact i hi
  unfold combDigit
  rw [WP.block_append_iff]
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have e3 : s₃.gpr .r12 = p + BitVec.ofNat 32 (i / 2) := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, dpVal, hc.r0, hp, u₂.gpr, u₁.other _ (by decide), h11, cf.1]
  have r3 : Rest [.r2, .r12] s s₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m3 : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  let a := State.addr p + BitVec.ofNat 64 (i / 2)
  refine wp_ldrb (a := a) (by decide)
    (by rw [e3]; exact (congrArg State.addr (BitVec.add_zero _)).trans (addr_add (by omega)))
    (by rw [r3.rd, r3.wr]; exact hr) fun s₄ u₄ => ?_
  have v_lt := (s.mem a).isLt
  have e4 : s₄.gpr .r3 = BitVec.ofNat 32 (s.mem a).toNat := by
    rw [u₄.gpr, m3]
    exact BitVec.eq_of_toNat_eq (by rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_lsr (by decide)) fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => wp_dp (op2_imm (by decide)) fun s₈ u₈ =>
    wp_dp (op2_reg _ _) fun s₉ u₉ => wp_dp (op2_reg _ _) fun s₁₀ u₁₀ =>
    wp_dp (op2_reg _ _) fun s₁₁ u₁₁ => wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  -- The nibble, in `r4`.
  have e12 : s₁₂.gpr .r4 = BitVec.ofNat 32 (nibAt s.mem (State.addr p) i) := by
    simp (disch := decide) only [u₁₂.gpr, dpVal, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other,
      u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, e4,
      u₄.other, u₃.other, u₂.other, u₁.other, h11, cf.2]
    exact nibble_fact _ v_lt _ (Nat.mod_lt _ (by decide))
  have g9 : s₁₂.gpr .r9 = 0 := by
    simp (disch := decide) only [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.gpr]
  have r12 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r12] s s₁₂ :=
    (r3.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
      ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans ((u₁₁.rest (by decide)).trans
      (u₁₂.rest (by decide))))))))))
  have m12 : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m3]
  -- The sign and the magnitude.
  have sf := sign_fact _ (nibAt_lt s.mem (State.addr p) i)
  refine wp_dp (op2_imm (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_lsr (by decide)) fun s₁₄ u₁₄ =>
    wp_dp (op2_reg _ _) fun s₁₅ u₁₅ => ?_
  have r15 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r12] s s₁₅ :=
    r12.trans ((u₁₃.rest (by decide)).trans ((u₁₄.rest (by decide)).trans (u₁₅.rest (by decide))))
  refine str0_ok (hc.of_rest r15 (by decide)) (by decide)
      fun s₁₆ u₁₆ => wp_dp (op2_reg _ _) fun s₁₇ u₁₇ => wp_dp (op2_reg _ _) fun s₁₈ u₁₈ => ?_
  have g15 : s₁₅.gpr .r5 = maskB (decide (nibAt s.mem (State.addr p) i < 8)) := by
    simp (disch := decide) only [u₁₅.gpr, dpVal, u₁₄.gpr, u₁₄.other, u₁₃.gpr,
      u₁₃.other, g9, e12]
    exact sf.1
  have g18 : s₁₈.gpr .r10 = BitVec.ofNat 32 (magOf (nibAt s.mem (State.addr p) i)) := by
    simp (disch := decide) only [u₁₈.gpr, dpVal, u₁₇.gpr, u₁₇.other, u₁₆.gpr, g15,
      u₁₅.other, u₁₄.other, u₁₃.gpr, e12]
    exact sf.2
  have g9' : s₁₈.gpr .r9 = 0 := by
    simp (disch := decide) only [u₁₈.other, u₁₇.other, u₁₆.gpr, u₁₅.other, u₁₄.other, u₁₃.other, g9]
  have m18 : s₁₈.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 SGN)
      (maskB (decide (nibAt s.mem (State.addr p) i < 8))) := by
    rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, g15, u₁₅.mem, u₁₄.mem, u₁₃.mem, m12]
  have r18 : Rest [.r2, .r3, .r4, .r5, .r6, .r9, .r10, .r12] s s₁₈ :=
    (r15.mono (by decide)).trans ((u₁₆.rest _).trans ((u₁₇.rest (by decide)).trans
      (u₁₈.rest (by decide))))
  refine WP.block_nil (WP.mono (combMasks_ok (magOf_le (nibAt_lt _ _ _)) g9' g18) fun t h => ?_)
  refine ⟨(r18.mono (by decide)).trans (h.rest.mono (by decide)), h.mem.trans m18,
    (h.rest.gpr _ (by decide)).trans g9', (h.rest.gpr _ (by decide)).trans g18, h.masks⟩

end VG.Proof.Ed25519.Arm
