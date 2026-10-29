module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops

/-!
# Streaming RC2-CBC on RISCV64: `init`'s checks

`checks_run`: `t0` is zero exactly if the lengths are valid, and otherwise
`a0` holds the code of the first invalid one.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream

theorem bne_zero_toNat (y : BitVec 64) : (y != (0 : BitVec 64)) = !decide (y.toNat = 0) := by
  have := ofNat_bne_zero' (y.isLt)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem range_bne {x b : Nat} (hx : x < 2 ^ 64) (hb : b < 64) :
    ((BitVec.ofNat 64 x - 1#64) >>> b != (0 : BitVec 64)) = !decide (1 ≤ x ∧ x ≤ 2 ^ b) := by
  rw [bne_zero_toNat]
  congr 1
  have hp : 2 ^ b ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx]
  apply decide_eq_decide.mpr
  rw [Nat.div_eq_zero_iff]
  by_cases h : x = 0
  · subst h; omega
  · rw [show (2 ^ 64 - 1 % 2 ^ 64 + x) % 2 ^ 64 = x - 1 by omega]; omega

/-- The code `checks` leaves in `a0` for invalid lengths. -/
def errCode (keyLen bits : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1 else if ¬(1 ≤ bits ∧ bits ≤ 1024) then 2 else 3

/-- Valid lengths. -/
def valid (keyLen bits ivLen : Nat) : Prop := (1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ bits ∧ bits ≤ 1024) ∧ ivLen = 8

instance (a b c : Nat) : Decidable (valid a b c) := by unfold valid; infer_instance

theorem checks_run (s : State) :
    WP isa checks s fun t => t.mem = s.mem ∧ Keep [.a0, .t0] s t ∧
      (t.gpr .t0 != (0 : BitVec 64)) = !decide (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat) ∧
      (¬valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat →
        t.gpr .a0 = BitVec.ofNat 64 (errCode (s.gpr .a1).toNat (s.gpr .a2).toNat)) ∧
      (valid (s.gpr .a1).toNat (s.gpr .a2).toNat (s.gpr .a4).toNat → t.gpr .a0 = s.gpr .a0) := by
  have e4 := (BitVec.ofNat_toNat 64 (s.gpr .a1)).trans (BitVec.setWidth_eq _)
  have e5 := (BitVec.ofNat_toNat 64 (s.gpr .a2)).trans (BitVec.setWidth_eq _)
  have e7 := (BitVec.ofNat_toNat 64 (s.gpr .a4)).trans (BitVec.setWidth_eq _)
  unfold checks
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a1 (-1), .shift .srl .d .t0 .t0 7]) (Q := fun t =>
      t.gpr .t0 = (s.gpr .a1 - 1#64) >>> 7 ∧ t.mem = s.mem) (by rrun)
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have c₁ := range_bne (x := (s.gpr .a1).toNat) (b := 7) (s.gpr .a1).isLt (by decide)
  rw [e4] at c₁
  refine WP.ite _ (by rw [Steps.eval_nonzero, a₁, c₁]) (fun h => ?_) (fun h => ?_)
  · have hk : ¬(1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128) := by simp at h; omega
    refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 1]) (Q := fun t => t.gpr .a0 = 1#64 ∧ t.mem = t₁.mem)
      (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
      ⟨by rw [m, m₁], (k₁.trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.1 hk⟩
    · rw [k.gpr (by decide), a₁, c₁]
      simp [valid, hk]
    · rw [a]; simp [errCode, hk]
  · have hk : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 128 := by simpa using h
    apply WP.seq
    refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a2 (-1), .shift .srl .d .t0 .t0 10]) (Q := fun t =>
        t.gpr .t0 = (s.gpr .a2 - 1#64) >>> 10 ∧ t.mem = t₁.mem) (by rrun [k₁.gpr (show Reg.a2 ∉ [Reg.t0] by decide)])
      (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
    have c₂ := range_bne (x := (s.gpr .a2).toNat) (b := 10) (s.gpr .a2).isLt (by decide)
    rw [e5] at c₂
    refine WP.ite _ (by rw [Steps.eval_nonzero, a₂, c₂]) (fun h => ?_) (fun h => ?_)
    · have hb : ¬(1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024) := by simp at h; omega
      refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 2]) (Q := fun t => t.gpr .a0 = 2#64 ∧ t.mem = t₂.mem)
        (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
        ⟨by rw [m, m₂, m₁], ((k₁.trans k₂).trans k).mono (by simp), ?_, fun _ => ?_, fun hv => absurd hv.2.1 hb⟩
      · rw [k.gpr (by decide), a₂, c₂]
        simp [valid, hb]
      · rw [a]; simp [errCode, hk, hb]
    · have hb : 1 ≤ (s.gpr .a2).toNat ∧ (s.gpr .a2).toNat ≤ 1024 := by simpa using h
      apply WP.seq
      refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a4 (-8)]) (Q := fun t =>
          t.gpr .t0 = s.gpr .a4 - 8#64 ∧ t.mem = t₂.mem)
        (by rrun [k₂.gpr (show Reg.a4 ∉ [Reg.t0] by decide), k₁.gpr (show Reg.a4 ∉ [Reg.t0] by decide)])
        (by rfl) rfl) fun t₃ ⟨⟨a₃, m₃⟩, k₃⟩ => ?_
      have c₃ := sub_bne (x := (s.gpr .a4).toNat) (y := 8) (s.gpr .a4).isLt (by decide)
      rw [e7] at c₃
      refine WP.ite _ (by rw [Steps.eval_nonzero, a₃, c₃]) (fun h => ?_) (fun h => ?_)
      · have hi : (s.gpr .a4).toNat ≠ 8 := by simpa using h
        refine WP.mono (WP.keep [.a0] (c := .block [.li .a0 3]) (Q := fun t => t.gpr .a0 = 3#64 ∧ t.mem = t₃.mem)
          (by rrun) (by rfl) rfl) fun t ⟨⟨a, m⟩, k⟩ =>
          ⟨by rw [m, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k).mono (by simp), ?_, fun _ => ?_,
            fun hv => absurd hv.2.2 hi⟩
        · rw [k.gpr (by decide), a₃, c₃]
          simp [valid, hi]
        · rw [a]; simp [errCode, hk, hb]
      · have hi : (s.gpr .a4).toNat = 8 := by simpa using h
        refine WP.block_nil ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp), ?_, fun hv => ?_,
          fun _ => by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]⟩
        · rw [a₃, c₃]; simp [valid, hk, hb, hi]
        · exact absurd ⟨hk, hb, hi⟩ hv

end VG.Proof.Rc2.RISCV64.Stream
