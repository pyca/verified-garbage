module

public import VerifiedGarbage.Impl.Dispatch.X86
public import VerifiedGarbage.Proof.Framework.Dispatch

/-!
# Choosing code by a public selector on x86 (32-bit): proofs

The tests of `Dispatch.X86.chain r` (`cmp r, k`) for keys below `2^31`
(`tests r`): each leaks nothing, sets `ZF` to whether `r` is `k`, and
changes only the flags (`FlagsOnly`), so `Dispatch.chain_wp`, `chain_exec`
and `chain_relCT` apply with the selector `r`.
-/

@[expose] public section

namespace VG.Proof.Dispatch.X86

open VG.X86 VG.Impl.Dispatch.X86

/-- The selector: the register `r`. -/
def sel (r : Reg) (s : State) : Nat := (s.gpr r).toNat

/-- `s'` is `s` with other flags. -/
def FlagsOnly (s s' : State) : Prop := ∃ c o z f, s' = s.setFlags c o z f

theorem FlagsOnly.refl (s : State) : FlagsOnly s s := ⟨s.cf, s.of, s.zf, s.sf, rfl⟩

theorem FlagsOnly.trans {a b c : State} (h₁ : FlagsOnly a b) (h₂ : FlagsOnly b c) : FlagsOnly a c := by
  obtain ⟨_, _, _, _, rfl⟩ := h₁
  obtain ⟨c', o', z', f', rfl⟩ := h₂
  exact ⟨c', o', z', f', rfl⟩

theorem FlagsOnly.gpr {s s' : State} (h : FlagsOnly s s') (r : Reg) : s'.gpr r = s.gpr r := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.mem {s s' : State} (h : FlagsOnly s s') : s'.mem = s.mem := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.rd {s s' : State} (h : FlagsOnly s s') : s'.rd = s.rd := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.wr {s s' : State} (h : FlagsOnly s s') : s'.wr = s.wr := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.syms {s s' : State} (h : FlagsOnly s s') : s'.syms = s.syms := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

/-- `cmp r, k`, for `k < 2^31`. -/
theorem tests (r : Reg) : Proof.Dispatch.Tests (M := isa) (test r) Cond.e (sel r) FlagsOnly (2 ^ 31) where
  step k hk s := by
    refine ⟨_, rfl, ?_, ⟨_, _, _, _, rfl⟩, rfl⟩
    simp only [eval, arithFlags, State.setFlags]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.sub_eq_iff_eq_add,
      show (0 : BitVec 32) + BitVec.ofNat 32 k = BitVec.ofNat 32 k from BitVec.zero_add _]
    show _ ↔ (s.gpr r).toNat = k
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat]; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega
  refl := FlagsOnly.refl
  trans := FlagsOnly.trans

end VG.Proof.Dispatch.X86
