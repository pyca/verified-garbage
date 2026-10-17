module

public import VerifiedGarbage.Impl.Dispatch.Arm
public import VerifiedGarbage.Proof.Framework.Dispatch

/-!
# Choosing code by a public selector on 32-bit ARM: proofs

The tests of `Dispatch.Arm.chain r` (`cmp r, #k`) for keys below 256
(`tests`): each leaks nothing, sets `Z` to whether `r` is `k`, and changes
only the flags (`FlagsOnly`), so `Dispatch.chain_wp`, `chain_exec` and
`chain_relCT` apply with the selector `r`.
-/

@[expose] public section

namespace VG.Proof.Dispatch.Arm

open VG.Arm VG.Impl.Dispatch.Arm

/-- The selector: the register `r`. -/
def sel (r : Reg) (s : State) : Nat := (s.gpr r).toNat

/-- `s'` is `s` with other flags. -/
def FlagsOnly (s s' : State) : Prop := ∃ n z c v, s' = { s with n := n, z := z, c := c, v := v }

theorem FlagsOnly.refl (s : State) : FlagsOnly s s := ⟨s.n, s.z, s.c, s.v, rfl⟩

theorem FlagsOnly.trans {a b c : State} (h₁ : FlagsOnly a b) (h₂ : FlagsOnly b c) : FlagsOnly a c := by
  obtain ⟨_, _, _, _, rfl⟩ := h₁
  obtain ⟨n', z', c', v', rfl⟩ := h₂
  exact ⟨n', z', c', v', rfl⟩

theorem FlagsOnly.gpr {s s' : State} (h : FlagsOnly s s') (r : Reg) : s'.gpr r = s.gpr r := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.mem {s s' : State} (h : FlagsOnly s s') : s'.mem = s.mem := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.sp {s s' : State} (h : FlagsOnly s s') : s'.sp = s.sp := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.rd {s s' : State} (h : FlagsOnly s s') : s'.rd = s.rd := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.wr {s s' : State} (h : FlagsOnly s s') : s'.wr = s.wr := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.unknowns {s s' : State} (h : FlagsOnly s s') : s'.unknowns = s.unknowns := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

/-- `cmp r, #k`, for `k < 256`. -/
theorem tests (r : Reg) : Proof.Dispatch.Tests (M := isa) (test r) Cond.eq (sel r) FlagsOnly 256 where
  step k hk s := by
    have he : encodable (BitVec.ofNat 32 k) = true := by
      simp only [encodable, List.any_eq_true, List.mem_range, decide_eq_true_eq]
      refine ⟨0, by decide, ?_⟩
      simp [BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (show k % 4294967296 < 2 ^ 32 by omega)]
      omega
    refine ⟨subFlags s (s.gpr r) (BitVec.ofNat 32 k), by
      simp only [test, execBlock, isa, exec, Op2.eval, he, ite_true, addrs]; rfl, ?_, ⟨_, _, _, _, rfl⟩, rfl⟩
    simp only [eval, subFlags]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.sub_eq_iff_eq_add,
      show (0 : BitVec 32) + BitVec.ofNat 32 k = BitVec.ofNat 32 k from BitVec.zero_add _]
    show _ ↔ (s.gpr r).toNat = k
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat]; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega
  refl := FlagsOnly.refl
  trans := FlagsOnly.trans

end VG.Proof.Dispatch.Arm
