module

public import VerifiedGarbage.Impl.Dispatch.AArch64
public import VerifiedGarbage.Proof.Framework.Dispatch

/-!
# Choosing code by a public selector on AArch64: proofs

The tests of `Dispatch.AArch64.chain t r` (`sub t, r, #k`), for keys below
4096 and `t ≠ r` (`tests`): each leaks nothing, makes `t` zero exactly when
`r` is `k`, and writes only `t` (`WritesOnly`), so `Dispatch.chain_wp`,
`chain_exec` and `chain_relCT` apply with the selector `r`.
-/

@[expose] public section

namespace VG.Proof.Dispatch.AArch64

open VG.AArch64 VG.Impl.Dispatch.AArch64

/-- The selector: the register `r`. -/
def sel (r : Reg) (s : State) : Nat := (s.gpr r).toNat

/-- `s'` is `s` with another value in the register `t`. -/
def WritesOnly (t : Reg) (s s' : State) : Prop := ∃ v, s' = s.write .x t v

theorem WritesOnly.refl (t : Reg) (s : State) : WritesOnly t s s := by
  refine ⟨s.gpr t, ?_⟩
  cases s; simp only [State.write, State.mk.injEq, and_true]
  funext r'; split <;> simp_all

theorem WritesOnly.trans {t : Reg} {a b c : State} (h₁ : WritesOnly t a b) (h₂ : WritesOnly t b c) :
    WritesOnly t a c := by
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  refine ⟨v₂, ?_⟩
  simp only [State.write]
  congr 1; funext r'; split <;> rfl

theorem WritesOnly.gpr {t : Reg} {s s' : State} (h : WritesOnly t s s') {r : Reg} (hr : r ≠ t) :
    s'.gpr r = s.gpr r := by
  obtain ⟨_, rfl⟩ := h; simp only [State.write, hr, ite_false]

theorem WritesOnly.mem {t : Reg} {s s' : State} (h : WritesOnly t s s') : s'.mem = s.mem := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- `sub t, r, #k`, for `k < 4096` and `t ≠ r`. -/
theorem tests (t r : Reg) (h : t ≠ r) :
    Proof.Dispatch.Tests (M := isa) (test t r) (.zero .x t) (sel r) (WritesOnly t) 4096 where
  step k hk s := by
    refine ⟨_, by simp only [test, execBlock, isa, exec, hk, ite_true, addrs]; rfl, ?_, ⟨_, rfl⟩, ?_⟩
    · simp only [eval, State.read, State.write, ite_true]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      show _ ↔ (s.gpr r).toNat = k
      simp only [Size.bits, BitVec.setWidth_eq]
      rw [BitVec.sub_eq_iff_eq_add, show (0 : BitVec 64) + BitVec.ofNat 64 k = BitVec.ofNat 64 k from BitVec.zero_add _]
      constructor
      · intro e; rw [e, BitVec.toNat_ofNat]; omega
      · intro e; apply BitVec.eq_of_toNat_eq; rw [e, BitVec.toNat_ofNat]; omega
    · simp only [sel, State.write, Ne.symm h, ite_false]
  refl := WritesOnly.refl t
  trans := WritesOnly.trans

end VG.Proof.Dispatch.AArch64
