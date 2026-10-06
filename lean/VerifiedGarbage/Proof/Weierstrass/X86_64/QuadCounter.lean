import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-!
# A public counter for pairs of window doublings

The low 12 bits of `rbx` retain the window index; the next bits count the
two pairs. Subtracting 4096 consumes one pair. Comparing with 4096 sets
carry exactly when the inner count reaches zero, leaving the index intact.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

/-- Add the two-pair count to the window index. -/
theorem quadStart_ok (s : State) {i : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .rbx (.imm 8192)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * 2) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left', hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e : (8192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8192 := by decide
    rw [e, ← BitVec.ofNat_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Consume one pair, setting carry when only the window index remains. -/
theorem quadCount_ok (s : State) {i j : Nat} (hi : i < 4096) (hj : 1 ≤ j) (hj' : j ≤ 2)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j)) :
    WP isa (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * (j - 1)) ∧
      s'.cf = some (decide (j - 1 = 0)) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', hb]
  have e : (4096 : BitVec 32).signExtend 64 = BitVec.ofNat 64 4096 := by decide
  have sub : BitVec.ofNat 64 (i + 4096 * j) - (4096 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (i + 4096 * (j - 1)) := by
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨sub, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [sub]
    rw [e]
    congr 1
    simp only [BitVec.toNat_ofNat]
    apply propext
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Run two pairs, branching while the public inner count remains nonzero. -/
theorem quadLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop}
    (hstep : ∀ j s, 1 ≤ j → j ≤ 2 → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.cf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) {s : State} (hs : Inv 2 s) :
    WP isa (.loop body .ae) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ 2 ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) 2 s
    ⟨by decide, by decide, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hc⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.cf.map (!·) = some false
    rw [hc, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show s'.cf.map (!·) = some true
    rw [hc]; simp [hj]

end VG.Proof.Weierstrass.X86_64
