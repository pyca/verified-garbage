module

public import VerifiedGarbage.Impl.Dispatch.X86_64
public import VerifiedGarbage.Proof.Framework.Dispatch
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-!
# Choosing code by a public selector on x86-64: proofs

The tests of `Dispatch.X86_64.chain` (`cmp rax, k`) for keys below `2^31`
(`tests`): each leaks nothing, sets `ZF` to whether `rax` is `k`, and
changes only the flags (`FlagsOnly`), so `Dispatch.chain_wp`,
`chain_exec` and `chain_relCT` apply with the selector `rax`; the chain's
calls nest as deep as its cases' (`chain_depth`, `chain_x86_64Depth`).
-/

@[expose] public section

namespace VG.Proof.Dispatch.X86_64

open VG.X86_64 VG.Impl.Dispatch.X86_64

/-- The selector: `rax`. -/
def sel (s : State) : Nat := (s.gpr .rax).toNat

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

/-- `cmp rax, k`, for `k < 2^31`. -/
theorem tests : Proof.Dispatch.Tests (M := isa) test Cond.e sel FlagsOnly (2 ^ 31) where
  step k hk s := by
    refine ⟨_, rfl, ?_, ⟨_, _, _, _, rfl⟩, rfl⟩
    have hm : (BitVec.ofNat 32 k).msb = false := by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hs : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
      rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    simp only [eval, State.setFlags, arithFlags, hs]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 64) + BitVec.ofNat 64 k = BitVec.ofNat 64 k from BitVec.zero_add _]
    show _ ↔ (s.gpr .rax).toNat = k
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat]; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega
  refl := FlagsOnly.refl
  trans := FlagsOnly.trans

/-- The calls of the chain nest as deep as those of its cases. -/
theorem chain_depth {n : Nat} : ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, c.2.depth ≤ n) → (chain cs).depth ≤ n
  | [], _ => Nat.zero_le _
  | [(_, c)], h => h _ List.mem_cons_self
  | (k, c) :: c' :: cs, h => by
    have h₁ : c.depth ≤ n := h _ List.mem_cons_self
    have h₂ := chain_depth (c' :: cs) fun c hc => h c (List.mem_cons_of_mem _ hc)
    show max 0 (max c.depth (chain (c' :: cs)).depth) ≤ n
    omega

/-- The stack the chain's calls and frames use is the most its cases' use. -/
theorem chain_x86_64Depth {n : Nat} : ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, c.2.x86_64Depth ≤ n) →
    (chain cs).x86_64Depth ≤ n
  | [], _ => Nat.zero_le _
  | [(_, c)], h => h _ List.mem_cons_self
  | (k, c) :: c' :: cs, h => by
    have h₁ : c.x86_64Depth ≤ n := h _ List.mem_cons_self
    have h₂ := chain_x86_64Depth (c' :: cs) fun c hc => h c (List.mem_cons_of_mem _ hc)
    show max 0 (max c.x86_64Depth (chain (c' :: cs)).x86_64Depth) ≤ n
    omega

end VG.Proof.Dispatch.X86_64
