module

public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Contracts with tables of constants (x86-64)

A function that reads tables of constants `cs` where the statics are has
its contract under `abi.withConsts cs`, whose readable regions end with the
tables' (`Abi.constRegions`). A caller that knows only that the tables are
held in memory, apart from what it passes, proves the contract's
precondition from the plain one, on the state without the tables' regions
(`withConsts_pre`), whatever `cs` is; and the postcondition and public data
are those of the plain contract, with the tables at the same addresses
(`withConsts_post`, `withConsts_pub`).
-/

@[expose] public section

namespace VG.X86_64.WithConsts

theorem constRegions_length (f : String → BitVec 64) (cs : List (String × List (BitVec 64))) :
    (Abi.constRegions f cs).length = cs.length := List.length_map _

/-- The arguments a contract reads, which do not depend on the regions. -/
theorem abi_args (ws : List Nat) :
    ∃ vals, abi.args ws = some vals ∧ ∀ (s : State) r w, vals (s.withRegions r w) = vals s := by
  simp only [abi]; split <;> exact ⟨_, rfl, fun _ _ _ => rfl⟩

section
variable (c : String × List (BitVec 64)) (cs : List (String × List (BitVec 64)))

theorem withConsts_args : (abi.withConsts (c :: cs)).args = abi.args := rfl
theorem withConsts_ptrBits (cs : List (String × List (BitVec 64))) : (abi.withConsts cs).ptrBits = 64 := by
  cases cs <;> rfl
theorem withConsts_mem : (abi.withConsts (c :: cs)).mem = abi.mem := rfl
theorem withConsts_wr : (abi.withConsts (c :: cs)).wr = abi.wr := rfl
theorem withConsts_argArea : (abi.withConsts (c :: cs)).argArea = abi.argArea := rfl
theorem withConsts_reserved : (abi.withConsts (c :: cs)).reserved = abi.reserved := rfl
theorem withConsts_rd (s : State) :
    (abi.withConsts (c :: cs)).rd s = s.rd.take (s.rd.length - (c :: cs).length) := rfl
theorem withConsts_wf (ws : List Nat) (n : Nat) (s : State) :
    (abi.withConsts (c :: cs)).wf ws n s = (abi.wf ws n s ∧
      s.rd.drop (s.rd.length - (c :: cs).length) = Abi.constRegions s.syms (c :: cs) ∧
      Abi.constsHeld s.mem s.syms (c :: cs) ∧
      ∀ t ∈ Abi.constRegions s.syms (c :: cs), t.base.toNat + t.len ≤ 2 ^ 64 ∧
        (∀ r ∈ s.wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s, t.Disjoint r) := rfl
theorem withConsts_pub (s₁ s₂ : State) :
    (abi.withConsts (c :: cs)).pub s₁ s₂ =
      (abi.pub s₁ s₂ ∧ ∀ x ∈ c :: cs, s₁.syms x.1 = s₂.syms x.1) := rfl
end

theorem wf_withRegions (ws : List Nat) (n : Nat) (s : State) (r w : List Region) :
    abi.wf ws n (s.withRegions r w) = abi.wf ws n s := rfl
theorem argArea_withRegions (ws : List Nat) (s : State) (r w : List Region) :
    abi.argArea ws (s.withRegions r w) = abi.argArea ws s := rfl
theorem reserved_withRegions (n : Nat) (s : State) (r w : List Region) :
    abi.reserved n (s.withRegions r w) = abi.reserved n s := rfl

/-- The precondition of a contract under `abi.withConsts cs`, of a state
whose readable regions are `rd₀` and then the tables', from the plain
contract's on the state with `rd₀` alone, when the tables are held and apart
from the writable regions and the stack. -/
theorem withConsts_pre {sig : Sig} {pre : ∀ pb, Curry (sig.words pb) (Mem → Prop)}
    {post : ∀ pb, sig.Post pb} {wa : Bool} {n : Nat}
    {cs : List (String × List (BitVec 64))} {s : State} {rd₀ : List Region}
    (hrd : s.rd = rd₀ ++ Abi.constRegions s.syms cs) (held : Abi.constsHeld s.mem s.syms cs)
    (hreg : ∀ t ∈ Abi.constRegions s.syms cs, t.base.toNat + t.len ≤ 2 ^ 64 ∧
      (∀ r ∈ s.wr, t.Disjoint r) ∧ ∀ r ∈ abi.reserved n s, t.Disjoint r)
    (h : (sig.contract abi (pre abi.ptrBits) (post abi.ptrBits) wa n).pre (s.withRegions rd₀ s.wr)) :
    (sig.contract (abi.withConsts cs) (pre (abi.withConsts cs).ptrBits) (post (abi.withConsts cs).ptrBits)
      wa n).pre s := by
  cases cs with
  | nil =>
    simp only [Abi.constRegions, List.map_nil, List.append_nil] at hrd
    rw [← hrd, State.withRegions_self] at h
    exact h
  | cons c cs =>
    have hl : (rd₀ ++ Abi.constRegions s.syms (c :: cs)).length - (c :: cs).length = rd₀.length := by
      rw [List.length_append, constRegions_length]; omega
    obtain ⟨vals, hv, hvw⟩ := abi_args ((sig.words 64).map (·.bits 64))
    simp only [Sig.contract, withConsts_args, withConsts_rd, withConsts_wf, withConsts_wr,
      withConsts_mem, withConsts_argArea, withConsts_reserved] at h ⊢
    rw [show abi.ptrBits = 64 from rfl] at h
    rw [show (abi.withConsts (c :: cs)).ptrBits = 64 from rfl]
    simp only [hv] at h ⊢
    simp only [hvw, wf_withRegions, argArea_withRegions, reserved_withRegions] at h
    obtain ⟨hwf, hr, hw, hp, hres, hb, hpre⟩ := h
    refine ⟨⟨hwf, ?_, held, hreg⟩, ?_, hw, hp, hres, hb, hpre⟩
    · rw [hrd, hl, List.drop_left]
    · rw [hrd, hl, List.take_left]; exact hr

/-- The postcondition of a contract under `abi.withConsts cs` is the plain
contract's. -/
theorem withConsts_post {sig : Sig} {pre : ∀ pb, Curry (sig.words pb) (Mem → Prop)}
    {post : ∀ pb, sig.Post pb} {wa : Bool} {n : Nat} {cs : List (String × List (BitVec 64))} {s s' : State}
    (h : (sig.contract (abi.withConsts cs) (pre (abi.withConsts cs).ptrBits)
      (post (abi.withConsts cs).ptrBits) wa n).post s s') :
    (sig.contract abi (pre abi.ptrBits) (post abi.ptrBits) wa n).post s s' := by
  cases cs with
  | nil => exact h
  | cons c cs => exact h

/-- The public data of a contract under `abi.withConsts cs`, from the plain
contract's, for states naming the statics at the same addresses. -/
theorem withConsts_pub' {sig : Sig} {pre : ∀ pb, Curry (sig.words pb) (Mem → Prop)}
    {post : ∀ pb, sig.Post pb} {wa : Bool} {n : Nat} {cs : List (String × List (BitVec 64))}
    {s₁ s₂ : State} (hsy : s₁.syms = s₂.syms)
    (h : (sig.contract abi (pre abi.ptrBits) (post abi.ptrBits) wa n).pub s₁ s₂) :
    (sig.contract (abi.withConsts cs) (pre (abi.withConsts cs).ptrBits) (post (abi.withConsts cs).ptrBits)
      wa n).pub s₁ s₂ := by
  cases cs with
  | nil => exact h
  | cons c cs =>
    obtain ⟨vals, hv, -⟩ := abi_args ((sig.words 64).map (·.bits 64))
    simp only [Sig.contract, withConsts_args, withConsts_pub] at h ⊢
    rw [show abi.ptrBits = 64 from rfl] at h
    rw [show (abi.withConsts (c :: cs)).ptrBits = 64 from rfl]
    simp only [hv] at h ⊢
    obtain ⟨hp, hpub, hd⟩ := h
    exact ⟨⟨hp, fun x _ => by rw [hsy]⟩, hpub, hd⟩

end VG.X86_64.WithConsts
