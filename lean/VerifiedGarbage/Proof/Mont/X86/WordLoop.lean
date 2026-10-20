module

public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Loops over the words of the working space (x86, 32-bit)

`wordLoop_ok` runs `wordLoop k body` from an invariant `P j` that holds
before the body runs with `ebp = edi + 4 j` and that the loop's own
instructions keep: it may not depend on `ebp`, `edx` or the flags.
-/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont

/-- `u'` is `u` but for `ebp`, `edx` and the flags. -/
def LoopRegs (u u' : State) : Prop :=
  u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ ∀ r, r ≠ .ebp → r ≠ .edx → u'.gpr r = u.gpr r

/-- An invariant the loop's own instructions keep. -/
def LoopStable (P : Nat → State → Prop) : Prop :=
  ∀ j u u', P j u → LoopRegs u u' → P j u'

theorem LoopRegs.of_upd_ebp {u u' : State} {v : BitVec 32} (h : Upd u u' .ebp v) : LoopRegs u u' :=
  ⟨h.mem, h.rd, h.wr, fun r h₁ _ => h.other r h₁⟩

theorem LoopRegs.of_upd_edx {u u' : State} {v : BitVec 32} (h : Upd u u' .edx v) : LoopRegs u u' :=
  ⟨h.mem, h.rd, h.wr, fun r _ h₂ => h.other r h₂⟩

theorem LoopRegs.of_fupd {u u' : State} (h : Fupd u u') : LoopRegs u u' :=
  ⟨h.mem, h.rd, h.wr, fun r _ _ => by rw [h.gpr]⟩

theorem LoopRegs.trans {u₁ u₂ u₃ : State} (h₁ : LoopRegs u₁ u₂) (h₂ : LoopRegs u₂ u₃) : LoopRegs u₁ u₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r a b => (h₂.2.2.2 r a b).trans (h₁.2.2.2 r a b)⟩

/-- The loop: `body` runs for `j = 0, …, k - 1` with `ebp = edi + 4 j`,
taking the invariant from `P j` to `P (j + 1)` and keeping `ebp` and `edi`. -/
theorem wordLoop_ok {s : State} {k : Nat} {body : List Instr} (P : Nat → State → Prop)
    {Q : State → Prop} (hk : 0 < k) (hk32 : 4 * k < 2 ^ 32) (hst : LoopStable P) (h0 : P 0 s)
    (hbody : ∀ j < k, ∀ t, P j t → t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * j) →
      WP isa (.block body) t fun u => P (j + 1) u ∧ u.gpr .ebp = t.gpr .ebp ∧ u.gpr .edi = t.gpr .edi)
    (hQ : ∀ u, P k u → Q u) :
    WP isa (wordLoop k body) s Q := by
  unfold wordLoop
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  have p₁ : P 0 s₁ := hst _ _ _ h0 (.of_upd_ebp u₁)
  have e₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * 0) := by
    rw [u₁.gpr, u₁.other _ (by decide)]; exact (BitVec.add_zero _).symm
  refine WP.loop (M := isa) (fun m t => ∃ j, m = k - j ∧ j < k ∧ P j t ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * j)) ?_ k s₁ ⟨0, rfl, hk, p₁, e₁⟩
  rintro m t ⟨j, rfl, hj, pj, ej⟩
  refine WP.block_append (WP.mono (hbody j hj t pj ej) fun u ⟨pu, eu, du⟩ => ?_)
  refine wp_addS rfl fun u₂ v₂ _ => ?_
  refine wp_movS rfl fun u₃ v₃ _ => ?_
  refine wp_addS rfl fun u₄ v₄ _ => ?_
  refine wp_cmpS rfl fun u₅ f₅ z₅ => WP.block_nil ?_
  have R : LoopRegs u u₅ :=
    ((((LoopRegs.of_upd_ebp v₂).trans (.of_upd_edx v₃)).trans (.of_upd_edx v₄)).trans (.of_fupd f₅))
  have p₅ : P (j + 1) u₅ := hst _ _ _ pu R
  have edi₅ : u₅.gpr .edi = t.gpr .edi := by rw [R.2.2.2 _ (by decide) (by decide), du]
  have ebp₄ : u₄.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * j) + 4 := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, eu, ej]
  have edx₄ : u₄.gpr .edx = t.gpr .edi + BitVec.ofNat 32 (4 * k) := by
    rw [v₄.gpr, v₃.gpr, v₂.other _ (by decide), du]
  have ebp₅ : u₅.gpr .ebp = u₅.gpr .edi + BitVec.ofNat 32 (4 * (j + 1)) := by
    rw [edi₅, f₅.gpr, ebp₄, row_ebp]
  rw [ebp₄, edx₄, row_zf _ hj hk32] at z₅
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by simp only [eval, z₅, hjk, decide_true, Option.map_some, Bool.not_true],
      hQ _ (hjk ▸ p₅)⟩
  · exact .inr ⟨by simp only [eval, z₅, hjk, decide_false, Option.map_some, Bool.not_false],
      k - (j + 1), by omega, j + 1, rfl, by omega, p₅, ebp₅⟩

end VG.Proof.Mont.X86
