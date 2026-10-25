module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Sbox
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# The S-boxes' spills

The S-boxes only store to slots 15–30 of the frame (`spillRegion`), so they
keep the modes' state, the buffer and the registers saved in slots 0–14.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64

def spillRegion (s : State) : Region := ⟨s.gpr sb + BitVec.ofNat 64 120, 128⟩

def spillSafe : Instr → Bool
  | .logic _ d _ _ | .logicImm _ d _ _ | .addi d _ _ | .load .d d _ _ => d != sb
  | .store .d _ n off => decide (n = sb ∧ 120 ≤ off ∧ off + 8 ≤ 248)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem write_frame (s : State) (d : Reg) (v : BitVec 64) (hd : d ≠ sb) :
    (s.write d v).gpr sb = s.gpr sb ∧ Frame [spillRegion s] s.mem (s.write d v).mem :=
  ⟨by simp [State.write, Ne.symm hd], Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : State)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr sb = s.gpr sb ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case logic op d n m =>
    have hd : d ≠ sb := by simpa using h
    simp only [exec, Option.some.injEq] at he
    subst s'
    exact write_frame _ _ _ hd
  case logicImm op d n imm | addi d n imm =>
    have hd : d ≠ sb := by simpa using h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    exact write_frame _ _ _ hd
  case load wd d n off =>
    cases wd <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ sb := by simpa using h
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨a, _, v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case store wd t n off =>
    cases wd <;> simp only [Bool.false_eq_true] at h
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, addr, Width.bytes] at he
    split at he <;> [skip; cases he]
    simp only [Option.bind_some, State.store] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    exact Offset.contains (s.gpr sb) (by omega) (by omega) (by decide)

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr sb = s.gpr sb ∧ Frame [spillRegion s] s.mem s'.mem := by
  induction is generalizing s with
  | nil =>
    rw [runBlock_nil] at he
    obtain rfl := Option.some.inj he
    exact ⟨rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    rw [runBlock_cons] at he
    change (exec i s).bind (runBlock isa is) = some s' at he
    obtain ⟨s₁, hi, hrest⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ h he).2

end VG.Proof.TripleDes.RISCV64
