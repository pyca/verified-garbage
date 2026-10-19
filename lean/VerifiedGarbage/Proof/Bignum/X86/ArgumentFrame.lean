module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Dsa.Frame

/-! # Cdecl arguments remain fixed across disjoint output writes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (stackAddress stackValue)

theorem CallArgument.frame {s t : State} {base : Addr} {bytes i : Nat} {v : BitVec 32}
    {rs : List Region} {regs : List Reg} (h : CallArgument s base bytes i v)
    (rest : Keeps regs s t) (sp : .esp ∉ regs) (frame : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨stackAddress s i, 4⟩ r) :
    CallArgument t base bytes i v := by
  refine ⟨h.stack.keep rest sp, ?_⟩
  unfold stackValue
  rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, rest.1 _ sp]]
  rw [frame.readW (r := ⟨stackAddress s i, 4⟩) (a := stackAddress s i) (w := 32)
    (by simpa using Offset.contains_base (stackAddress s i) (d := 0) (n := 4) (k := 4) (by decide) (by decide)) apart (by decide)]
  exact h.value
end VG.Proof.Bignum.X86
