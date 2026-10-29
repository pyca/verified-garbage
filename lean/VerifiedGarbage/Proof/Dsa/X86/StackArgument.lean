module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer

/-! # Caller stack arguments remain readable while the header is installed -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

def stackAddress (s : State) (i : Nat) : Addr := addr (s.gpr .esp) (4 + 4 * i)
def stackValue (s : State) (i : Nat) : BitVec 32 := s.mem.readW (stackAddress s i) 32

structure StackArgument (s : State) (base : Addr) (size i : Nat) : Prop where
  read : InRegions (s.rd ++ s.wr) (stackAddress s i) 4
  apart : Region.Disjoint ⟨stackAddress s i, 4⟩ ⟨base, size⟩

theorem StackArgument.readSrc {s : State} {base : Addr} {size i : Nat}
    (A : StackArgument s base size i) : readSrc s (.mem (Entry.argument i)) = some (stackValue s i) :=
  readSrc_mem rfl A.read

theorem StackArgument.keep {s t : State} {base : Addr} {size i : Nat} {regs : List Reg}
    (A : StackArgument s base size i) (K : Keeps regs s t) (hsp : .esp ∉ regs) :
    StackArgument t base size i := by
  have P : stackAddress t i = stackAddress s i := by simp only [stackAddress, K.1 _ hsp]
  exact ⟨by rw [K.2.1, K.2.2, P]; exact A.read, by rw [P]; exact A.apart⟩

theorem StackArgument.value_keep {s t : State} {base : Addr} {size i : Nat} {regs : List Reg}
    (A : StackArgument s base size i) (K : Keeps regs s t) (hsp : .esp ∉ regs)
    (O : Outside base 0 size s.mem t.mem) : stackValue t i = stackValue s i := by
  unfold stackValue
  rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, K.1 _ hsp]]
  apply Mem.readW_congr
  intro j hj
  have H := A.apart (stackAddress s i + BitVec.ofNat 64 j)
    (Offset.contains_base _ (by omega) (by omega))
  change ¬ (ofs base (stackAddress s i + BitVec.ofNat 64 j) + 1 ≤ size) at H
  exact O _ (.inr (by omega))

end VG.Proof.Dsa.X86
