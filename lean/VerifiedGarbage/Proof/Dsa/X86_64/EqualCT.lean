module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks

import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Impl.Dsa.X86_64.Checks
meta import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time equality of DSA byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure EqualPublic where
  base : Addr
  left : Addr
  right : Addr
  length : Nat

def EqualPre (a b : Operand) (p : EqualPublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .rdi = p.base ∧
    pointerValue s.mem p.base a.pointer = p.left ∧ pointerValue s.mem p.base b.pointer = p.right ∧
    word s.mem p.base a.length.offset = BitVec.ofNat 64 p.length

def EqualRegs (p : EqualPublic) (s : State) : Prop :=
  s.gpr .rdi = p.base ∧ s.gpr .rsi = p.left ∧ s.gpr .rdx = p.right ∧
    s.gpr .rcx = BitVec.ofNat 64 p.length

/-- The equality check and mask accumulation depend only on the public
workspace address, operand pointers and length. Input contents remain secret. -/
theorem equal_ct {a b : Operand} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (unequal : Bool) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax)] : List Instr) ++ Core.pointer b.pointer ++
      ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EqualPre a b)) (Checks.equal a b unequal) (fun _ _ => True) := by
  unfold Checks.equal seqs
  refine RelCT.seq (two_piece (Ψ := EqualRegs) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hleft, hright, hlen⟩
    exact WP.mono (equalHead_ok hs hdi hZ a b ha hb) fun t h =>
      ⟨(h.2.2.2.2.2.gpr (by decide)).trans hdi, h.1.trans hleft,
        h.2.1.trans hright, h.2.2.1.trans hlen⟩
  have hp : Pins EqualRegs [.rdi, .rsi, .rdx, .rcx] :=
    pins_of (fun p r => if r = .rdi then p.base else if r = .rsi then p.left
      else if r = .rdx then p.right else BitVec.ofNat 64 p.length) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2)
  cases unequal <;> exact two_taint [.rdi, .rsi, .rdx, .rcx] hp (by taint_decide)

end VG.Proof.Dsa.X86_64
