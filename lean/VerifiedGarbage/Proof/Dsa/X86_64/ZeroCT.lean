module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks

import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Impl.Dsa.X86_64.Checks
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time zero checks of DSA byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ZeroPublic where
  base : Addr
  left : Addr
  length : Nat

def ZeroPre (a : Operand) (p : ZeroPublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .rdi = p.base ∧
    pointerValue s.mem p.base a.pointer = p.left ∧
    word s.mem p.base a.length.offset = BitVec.ofNat 64 p.length

def ZeroRegs (p : ZeroPublic) (s : State) : Prop :=
  s.gpr .rdi = p.base ∧ s.gpr .rsi = p.left ∧
    s.gpr .rcx = BitVec.ofNat 64 p.length

/-- The zero check and mask accumulation depend only on the public
workspace address, operand pointers and length. Input contents remain secret. -/
theorem zero_ct {a : Operand} (ha : pointerFits a.pointer)
    (nonzero : Bool) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Core.pointer a.pointer ++
      ([.mov .rsi (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ZeroPre a)) (Checks.zero a nonzero) (fun _ _ => True) := by
  unfold Checks.zero seqs
  refine RelCT.seq (two_piece (Ψ := ZeroRegs) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hleft, hlen⟩
    exact WP.mono (zeroHead_ok hs hdi hZ a ha) fun t h =>
      ⟨(h.2.2.2.2.gpr (by decide)).trans hdi, h.1.trans hleft,
        h.2.1.trans hlen⟩
  have hp : Pins ZeroRegs [.rdi, .rsi, .rcx] :=
    pins_of (fun p r => if r = .rdi then p.base else if r = .rsi then p.left
      else BitVec.ofNat 64 p.length) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)
  cases nonzero <;> exact two_taint [.rdi, .rsi, .rcx] hp (by taint_decide)

end VG.Proof.Dsa.X86_64
