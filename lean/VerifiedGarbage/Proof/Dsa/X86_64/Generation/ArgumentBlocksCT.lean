module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Argument transfer touches fixed offsets of public frame and workspace pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure ArgumentPointers where
  B : Addr
  F : Addr

def ArgumentRegisters (p : ArgumentPointers) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ s.gpr .rsp = p.F

theorem argumentRegisters_pins : Pins ArgumentRegisters [.rdi, .rsp] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.trans ht.2.symm

theorem candidateArguments_ct (pLen qLen : Nat)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (candidateArguments pLen qLen))) hc).isSome = true) : RelCT isa (Two ArgumentRegisters)
    (.block (headerArguments (candidateArguments pLen qLen))) (fun _ _ => True) :=
  two_taint [.rdi, .rsp] argumentRegisters_pins ht

end VG.Proof.Dsa.X86_64.Generation
