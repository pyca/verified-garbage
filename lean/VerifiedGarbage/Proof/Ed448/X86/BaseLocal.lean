import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 base-point multiplication on x86 (32-bit): the contract the proof is written against

`scalarBaseLocal`, in a module of its own: callers proven for any code
meeting it need not import the proof.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86
open VG.Spec.Ed448 (bytesAt)

/-- `vg_ed448_scalar_base(out, scalar, scratch)`, whose arguments are on the
stack (cdecl), with the 20 bytes of stack below its return address that its
calls of the field functions use. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩
    s.rd = [scalar, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint out ∧
      stk.Disjoint scratch
  post s t := bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.scalarBase (bytesAt s.mem ((arg s 1).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

end VG.Proof.Ed448.X86
