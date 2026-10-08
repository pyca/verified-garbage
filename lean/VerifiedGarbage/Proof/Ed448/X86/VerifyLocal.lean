import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): the contract the proof is written against

`verifyEquationLocal`, the facts of `Spec.Ed448.verifyEquationContract` the
proof is written against, in a module of their own: callers proven for any
code meeting it need not import the proof. The arguments are only read; the
inputs are public (`pub` includes their bytes).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86
open VG.Spec.Ed448 (bytesAt)

/-- `vg_ed448_verify_equation(pk, signature, challenge, scratch) -> eax`,
whose arguments are on the stack (cdecl), with the 20 bytes of stack below its
return address that its calls of the field functions use. -/
def verifyEquationLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let sig : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let challenge : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩
    s.rd = [pk, sig, challenge, args] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint pk ∧
      stk.Disjoint sig ∧ stk.Disjoint challenge ∧ stk.Disjoint scratch
  post s t := t.gpr .eax = if Spec.Ed448.verifyEquation
    (bytesAt s.mem ((arg s 0).setWidth 64) 57) (bytesAt s.mem ((arg s 1).setWidth 64) 114)
    (bytesAt s.mem ((arg s 2).setWidth 64) 57) then 1 else 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧
    bytesAt s.mem ((arg s 0).setWidth 64) 57 = bytesAt t.mem ((arg t 0).setWidth 64) 57 ∧
    bytesAt s.mem ((arg s 1).setWidth 64) 114 = bytesAt t.mem ((arg t 1).setWidth 64) 114 ∧
    bytesAt s.mem ((arg s 2).setWidth 64) 57 = bytesAt t.mem ((arg t 2).setWidth 64) 57

end VG.Proof.Ed448.X86
