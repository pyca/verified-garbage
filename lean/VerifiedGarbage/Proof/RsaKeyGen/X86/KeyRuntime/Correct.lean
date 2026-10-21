module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FrameResult
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.TCB.X86.Target

/-! # Complete native key generation satisfies the shared encoded cdecl contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_sizes keyStack EncodedResult encodedOperation
  callEnvironment Environment)

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have Z := call_sizes h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_result_ok h
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold EncodedResult encodedOperation at R
  simp only [callEnvironment, Environment.exponentRegion, Environment.outputRegion, Environment.outputLength,
    List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.reduceLT, ite_true, ite_false] at R
  rw [← Z.modulus] at R
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at R
  generalize result : Spec.RsaKeyGen.keyOp (arg s 5).toNat
    (Spec.Rsa.bytesAt s.mem ((arg s 14).setWidth 64) (arg s 15).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 5).toNat) = value at R ⊢
  cases value with
  | inl answer => cases answer <;> exact R
  | inr u => cases u; exact R

end VG.Proof.RsaKeyGen.X86.KeyRuntime
