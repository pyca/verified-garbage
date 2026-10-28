module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyInvariant
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Deriving
public import VerifiedGarbage.Proof.Dsa.X86.CheckingLayout
public import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallPre
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre

/-! Shared facts about the inlined bodies' allocated cdecl arguments. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom

theorem check_allocated_args {s t : State} (R : Ready s t) (C : CheckCall.CallSlots s t)
    (i : Nat) (hi : i<6) :
    arg ((allocated 4 t).withRegions (CheckCall.callRd s) (CheckCall.callWr s)) i=
      CheckCall.callVal s (t.gpr .esp) i := by
  rw [allocated_arg R (by omega)]; exact C i hi

theorem derive_allocated_args {s t : State} (R : Ready s t) (C : CallSlots s t)
    (i : Nat) (hi : i<9) :
    arg ((allocated 4 t).withRegions (callRd s) (callWr s)) i=callVal s (t.gpr .esp) i := by
  rw [allocated_arg R (by omega)]; exact C i hi

theorem check_allocated_params {s t : State} (A : KeyABI s) (R : Ready s t) (C : CheckCall.CallSlots s t) :
    checkingParams ((allocated 4 t).withRegions (CheckCall.callRd s) (CheckCall.callWr s))=
      Spec.Dsa.paramsBytes (arg s 5).toNat (arg s 6).toNat (rInput s).key := by
  unfold checkingParams
  simp only [argumentPointer,check_allocated_args R C 0 (by decide),check_allocated_args R C 1 (by decide),
    check_allocated_args R C 2 (by decide),check_allocated_args R C 3 (by decide),CheckCall.callVal]
  change Spec.Dsa.paramsBytes _ _ (Spec.Rsa.bytesAt t.mem (argumentPointer s 3) (arg s 4).toNat)=_
  rw [callKey A R]

theorem derive_allocated_params {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t) :
    derivingParams ((allocated 4 t).withRegions (callRd s) (callWr s))=
      Spec.Dsa.paramsBytes (arg s 5).toNat (arg s 6).toNat (rInput s).key := by
  unfold derivingParams
  simp only [argumentPointer,derive_allocated_args R C 2 (by decide),derive_allocated_args R C 3 (by decide),
    derive_allocated_args R C 4 (by decide),derive_allocated_args R C 6 (by decide),callVal]
  change Spec.Dsa.paramsBytes _ _ (Spec.Rsa.bytesAt t.mem (argumentPointer s 3) (arg s 4).toNat)=_
  rw [callKey A R]

theorem derive_allocated_valid {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t)
    (checked : KeyRandom.checked s=true) :
    validParameters ((allocated 4 t).withRegions (callRd s) (callWr s)) := by
  change Spec.Dsa.parametersValid (derivingParams _)
  rw [derive_allocated_params A R C]
  unfold KeyRandom.checked Spec.Dsa.checkParametersBytes at checked
  simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
  exact checked.2

theorem derive_allocated_context {s t : State} (A : KeyABI s) (R : Ready s t) (C : CallSlots s t)
    (context : keyInvariant s t.mem) :
    deriveContext ((allocated 4 t).withRegions (callRd s) (callWr s)) t.mem := by
  unfold deriveContext parameterContext
  change canonical _ _ (derivingParams _).p (derivingParams _).g _ _
  rw [derive_allocated_params A R C]
  simp only [argumentPointer,derive_allocated_args R C 4 (by decide),derive_allocated_args R C 6 (by decide),
    derive_allocated_args R C 7 (by decide),callVal]
  exact context.2

end VG.Proof.Dsa.X86.Comb
