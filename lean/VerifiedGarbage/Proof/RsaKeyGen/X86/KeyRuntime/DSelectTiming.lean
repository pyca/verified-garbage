module

import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOddPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DEvenPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOnePublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Public exponent branches compose with secret native arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (kEv equalExponent parityExponent)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure ExponentPair (B : Addr) (Z n e : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  exponentLeft : val32 s.mem B kEv 2 = e
  exponentRight : val32 t.mem B kEv 2 = e

def ExponentTest (B : Addr) (Z n e : Nat) (bit : Bool) (s t : State) : Prop :=
  ExponentPair B Z n e s t ∧ isa.eval .e s = some bit ∧ isa.eval .e t = some bit

theorem equalExponent_trace (B : Addr) (Z n e : Nat) (value : BitVec 32) :
    RelCT isa (ExponentPair B Z n e) (.block (equalExponent value))
      (ExponentTest B Z n e (decide (e = value.toNat))) := by
  have checked : Public (.block (equalExponent value)) := by
    refine ⟨(VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))),
        runtimeTaint, ?_, rfl⟩
    exact (check_of_erase_eq (.block (equalExponent value)) (.block (equalExponent 0) : Prog isa) runtimeTaint
      (VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (equalExponent_ok P.left value) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (equalExponent_ok P.right value) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight⟩, flagU, flagV⟩

theorem parityExponent_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) (.block parityExponent)
      (ExponentTest B Z n e (decide (e % 2 = 0))) := by
  have checked : Public (.block parityExponent) := ⟨.block [], runtimeTaint, rfl, rfl⟩
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (parityExponent_ok P.left) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (parityExponent_ok P.right) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight⟩, flagU, flagV⟩

theorem exponent_branch_trace {B : Addr} {Z n e : Nat} {bit : Bool} {th el : Prog isa}
    (first : RelCT isa (ExponentPair B Z n e) th (VG.X86.Taint.Agree runtimeTaint))
    (second : RelCT isa (ExponentPair B Z n e) el (VG.X86.Taint.Agree runtimeTaint)) :
    RelCT isa (ExponentTest B Z n e bit) (.ite .e th el) (VG.X86.Taint.Agree runtimeTaint) := by
  apply RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · exact first.mono (fun _ _ P => P.1.1) (fun _ _ P => P)
  · exact second.mono (fun _ _ P => P.1.1) (fun _ _ P => P)

theorem dSelect_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) dSelect (VG.X86.Taint.Agree runtimeTaint) := by
  have odd := (public_trace dOdd_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  have even := (public_trace dEven_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  have one := (public_trace dOne_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  have zero := (public_trace dZero_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  unfold dSelect
  exact RelCT.seq (equalExponent_trace B Z n e 0) (exponent_branch_trace zero
    (RelCT.seq (equalExponent_trace B Z n e 1) (exponent_branch_trace one
      (RelCT.seq (parityExponent_trace B Z n e) (exponent_branch_trace even odd)))))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
