module

public import VerifiedGarbage.Proof.Bignum.X86.CrtImport
public import VerifiedGarbage.Proof.Bignum.X86.CrtValidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtCheckedCompute
public import VerifiedGarbage.Proof.Bignum.X86.CrtOutputMath
public import VerifiedGarbage.Proof.Bignum.WordsPrefix

/-! # Import and validation keep the call and its arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic

theorem validated_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) :
    WP isa (.seq (importComponents (Spec.Rsa.modulusWords len)) (validate (Spec.Rsa.modulusWords len))) s
      fun t => Inputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp := by
  have dims := h.dimensions
  have modulusBound : componentValue s.mem args 2 < 2 ^ (64 * Spec.Rsa.modulusWords len) :=
    Nat.lt_of_lt_of_le h.modulus_bound (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.seq (WP.mono (importComponents_ok h) fun u ⟨N, _, _, _, _, _, _, _, hu, K⟩ => ?_)
  have Narrow : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) 9) (Spec.Rsa.modulusWords len) =
      wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) 9) (2 * Spec.Rsa.modulusWords len) := by
    rw [VG.Proof.Bignum.wordsVal_low_half, N, Nat.mod_eq_of_lt modulusBound]
  refine WP.mono (validate_ok hu.scratch dims.1 h.space Narrow) fun t ⟨_, O, Kt⟩ => ?_
  exact ⟨hu.keep Kt (by decide) (by decide) (validation_outside O h.space),
    (Kt.1 _ (by decide)).trans (K.1 _ (by decide))⟩

end VG.Proof.Bignum.X86.Crt
