module

public import VerifiedGarbage.Proof.Bignum.X86.CrtSized

/-! # Resources and a boolean acceptance mask survive private CRT arithmetic -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic

theorem prepared_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) :
    WP isa (.seq (importComponents (Spec.Rsa.modulusWords len))
      (.seq (validate (Spec.Rsa.modulusWords len)) (compute (Spec.Rsa.modulusWords len)))) s fun t =>
      Inputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp ∧
      ∃ accept : Bool, t.mem.readW (off base 8) 32 = if accept then BitVec.allOnes 32 else 0 := by
  have dims := h.dimensions
  have space := h.space
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have modulusBound : componentValue s.mem args 2 < 2 ^ (64 * Spec.Rsa.modulusWords len) :=
    Nat.lt_of_lt_of_le h.modulus_bound (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.seq (WP.mono (importComponents_ok h) fun u ⟨N, _, _, _, _, _, _, O, hu, K⟩ => ?_)
  have Narrow : wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) 9) (Spec.Rsa.modulusWords len) =
      wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) 9) (2 * Spec.Rsa.modulusWords len) := by
    rw [VG.Proof.Bignum.wordsVal_low_half, N, Nat.mod_eq_of_lt modulusBound]
  refine WP.mono (checkedCompute_ok hu.scratch dims.1 dims.2.1 h.space Narrow) fun t ⟨A, _, Ot, Kt⟩ => ?_
  have Kst : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := K.trans (Kt.mono (by decide))
  have Ost := (O.mono (by omega : 0 ≤ 64) (by omega : 64 + (bytes - 64) ≤ 0 + bytes)).trans
    (body_scratch (checked_frame Ot h.space) (by omega))
  let w (i : Nat) := wordsVal u.mem base (VG.Impl.Mont.X86.Dynamic.slot (Spec.Rsa.modulusWords len) i) (Spec.Rsa.modulusWords len)
  refine ⟨h.keep Kst (by decide) (by decide) Ost, Kst.1 _ (by decide),
    decide (w pSlot * w qSlot = w modulusSlot ∧ w inputSlot < w modulusSlot ∧ w inverseSlot < w pSlot), ?_⟩
  simpa only [mask32, decide_eq_true_eq, w, acceptanceOffset] using A

end VG.Proof.Bignum.X86.Crt
