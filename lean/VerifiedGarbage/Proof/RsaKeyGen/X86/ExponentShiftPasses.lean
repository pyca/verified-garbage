module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentShiftContext
public import VerifiedGarbage.Spec.MillerRabin

/-! # The three masked native passes produce the reviewed exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem passes_ok {s : State} {base : Addr} {size n marker out k : Nat}
    (C : Context base size n marker out k s) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n =
        (let x := val32 s.mem base out n
         let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf k then x / 2 else x
         let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf k then x1 / 2 else x1
         if 3 < VG.Proof.RsaKeyGen.sigOf k then x2 / 2 else x2) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (halfIf_context C (j := 1) (by decide)) fun a ⟨A, Oa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_context A (j := 2) (by decide)) fun b ⟨B, Ob, Vb, Kb⟩ => ?_)
  refine WP.mono (halfIf_context B (j := 3) (by decide)) fun t ⟨T, Ot, Vt, Kt⟩ => ?_
  exact ⟨T, (Oa.trans Ob).trans Ot, by rw [Vt, Vb, Va], (Ka.trans Kb).trans Kt⟩

theorem passes_exponent {s : State} {base : Addr} {size n marker out c : Nat}
    (C : Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) s)
    (odd : c % 2 = 1) (value : val32 s.mem base out n = c / 2) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) t ∧
      Outside base out (4 * n) s.mem t.mem ∧ val32 t.mem base out n = Spec.MillerRabin.exponent c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (passes_ok C) fun t ⟨T, O, V, K⟩ => ?_
  rw [value, VG.Proof.RsaKeyGen.sigOf_mod] at V
  exact ⟨T, O, V.trans (VG.Proof.RsaKeyGen.mrE_halves odd), K⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
