module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerFrame

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! The callable round retains every constant needed for the next witness. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin

theorem kernel_preserves_modulus {s t : State} {B : Addr} {Z w N : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hf : Frm B (VG.Proof.MillerRabin.AArch64.Caller.callRanges w) s.mem t.mem)
    (hk : Keep mmRegs s t) : ModulusReady t B Z w N := by
  apply h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      KMut, VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, sW, sMinv, sArr, sStride, sFn]
    and_intros <;> omega_arith
  · intro a ha
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
        Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aN, aOne, aR2, aR1, aRm1,
        Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
      and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, sMinv,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, aE,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation
