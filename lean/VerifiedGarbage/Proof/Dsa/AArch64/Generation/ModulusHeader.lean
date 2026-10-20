module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Policy-header writes leave the prepared modulus and exponent intact. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem ModulusReady.write_header {s : State} {B : Addr} {Z w N i : Nat} (v : BitVec 64)
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hi : i ∈ [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 31]) :
    ModulusReady {s with mem := s.mem.writeW (off B (8 * i)) v} B Z w N := by
  have hi32 : i < 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  have hf : Frm B [(8 * i, 8)] s.mem (s.mem.writeW (off B (8 * i)) v) :=
    Frm.of_outside (writeW_outside _ B v (by omega)) (by simp)
  have hk : Keep [] s {s with mem := s.mem.writeW (off B (8 * i)) v} :=
    ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_
  · intro r hr; rw [List.mem_singleton.mp hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact KMut.hdr (by decide)
  · intro a ha r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes]; omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes, aE]; omega_arith

end VG.Proof.Dsa.AArch64.Generation
