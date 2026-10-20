module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABI
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The generation contract makes all three input tapes public -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure GenerationPublicAgree (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ argRegs, s.gpr r = t.gpr r
  args : ∀ i < 4, stackArg s i = stackArg t i
  seeds : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat
  hs : Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x7).toNat
  rand : Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat = Spec.Rsa.bytesAt t.mem (stackArg t 0) (stackArg t 1).toNat

theorem generation_public_related {s t : State}
    (h : (Spec.Dsa.generateParametersContract abi 464).pub s t) : GenerationPublicAgree s t := by
  sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, generationStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3⟩ := h
  have hregs : ∀ r ∈ argRegs, s.gpr r = t.gpr r := by
    intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5, h6, h7]
  have hargs : ∀ i < 4, stackArg s i = stackArg t i := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]
  rw [List.append_assoc, List.append_assoc] at hleak
  have lens : ((Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, h5]
  obtain ⟨seeds, rest⟩ := List.append_inj hleak lens
  have lenh : ((Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x7).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, h7]
  obtain ⟨hs, rand⟩ := List.append_inj rest lenh
  exact ⟨hsp, hregs, hargs,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 seeds,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hs,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 rand⟩

end VG.Proof.Dsa.AArch64.Generation
