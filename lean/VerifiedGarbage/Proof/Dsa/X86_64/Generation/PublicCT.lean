module
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86_64.Target

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # The generation contract makes all three input tapes public -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure GenerationPublicAgree (s t : State) : Prop where
  sp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ argRegs, s.gpr r = t.gpr r
  args : ∀ i < 6, stackArg s i = stackArg t i
  seeds : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat
  hs : Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat = Spec.Rsa.bytesAt t.mem (stackArg t 0) (stackArg t 1).toNat
  rand : Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat = Spec.Rsa.bytesAt t.mem (stackArg t 2) (stackArg t 3).toNat

theorem generation_public_related {s t : State}
    (h : (Spec.Dsa.generateParametersContract abi 536).pub s t) : GenerationPublicAgree s t := by
  sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
  have hregs : ∀ r ∈ argRegs, s.gpr r = t.gpr r := by
    intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hdi, hsi, hdx, hcx, h8, h9]
  have hargs : ∀ i < 6, stackArg s i = stackArg t i := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5]
  rw [List.append_assoc, List.append_assoc] at hleak
  have lens : ((Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (t.gpr .r8) (t.gpr .r9).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, h9]
  obtain ⟨seeds, rest⟩ := List.append_inj hleak lens
  have lenh : ((Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (stackArg t 0) (stackArg t 1).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, a1]
  obtain ⟨hs, rand⟩ := List.append_inj rest lenh
  exact ⟨hsp, hregs, hargs,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 seeds,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hs,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 rand⟩

end VG.Proof.Dsa.X86_64.Generation
