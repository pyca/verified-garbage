module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Spec.Dsa.Generate
import Batteries.Tactic.Init

/-! # The parameter-generation contract discloses lengths and all three search tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

structure GenerationPublicAgree (s t : State) : Prop where
  sp : s.gpr .esp = t.gpr .esp
  args : ∀ i < 12, arg s i = arg t i
  seeds : Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat = Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat
  hs : Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat = Spec.Rsa.bytesAt t.mem (argumentPointer t 6) (arg t 7).toNat
  rand : Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat = Spec.Rsa.bytesAt t.mem (argumentPointer t 8) (arg t 9).toNat

theorem generation_public_related {s t : State}
    (h : (Spec.Dsa.generateParametersContract abi 292).pub s t) : GenerationPublicAgree s t := by
  sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  obtain ⟨sp, leak, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  have args : ∀ i < 12, arg s i = arg t i := by
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
  change ((Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat) ++
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat).map (·.toNat)) ++
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat).map (·.toNat) =
    ((Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat) ++
    (Spec.Rsa.bytesAt t.mem (argumentPointer t 6) (arg t 7).toNat).map (·.toNat)) ++
    (Spec.Rsa.bytesAt t.mem (argumentPointer t 8) (arg t 9).toNat).map (·.toNat) at leak
  rw [List.append_assoc, List.append_assoc] at leak
  have lens : ((Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, args 5 (by decide)]
  obtain ⟨seeds, rest⟩ := List.append_inj leak lens
  have lenh : ((Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (argumentPointer t 6) (arg t 7).toNat).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, args 7 (by decide)]
  obtain ⟨hs, rand⟩ := List.append_inj rest lenh
  exact ⟨sp, args, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 seeds,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hs,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 rand⟩
end VG.Proof.Dsa.X86.Generation
