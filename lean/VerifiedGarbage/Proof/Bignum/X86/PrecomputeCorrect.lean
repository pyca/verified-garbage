module
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInstalled
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeOperation
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Correct
import VerifiedGarbage.Proof.Framework.Offset

/-! # Functional correctness and cdecl preservation of RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86 PublicContext

theorem precomputeOperation_ok {s : State} (A : PrecomputeABI s) :
    WP isa PrecomputeFn.code s fun t =>
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) with
      | some ws => t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat = ws
      | none => t.gpr .eax = 0 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat =
          List.replicate (arg s 1).toNat 0) ∧ abiPreserved s t := by
  have low : 16 ≤ (arg s 5).toNat * 8 := by have := A.used; omega
  have high : (arg s 5).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  unfold PrecomputeFn.code
  refine WP.seq (WP.mono (precomputeInstalled_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  refine WP.seq (WP.mono (precomputeBody_ok I) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have slot : (⟨addr (u.gpr .esp) 8, 4⟩ : Region).Disjoint
      ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ := (I.stack 1 (by decide)).stack.apart
  rw [espu] at F slot
  have Saved : VG.X86.Spill.Saved v.mem (off (argumentPointer s 4)) s.gpr PublicFn.savedRegisters := by
    intro p hp
    have B : p.2 + 4 ≤ 16 := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    refine (F.readW (r := ⟨argumentPointer s 4, 16⟩) (Offset.contains_base _ B (by omega)) ?_ (by decide)).trans
      (S p hp)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (Nat.le_refl 16) (by omega)
    · exact I.outApart.sub_left (Region.sub_prefix (by omega))
    · have := I.room.apart; rw [espu] at this; exact (this.sub_right (Region.sub_prefix (by omega))).symm
    · exact (slot.sub_right (Region.sub_prefix (by omega))).symm
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    have Start := outside_frame O (by omega)
    simp only [BitVec.add_zero] at Start
    have hlow := A.stackLow
    have hb := A.stackBound
    rw [F.readW (Region.contains_self _ 4) ?_ (by decide)]
    · refine Start.readW (Region.contains_self _ 4) ?_ (by decide)
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact A.retScratch
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.retScratch.sub_right (Offset.sub_base _ (by omega))
    · rw [← A.outputBytes]; exact A.retOut
    · exact VG.Proof.Bignum.X86.PublicRt.ret_below hlow
    · have e : addr (s.gpr .esp) 8 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega)
      rw [e]
      exact Offset.base_disjoint _ (by decide) (by omega)
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide), A.preLength]
  have N := scratch_bytes O (by have := A.lengths.2; omega) A.nScratch
  change (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt u.mem (argumentPointer s 2) (arg s 3).toNat) with
    | some ws => v.gpr .eax = 1 ∧ Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) = ws
    | none => v.gpr .eax = 0 ∧ Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
        List.replicate (2 * Spec.Rsa.modulusWords (arg s 3).toNat) 0) at V
  rw [N] at V
  exact V

theorem precomputeCorrect (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 96).pre s) :
    ∃ trace t, Exec isa PrecomputeFn.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputeContract abi 96).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := precomputeOperation_ok (precomputeABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86
