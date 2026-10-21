module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Function
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Public
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PushedArguments
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PushMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! The unchanged public signature provides all inputs for the verified native search function. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem searchInput {p : SearchParams} {s : State}
    (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) (args : SearchAbi p s) : FunctionInput p s := by
  have layout := searchLayout pre args
  have fit := layout.stackFits
  have savedSub : (⟨State.addr (bodyState s).sp, 24⟩ : Region).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_sub (by decide) fit
  have belowSub : (FrameStack.belowA (bodyState s).sp 208).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_inner (by decide) fit
  have storage : SearchBuffers p ((bodyState s).setReg .r4 p.control) := by
    refine ⟨⟨⟨p.controlFits, ?_⟩, ?_⟩, ⟨p.c.outputFits, ?_⟩, ⟨p.c.usedFits, ?_⟩,
      ⟨p.c.scratchFits, ?_⟩, ?_, layout.push_bytes args, ?_, ?_, ?_⟩
    · change (⟨State.addr p.control, 128⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · simp only [State.setReg, ite_true]
    · change (⟨State.addr p.c.out, p.c.length⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.usedPtr, 8⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.base, 8 * p.c.capacity⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · refine ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ ?_), Region.contains_self _ _⟩
      rw [layout.reads]; simp [readRegions]
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self), Region.contains_self _ _⟩
    · change 208 ≤ (s.sp - 24#32).toNat
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    · intro r member
      have original : r ∈ writeRegions p ++ readRegions p s.sp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [writeRegions, readRegions]
      exact ⟨(layout.stackSeparate r original).sub_left savedSub,
        (layout.stackSeparate r original).sub_left belowSub⟩
  have initial : SearchStart p (bodyState s) := by
    refine ⟨storage, pushed_arguments layout args, args.out, args.used, args.bits, ?_, ?_, ?_⟩
    · have word := layout.push_word (j := 0) (by decide)
      have address : VG.Proof.Mont.off (State.addr p.control) 0 = State.addr p.control := by simp [VG.Proof.Mont.off]
      rw [show 8 * 0 = 0 from rfl, address] at word
      exact word.trans args.counter
    · exact (layout.push_word (j := 1) (by decide)).trans args.widthPolicy
    · exact (layout.push_word (j := 2) (by decide)).trans args.entropyPolicy
  refine ⟨fit, initial, ?_⟩
  intro r member
  rw [layout.writes] at member
  exact (layout.stackSeparate r (List.mem_append_left _ member)).sub_left savedSub

end VG.Proof.Ffdh.Arm.ParameterSearch
