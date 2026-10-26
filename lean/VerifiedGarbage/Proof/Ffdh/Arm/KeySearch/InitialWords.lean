module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import Mathlib.Util.CompileInductive

/-! Exact native halves of the initialized retry counters and domain width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyInput.initial_words {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.mem.readW (off (State.addr p.control) 0) 64 = BitVec.ofNat 64 p.keys ∧
    s.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.scalars ∧
    s.mem.readW (off (State.addr p.control) 16) 64 = BitVec.ofNat 64 p.len := by
  have pre := h.1
  cases h.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq, off, BitVec.add_zero]
  · simp only [keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · cases sampling <;>
      sig_pre [GenerationPolicy.searchContract,GenerationPolicy.legacySearchContract,
        cachedKeySearchContract,cachedKeySearchSig,keySearchSig,abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
    all_goals simp only [KeyConstants.stackArg_stripConsts,KeyConstants.stackArgAddr_stripConsts] at pre
    all_goals sig_split pre
    all_goals
      have value : s.mem.readW (BitVec.setWidth 64 (stackArg s 8)+(16 : BitVec 64)) 64 = BitVec.ofNat 64 (stackArg s 3).toNat := by assumption
      simpa only [keyOfState,off,State.addr,BitVec.ofNat_toNat,show (16 : BitVec 64)=16#64 from rfl] using value

theorem KeyInput.pushed_word {p : KeyPublic sampling} {s : State} {j : Nat} (h : KeyInput p s) (bound : j < 3) :
    (searchPushed s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have fit : stackUse sampling ≤ p.sp.toNat := h.bounds.stackFits
  have rootFit : 24 ≤ s.sp.toNat := by rw [← h.2.1] at fit; change stackUse sampling ≤ s.sp.toNat at fit; have := stackUse_min sampling; omega
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) rootFit
  have sep : (rControl p).Disjoint (FrameStack.belowA s.sp 24) := by
    have base : p.sp = s.sp := by rw [← h.2.1]; rfl
    rw [← base]
    exact h.saved_control.symm
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
    (by simpa using sep) (by decide)

theorem KeyInput.pushed_policy {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    lowWord (searchPushed s).mem p.control 0 = BitVec.ofNat 32 p.keys ∧
    lowWord (searchPushed s).mem p.control 1 = BitVec.ofNat 32 p.scalars ∧
    lowWord (searchPushed s).mem p.control 2 = BitVec.ofNat 32 p.len ∧
    (∀ j < 3, (searchPushed s).mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0) := by
  have w0 := (h.pushed_word (j := 0) (by decide)).trans h.initial_words.1
  have w1 := (h.pushed_word (j := 1) (by decide)).trans h.initial_words.2.1
  have w2 := (h.pushed_word (j := 2) (by decide)).trans h.initial_words.2.2
  have keys : p.keys < 2 ^ 32 := by have := h.bounds.keys; omega
  have scalars : p.scalars < 2 ^ 32 := by have := h.bounds.scalars; omega
  have len : p.len < 2 ^ 32 := by have := h.bounds.maxLength; omega
  refine ⟨packed_low _ _ _ _ keys w0, packed_low _ _ _ _ scalars w1, packed_low _ _ _ _ len w2, ?_⟩
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases casesJ with rfl | rfl | rfl
  · exact packed_high _ _ _ _ keys w0
  · exact packed_high _ _ _ _ scalars w1
  · exact packed_high _ _ _ _ len w2

end VG.Proof.Ffdh.Arm.KeySearch
