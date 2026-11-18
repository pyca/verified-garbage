module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.KeySearch.CallFacts`, which only this module used -/

section

/-! The nested attempt's buffers and private stack satisfy its shared signature. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/Tape.lean`, which only this module imported.
section

/-! A nested attempt receives exactly the next public-width slice of entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

abbrev rTape (p : KeyPublic sampling) (used : Nat) : Region :=
  ⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩

theorem KeyInput.tape_addr {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    State.addr (p.rp + BitVec.ofNat 32 used) = off (State.addr p.rp) used :=
  VG.Arm.addr_add (by have := h.bounds.randomFit; have := h.bounds.minLength; omega_arith)

theorem KeyInput.tape_sub {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) : (rTape p used).Sub (rRandom p) := by
  change (⟨State.addr (p.rp + BitVec.ofNat 32 used), p.len⟩ : Region).Sub _
  rw [h.tape_addr room]
  exact Offset.sub_base _ room

theorem KeyInput.tape_fits {p : KeyPublic sampling} {s : State} {used : Nat}
    (h : KeyInput p s) (room : used + p.len ≤ p.randLen) :
    (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32 := by
  have fits := h.bounds.randomFit
  have positive := h.bounds.minLength
  have usedFits : used < 2 ^ 32 := by omega_using [room, fits, positive]
  have pointerFits : p.rp.toNat + used < 2 ^ 32 := by omega_using [room, fits, positive]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFits, Nat.mod_eq_of_lt pointerFits]
  omega_using [room, fits]

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

abbrev rCallArgs (p : KeyPublic sampling) : Region := ⟨State.addr (callSp p), sampling.argumentBytes - 4⟩

structure CallFacts (p : KeyPublic sampling) (used : Nat) : Prop where
  stackFits : 176 ≤ (callSp p).toNat
  argsFit : (callSp p).toNat + (sampling.argumentBytes - 4) ≤ 2 ^ 32
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rDomain p)
  xr : (rX p).Disjoint (rTape p used)
  xs : (rX p).Disjoint (rScratch p)
  xa : (rX p).Disjoint (rCallArgs p)
  yd : (rY p).Disjoint (rDomain p)
  yr : (rY p).Disjoint (rTape p used)
  ys : (rY p).Disjoint (rScratch p)
  ya : (rY p).Disjoint (rCallArgs p)
  ds : (rDomain p).Disjoint (rScratch p)
  rs : (rTape p used).Disjoint (rScratch p)
  sa : (rScratch p).Disjoint (rCallArgs p)
  stack : ∀ r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p],
    (rCallStack p).Disjoint r
  xFit : p.xp.toNat + p.len ≤ 2 ^ 32
  yFit : p.yp.toNat + p.len ≤ 2 ^ 32
  domainFit : p.dp.toNat + p.dlen ≤ 2 ^ 32
  tapeFit : (p.rp + BitVec.ofNat 32 used).toNat + p.len ≤ 2 ^ 32
  scratchFit : p.scratch.toNat + p.capacity * 8 ≤ 2 ^ 32
  length : pLenValid p.len
  domainLength : domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.capacity
  lenFits : p.len < 2 ^ 32
  domainLenFits : p.dlen < 2 ^ 32
  capacityFits : p.capacity < 2 ^ 32

theorem KeyInput.callFacts {p : KeyPublic sampling} {original : State} {used : Nat}
    (h : KeyInput p original) (room : used + p.len ≤ p.randLen) : CallFacts p used := by
  have fit : stackUse sampling ≤ p.sp.toNat := h.bounds.stackFits
  have sizeMin := argumentBytes_min sampling
  have sizeMax := argumentBytes_max sampling
  have callNat : (callSp p).toNat = p.sp.toNat - (24 + sampling.argumentBytes) :=
    FrameStack.sub_toNat' (by change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit; omega_using [fit])
  have rootWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) : r ∈ original.wr := by
    rw [h.write_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp
  have rootRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : r ∈ original.rd := by
    rw [h.read_regions]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have cross (w : Region) (hw : w ∈ [rX p, rY p, rScratch p])
      (r : Region) (hr : r ∈ [rDomain p, rRandom p]) : w.Disjoint r :=
    h.layout.separate w (by rw [← h.layout.wr]; exact rootWrite w hw)
      r (by rw [← h.layout.rd]; exact rootRead r hr)
  have tape := h.tape_sub room
  have argsSub : (rCallArgs p).Sub (FrameStack.belowA p.sp (stackUse sampling)) :=
    fun a ha => (arguments_sub h.bounds.stackFits) a (Region.sub_prefix (by omega_using [] : sampling.argumentBytes - 4 ≤ sampling.argumentBytes) a ha)
  have stackSub := callStack_sub h.bounds.stackFits
  have stackWrite (r : Region) (hr : r ∈ [rX p, rY p, rScratch p]) :
      (FrameStack.belowA p.sp (stackUse sampling)).Disjoint r :=
    h.stack_separate (List.mem_append_left _ (rootWrite r hr))
  have stackRead (r : Region) (hr : r ∈ [rDomain p, rRandom p]) :
      (FrameStack.belowA p.sp (stackUse sampling)).Disjoint r :=
    h.stack_separate (List.mem_append_right _ (rootRead r hr))
  have geometry := h.output_regions_disjoint
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
  refine ⟨by rw [callNat]; omega_using [fit], by rw [callNat]; have := p.sp.isLt; omega_using [sizeMax],
    geometry.1, cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    cross _ (by simp) _ (by simp), (cross _ (by simp) _ (by simp)).sub_right tape,
    geometry.2.2.1, (stackWrite _ (by simp)).symm.sub_right argsSub,
    (cross _ (by simp) _ (by simp)).symm, ((cross _ (by simp) _ (by simp)).sub_right tape).symm,
    (stackWrite _ (by simp)).symm.sub_right argsSub, ?_, h.bounds.xFit, h.bounds.yFit,
    h.bounds.domainFit, h.tape_fits room, by simpa only [Nat.mul_comm] using h.bounds.scratchFit,
    ⟨h.bounds.minLength, h.bounds.maxLength⟩, h.bounds.domainLength, h.bounds.scratchSpace,
    by have := h.bounds.maxLength; omega_using [this], ?_, h.bounds.capacityFits⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · exact (stackRead _ (by simp)).sub_left stackSub
    · exact ((stackRead _ (by simp)).sub_left stackSub).sub_right tape
    · exact (stackWrite _ (by simp)).sub_left stackSub
    · have enough : 176 ≤ (callSp p).toNat := by rw [callNat]; omega_using [fit]
      rw [rCallStack, FrameStack.belowA, FrameStack.addr_sub' enough]
      exact (Offset.base_disjoint_below _ (by omega_using [sizeMax] : 176 + (sampling.argumentBytes - 4) ≤ 2 ^ 64)).symm
  · have lengths := h.bounds.domainLength
    have maxLength := h.bounds.maxLength
    unfold domainLenValid at lengths
    rcases lengths with eq | eq <;> omega_using [maxLength, eq]

end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! Reading the seven ARM stack arguments after filling the call frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

def stackWord (m : Mem) (sp : BitVec 32) (j : Nat) : BitVec 32 :=
  m.readW (off (State.addr sp) (4 * j)) 32

def callValue (p : KeyPublic sampling) (used j : Nat) : BitVec 32 :=
  match j with
  | 0 => p.dp
  | 1 => BitVec.ofNat 32 p.dlen
  | 2 => BitVec.ofNat 32 p.len
  | 3 => p.rp + BitVec.ofNat 32 used
  | 4 => BitVec.ofNat 32 p.len
  | 5 => p.scratch
  | 6 => BitVec.ofNat 32 p.capacity
  | 7 => p.context
  | 8 => BitVec.ofNat 32 p.contextWords
  | _ => 0

theorem stackWord_store (m : Mem) (sp : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 10) (hj : j < 10) :
    stackWord (m.writeW (off (State.addr sp) (4 * i)) v) sp j =
      if j = i then v else stackWord m sp j := by
  by_cases same : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right same]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [same]) (by omega_using [hj]) (by omega_using [hi])) (by decide)

theorem callMemBase_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 7) :
    stackWord (callMemBase p used m sp) sp j = callValue p used j := by
  unfold callMemBase
  rw [stackWord_store (i := 6) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 5) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 4) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 3) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 2) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 1) _ _ _ (by decide) (by omega_using [bound]),
    stackWord_store (i := 0) _ _ _ (by decide) (by omega_using [bound])]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega_using [bound]
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

abbrev attemptWords (sampling : GenerationPolicy) : Nat :=
  if sampling.cachedContext then 9 else 7

theorem callMem_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat}
    (bound : j < attemptWords sampling) : stackWord (callMem p used m sp) sp j = callValue p used j := by
  unfold callMem
  split <;> rename_i active
  · have bound : j < 9 := by simpa only [attemptWords, active, ite_true] using bound
    rw [stackWord_store (i := 8) _ _ _ (by decide) (by omega_using [bound]),
      stackWord_store (i := 7) _ _ _ (by decide) (by omega_using [bound])]
    by_cases eight : j = 8
    · subst j; rfl
    by_cases seven : j = 7
    · subst j; rfl
    simp only [eight, seven, ite_false]
    exact callMemBase_word _ _ _ _ (by omega_using [bound, eight, seven])
  · have bound : j < 7 := by simpa only [attemptWords, active, Bool.false_eq_true, ite_false] using bound
    exact callMemBase_word _ _ _ _ bound

def callRdPlain (p : KeyPublic sampling) (used : Nat) : List Region := [rDomain p, rTape p used] ++ contextRegions p ++ [rCallArgs p]

def callRd (p : KeyPublic sampling) (used : Nat) : List Region :=
  callRdPlain p used ++ KeyConstants.regions sampling p.tablePtr
def callWr (p : KeyPublic sampling) : List Region := [rX p, rY p, rScratch p]

abbrev callState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRd p used) (callWr p)

abbrev plainCallState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRdPlain p used) (callWr p)

theorem call_stackArg {p : KeyPublic sampling} {used : Nat} {s : State} {m : Mem} {j : Nat}
    (facts : CallFacts p used) (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p))
    (bound : j < attemptWords sampling) : stackArg (callState p used s) j = callValue p used j := by
  change s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = _
  rw [sp, VG.Arm.addr_add (by have fit := facts.argsFit; cases sampling <;> simp only [attemptWords, GenerationPolicy.cachedContext, GenerationPolicy.argumentBytes, Bool.false_eq_true, ite_true, ite_false] at bound fit <;> omega_using [bound, fit]), mem]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.KeySearch
