module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallFacts
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem callMemBase_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 7) :
    stackWord (callMemBase p used m sp) sp j = callValue p used j := by
  unfold callMemBase
  rw [stackWord_store (i := 6) _ _ _ (by decide) (by omega),
    stackWord_store (i := 5) _ _ _ (by decide) (by omega),
    stackWord_store (i := 4) _ _ _ (by decide) (by omega),
    stackWord_store (i := 3) _ _ _ (by decide) (by omega),
    stackWord_store (i := 2) _ _ _ (by decide) (by omega),
    stackWord_store (i := 1) _ _ _ (by decide) (by omega),
    stackWord_store (i := 0) _ _ _ (by decide) (by omega)]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

abbrev attemptWords (sampling : GenerationPolicy) : Nat :=
  if sampling.cachedContext then 9 else 7

theorem callMem_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat}
    (bound : j < attemptWords sampling) : stackWord (callMem p used m sp) sp j = callValue p used j := by
  unfold callMem
  split <;> rename_i active
  · have bound : j < 9 := by simpa only [attemptWords, active, ite_true] using bound
    rw [stackWord_store (i := 8) _ _ _ (by decide) (by omega),
      stackWord_store (i := 7) _ _ _ (by decide) (by omega)]
    by_cases eight : j = 8
    · subst j; rfl
    by_cases seven : j = 7
    · subst j; rfl
    simp only [eight, seven, ite_false]
    exact callMemBase_word _ _ _ _ (by omega)
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
  rw [sp, VG.Arm.addr_add (by have fit := facts.argsFit; cases sampling <;> simp only [attemptWords, GenerationPolicy.cachedContext, GenerationPolicy.argumentBytes, Bool.false_eq_true, ite_true, ite_false] at bound fit <;> omega), mem]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.KeySearch
