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
  | _ => 0

theorem stackWord_store (m : Mem) (sp : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 8) (hj : j < 8) :
    stackWord (m.writeW (off (State.addr sp) (4 * i)) v) sp j =
      if j = i then v else stackWord m sp j := by
  by_cases same : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right same]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem callMem_word (p : KeyPublic sampling) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 7) :
    stackWord (callMem p used m sp) sp j = callValue p used j := by
  unfold callMem
  rw [stackWord_store (i := 6) _ _ _ (by decide) (by omega),
    stackWord_store (i := 5) _ _ _ (by decide) (by omega),
    stackWord_store (i := 4) _ _ _ (by decide) (by omega),
    stackWord_store (i := 3) _ _ _ (by decide) (by omega),
    stackWord_store (i := 2) _ _ _ (by decide) (by omega),
    stackWord_store (i := 1) _ _ _ (by decide) (by omega),
    stackWord_store (i := 0) _ _ _ (by decide) (by omega)]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

def callRdPlain (p : KeyPublic sampling) (used : Nat) : List Region := [rDomain p, rTape p used, rCallArgs p]

def callRd (p : KeyPublic sampling) (used : Nat) : List Region :=
  callRdPlain p used ++ KeyConstants.regions sampling p.tablePtr
def callWr (p : KeyPublic sampling) : List Region := [rX p, rY p, rScratch p]

abbrev callState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRd p used) (callWr p)

abbrev plainCallState (p : KeyPublic sampling) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRdPlain p used) (callWr p)

theorem call_stackArg {p : KeyPublic sampling} {used : Nat} {s : State} {m : Mem} {j : Nat}
    (facts : CallFacts p used) (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p))
    (bound : j < 7) : stackArg (callState p used s) j = callValue p used j := by
  change s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = _
  rw [sp, VG.Arm.addr_add (by have := facts.argsFit; omega), mem]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.KeySearch
