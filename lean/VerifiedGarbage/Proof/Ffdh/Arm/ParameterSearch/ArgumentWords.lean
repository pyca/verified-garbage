module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallLayout
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Read the candidate's AAPCS arguments using the shared native stack-word lemmas. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

def callValue (p : SearchParams) (used : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 p.c.generator
  | 1 => p.c.tape + BitVec.ofNat 32 used
  | 2 => BitVec.ofNat 32 (p.c.bytes.length - used)
  | 3 => p.c.base
  | 4 => BitVec.ofNat 32 p.c.capacity
  | _ => 0

theorem callMem_word (p : SearchParams) (used : Nat) (m : Mem) (sp : BitVec 32) {j : Nat} (bound : j < 5) :
    (callMem p used m sp).readW (off (State.addr sp) (4 * j)) 32 = callValue p used j := by
  change VG.Proof.Ffdh.Arm.KeySearch.stackWord (callMem p used m sp) sp j = _
  unfold callMem
  rw [VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 4) _ _ _ (by decide) (by omega),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 3) _ _ _ (by decide) (by omega),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 2) _ _ _ (by decide) (by omega),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 1) _ _ _ (by decide) (by omega),
    VG.Proof.Ffdh.Arm.KeySearch.stackWord_store (i := 0) _ _ _ (by decide) (by omega)]
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl | rfl <;> simp [callValue]

theorem call_stackArg {p : SearchParams} {used : Nat} {s : State} {m : Mem} {j : Nat}
    (fit : s.sp.toNat + 20 ≤ 2 ^ 32) (memory : s.mem = callMem p used m s.sp) (bound : j < 5) :
    stackArg (callState p used s) j = callValue p used j := by
  change s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * j))) 32 = _
  rw [VG.Arm.addr_add (by omega), memory]
  exact callMem_word _ _ _ _ bound

end VG.Proof.Ffdh.Arm.ParameterSearch
