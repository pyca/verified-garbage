module
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! Saved argument and procedure-call registers in the shared arithmetic frame. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
def callAllSaved : List (Reg × Nat) :=
  [(.r0, 0), (.r4, 4), (.r5, 8), (.r6, 12), (.r7, 16), (.r8, 20),
   (.r9, 24), (.r10, 28), (.r11, 32), (.lr, 36)]
abbrev callPushed (s : State) : State := pushed MontCall.savedRegs s

theorem call_push_saved (s : State) (fit : 40 ≤ s.sp.toNat) :
    Spill.Saved (callPushed s).mem (State.addr (s.sp - 40)) s.gpr callAllSaved := by
  let sp := s.sp - 40
  have bound : sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [show sp = s.sp - BitVec.ofNat 32 40 from rfl, FrameStack.sub_toNat' fit]
    have := s.sp.isLt
    omega
  have address (k : Nat) (hk : k < 40) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    addr_add (by omega)
  have memEq : (callPushed s).mem = Spill.saveMem s.mem (State.addr sp) s.gpr callAllSaved := by
    change storeWords s.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem, callAllSaved, MontCall.savedRegs]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide),
      address 20 (by decide), address 24 (by decide), address 28 (by decide), address 32 (by decide), address 36 (by decide)]
    simp only [off, BitVec.add_zero]
  rw [memEq]
  exact Spill.saveMem_saved (lo := 0) (hi := 40) (State.addr sp) s.gpr s.mem callAllSaved (by decide)

def callCalleeSaved : List (Reg × Nat) :=
  [(.r4, 4), (.r5, 8), (.r6, 12), (.r7, 16), (.r8, 20),
   (.r9, 24), (.r10, 28), (.r11, 32), (.lr, 36)]

theorem call_restore_ok (s : State) (g : Reg → BitVec 32)
    (fit : s.sp.toNat + 40 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 40)
    (saved : Spill.Saved s.mem (State.addr s.sp) g callAllSaved) :
    WP isa (.block MontCall.restore) s fun t =>
      (∀ p ∈ callCalleeSaved, t.gpr p.1 = g p.1) ∧ t.mem = s.mem ∧
      VG.Proof.X25519.Arm.Rest (callCalleeSaved.map Prod.fst) s t := by
  apply restoreSlots_ok callCalleeSaved s g (by decide) fit read
    (by intro p hp; simp only [callCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  intro p hp
  apply saved p
  simp only [callCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [callAllSaved]


end VG.Proof.Bignum.Arm
