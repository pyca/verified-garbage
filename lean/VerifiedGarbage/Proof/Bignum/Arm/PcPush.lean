module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.RestoreSlots
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The public RSA frame saves arguments and all callee-saved registers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

def pcAllSaved : List (Reg × Nat) :=
  [(.r0, 0), (.r1, 4), (.r2, 8), (.r3, 12), (.r4, 16), (.r5, 20), (.r6, 24),
   (.r7, 28), (.r8, 32), (.r9, 36), (.r10, 40), (.r11, 44), (.r12, 48), (.lr, 52)]
def pcCalleeSaved : List (Reg × Nat) :=
  [(.r4, 16), (.r5, 20), (.r6, 24), (.r7, 28), (.r8, 32), (.r9, 36), (.r10, 40), (.r11, 44), (.lr, 52)]
abbrev pcPushed (s : State) : State :=
  pushed [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] s

theorem pc_push_saved (s : State) (fit : 56 ≤ s.sp.toNat) :
    Spill.Saved (pcPushed s).mem (State.addr (s.sp - 56)) s.gpr pcAllSaved := by
  let sp := s.sp - 56
  have bound : sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [show sp = s.sp - BitVec.ofNat 32 56 from rfl, FrameStack.sub_toNat' fit]
    have := s.sp.isLt
    omega
  have address (k : Nat) (hk : k < 56) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    addr_add (by omega)
  have memEq : (pcPushed s).mem = Spill.saveMem s.mem (State.addr sp) s.gpr pcAllSaved := by
    change storeWords s.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem, pcAllSaved]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide),
      address 20 (by decide), address 24 (by decide), address 28 (by decide), address 32 (by decide),
      address 36 (by decide), address 40 (by decide), address 44 (by decide), address 48 (by decide), address 52 (by decide)]
    simp only [off, BitVec.add_zero]
  rw [memEq]
  exact Spill.saveMem_saved (lo := 0) (hi := 56) (State.addr sp) s.gpr s.mem pcAllSaved (by decide)

theorem pc_push_callee_saved (s : State) (fit : 56 ≤ s.sp.toNat) :
    Spill.Saved (pcPushed s).mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved := by
  intro p hp
  apply pc_push_saved s fit p
  simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pcAllSaved]

theorem pc_restore_ok (s : State) (g : Reg → BitVec 32)
    (fit : s.sp.toNat + 56 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 56)
    (saved : Spill.Saved s.mem (State.addr s.sp) g pcCalleeSaved) :
    WP isa (.block PcFn.restore) s fun t =>
      (∀ p ∈ pcCalleeSaved, t.gpr p.1 = g p.1) ∧ t.mem = s.mem ∧
      VG.Proof.X25519.Arm.Rest (pcCalleeSaved.map Prod.fst) s t :=
  restoreSlots_ok pcCalleeSaved s g (by decide) fit read
    (by intro p hp; simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) saved

end VG.Proof.Bignum.Arm
