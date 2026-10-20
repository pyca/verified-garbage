module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Incoming
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The 24-byte ARM key-search frame saves exactly the registers its body
needs to restore, with one padding word maintaining AAPCS alignment. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

abbrev searchPushed (s : State) : State := pushed [.r4, .r9, .r10, .r11, .r12, .lr] s

theorem push_saved (s : State) (fits : 24 ≤ s.sp.toNat) :
    Spill.Saved (searchPushed s).mem (State.addr (s.sp - 24#32)) s.gpr savedSlots := by
  let sp := s.sp - 24#32
  have bound : sp.toNat + 24 ≤ 2 ^ 32 := by
    rw [show sp = s.sp - 24#32 from rfl, FrameStack.sub_toNat' fits]
    have := s.sp.isLt
    omega
  have address (k : Nat) (hk : k < 24) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    VG.Arm.addr_add (by omega)
  have memEq : (searchPushed s).mem = Spill.saveMem s.mem (State.addr sp) s.gpr savedSlots := by
    change storeWords s.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem, savedSlots]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide), address 20 (by decide)]
    simp only [off, BitVec.add_zero]
  rw [memEq]
  exact Spill.saveMem_saved (lo := 0) (hi := 24) (State.addr sp) s.gpr s.mem savedSlots (by decide)

theorem KeyInput.incoming_value {p : KeyPublic} {s : State} {i : Nat} (h : KeyInput p s) (bound : i < 9) :
    stackArg s i = incomingValue p i := by
  rw [← h.2]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [incomingValue, keyOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Ffdh.Arm.KeySearch
