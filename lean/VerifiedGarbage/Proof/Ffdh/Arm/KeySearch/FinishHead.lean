module

public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The controller returns its status and writes a full u64 entropy-consumption count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def usedMem (m : Mem) (ptr : BitVec 32) (count : BitVec 32) : Mem :=
  (m.writeW (State.addr ptr) count).writeW (off (State.addr ptr) 4) (0#32)

theorem usedMem_frame (m : Mem) (ptr : BitVec 32) (count : BitVec 32) :
    Frame [⟨State.addr ptr, 8⟩] m (usedMem m ptr count) := by
  have first : Frame [⟨State.addr ptr, 8⟩] m (m.writeW (State.addr ptr) count) :=
    (Frame.refl _ _).writeW (r := ⟨State.addr ptr, 8⟩) (by simp) count
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  exact first.writeW (by simp) _ (Offset.contains_base _ (by decide : 4 + 4 ≤ 8) (by decide))

theorem usedMem_words (m : Mem) (ptr : BitVec 32) (count : Nat) (fits : count < 2 ^ 32) :
    Spec.Rsa.wordsAt (usedMem m ptr (BitVec.ofNat 32 count)) (State.addr ptr) 1 = [BitVec.ofNat 64 count] := by
  have paired : usedMem m ptr (BitVec.ofNat 32 count) =
      m.writeW (State.addr ptr) ((0#32) ++ BitVec.ofNat 32 count) := by
    exact (VG.Proof.Rc2.Word32.write64_pair _ _ _ _).symm
  have value : ((0#32) ++ BitVec.ofNat 32 count) = BitVec.ofNat 64 count := by
    have zero32 : (0 : BitVec 32) = 0#32 := rfl
    simpa only [zero32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] using zeroHigh (BitVec.ofNat 32 count)
  have one (mem : Mem) (a : Addr) : Spec.Rsa.wordsAt mem a 1 = [mem.readW a 64] := by
    simp only [Spec.Rsa.wordsAt, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
      Nat.mul_zero, BitVec.add_zero]
  rw [one, paired, value, Mem.readW_writeW_self64]

theorem finishHead_ok (s : State) {base ptr : BitVec 32} {count status : Nat}
    (h : Controller base s) (output : OutputBuffer ptr 8 s)
    (pointer : lowWord s.mem base 15 = ptr) (used : lowWord s.mem base 11 = BitVec.ofNat 32 count)
    (result : lowWord s.mem base 14 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧ t.mem = usedMem s.mem ptr (BitVec.ofNat 32 count)) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  refine withRest [.r0, .r1, .r2, .r3] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 15,
        VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 11, VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 14,
        .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  have write0 : InRegions s.wr (State.addr ptr) 4 := by
    simpa only [BitVec.add_zero] using
      CallLay.inRegions_sub output.writable (off := 0) (by decide : 0 + 4 ≤ 8) (by decide)
  have write4 : InRegions s.wr (off (State.addr ptr) 4) 4 :=
    CallLay.inRegions_sub output.writable (by decide : 4 + 4 ≤ 8) (by decide)
  have addr4 : State.addr (ptr + 4#32) = off (State.addr ptr) 4 := VG.Arm.addr_add (by have := output.fits; omega)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord usedMem at *
  ffrun [h.addr (by decide : 15 < 16), h.addr (by decide : 11 < 16), h.addr (by decide : 14 < 16),
    h.read (by decide : 15 < 16), h.read (by decide : 11 < 16), h.read (by decide : 14 < 16),
    pointer, used, result, BitVec.add_zero, addr4, write0, write4]
  rfl

end VG.Proof.Ffdh.Arm.KeySearch
