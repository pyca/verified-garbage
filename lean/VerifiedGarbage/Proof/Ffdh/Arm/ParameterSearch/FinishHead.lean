module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Code

/-! The controller returns its status and writes a full u64 entropy-consumption count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord usedMem)

theorem finishHead_ok (s : State) {base ptr : BitVec 32} {count status : Nat}
    (h : Controller base s) (output : OutputBuffer ptr 8 s)
    (pointer : lowWord s.mem base 6 = ptr) (used : lowWord s.mem base 4 = BitVec.ofNat 32 count)
    (result : lowWord s.mem base 13 = BitVec.ofNat 32 status) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4]) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 status ∧ t.mem = usedMem s.mem ptr (BitVec.ofNat 32 count)) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  refine withRest [.r0, .r1, .r2, .r3] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r1 6,
        VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r2 4, VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r0 13,
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
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord usedMem at *
  ffrun [h.addr (by decide : 6 < 16), h.addr (by decide : 4 < 16), h.addr (by decide : 13 < 16),
    h.read (by decide : 6 < 16), h.read (by decide : 4 < 16), h.read (by decide : 13 < 16),
    pointer, used, result, BitVec.add_zero, addr4, write0, write4]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
