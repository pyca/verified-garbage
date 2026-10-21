module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller

/-! Request arithmetic loads bounded public values and stores a complete u64 request. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem requestHead_ok (s : State) {base : BitVec 32} {available width : Nat}
    (h : Controller base s) (tape : lowWord s.mem base 10 = BitVec.ofNat 32 available)
    (length : lowWord s.mem base 1 = BitVec.ofNat 32 width) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1, .mov .r10 (.shifted .r10 .lsl 8)]) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 32 available ∧ t.gpr .r10 = BitVec.ofNat 32 (256 * width) ∧
        t.mem = s.mem) ∧ Rest [.r9, .r10] s t := by
  refine withRest [.r9, .r10] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
        VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1, .mov .r10 (.shifted .r10 .lsl 8)] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord at *
  ffrun [h.addr (by decide : 10 < 16), h.addr (by decide : 1 < 16),
    h.read (by decide : 10 < 16), h.read (by decide : 1 < 16), tape, length]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem requestDouble_ok (s : State) {base : BitVec 32} {n cap : Nat}
    (h : Controller base s) (value : s.gpr .r9 = BitVec.ofNat 32 n)
    (capacity : lowWord s.mem base 2 = BitVec.ofNat 32 cap) :
    WP isa (.block [.dp .add .r9 .r9 (.reg .r9), VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2]) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 32 (2 * n) ∧ t.gpr .r10 = BitVec.ofNat 32 cap ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10] s t := by
  refine withRest [.r9, .r10] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [.dp .add .r9 .r9 (.reg .r9),
        VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord at *
  ffrun [h.addr (by decide : 2 < 16), h.read (by decide : 2 < 16), value, capacity]
  rw [← BitVec.ofNat_add]
  congr 1
  omega

def requestMem (m : Mem) (base : BitVec 32) (request : Nat) : Mem :=
  ((m.writeW (off (State.addr base) 24) (BitVec.ofNat 32 request)).writeW
    (off (State.addr base) 28) (0#32)).writeW (off (State.addr base) 104) (0#32)

theorem requestStore_ok (s : State) {base : BitVec 32} {request : Nat}
    (h : Controller base s) (value : s.gpr .r9 = BitVec.ofNat 32 request) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 3, .mov .r11 (.imm 0),
      .str .r11 .r4 28, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13]) s fun t =>
      t.mem = requestMem s.mem base request ∧ Rest [.r11] s t := by
  refine withRest [.r11] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 3, .mov .r11 (.imm 0),
        .str .r11 .r4 28, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf requestMem
  ffrun [controllerAddr h 24 (by decide), controllerAddr h 28 (by decide), controllerAddr h 104 (by decide),
    h.space.write (off := 24) (by decide), h.space.write (off := 28) (by decide),
    h.space.write (off := 104) (by decide), value]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
