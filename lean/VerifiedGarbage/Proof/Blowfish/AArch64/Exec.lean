import VerifiedGarbage.Impl.Blowfish.AArch64
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-!
# Instructions of the batch code, one at a time

What each kind of instruction of `Impl/Blowfish/AArch64.lean` does to a
state (`exec_*`), and which vector registers a block may change (`VOnly`).
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

theorem exec_veor (s : State) (d n m : VReg) :
    exec (veor d n m) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_vperm (s : State) (op : VPermOp) (a : VArr) (d n m : VReg) :
    exec (vperm op a d n m) s = some (s.setV d (op.eval a (s.v n) (s.v m))) := rfl

theorem exec_vmov (s : State) (d n : VReg) :
    exec (.vop (.mov d n)) s = some (s.setV d (s.v n)) := rfl

theorem exec_vadd (s : State) (d n m : VReg) :
    exec (.vop (.add .s4 d n m)) s =
      some (s.setV d (VArr.s4.map2 (fun _ x y => x + y) (s.v n) (s.v m))) := rfl

theorem exec_dup4 (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .s4 d n)) s =
      some (s.setV d (let w := (s.gpr n).setWidth 32; ofVWords w w w w)) := rfl

theorem exec_rev32b (s : State) (d n : VReg) :
    exec (.vop (.rev .rev32b d n)) s = some (s.setV d (VRevOp.eval .rev32b (s.v n))) := rfl

theorem exec_tbl4 (s : State) (x : Bool) (d n m : VReg) :
    exec (.vop (.tblN x 4 d n m)) s = some (s.setV d (ofVBytes fun i =>
      if (vbyte (s.v m) i).toNat < 16 * 4 then tableByte s.v n (vbyte (s.v m) i).toNat
      else if x then vbyte (s.v d) i else 0)) := rfl

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show off < 4096 * 16 by omega, ho, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off < 4096 * 16 by omega, ho, and_self, ite_true, Option.bind_some,
    State.store, h]

end VG.Proof.Blowfish.AArch64
