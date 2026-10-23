module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.Block

/-! # SM4's linear map with shifted-register XORs -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial

theorem rotate_complement (x : BitVec 32) (r : Nat) (hr : 0 < r) (hr' : r < 32) :
    x.rotateRight (32-r) = x.rotateLeft r := by
  rw [BitVec.rotateRight_def,BitVec.rotateLeft_def,Nat.mod_eq_of_lt hr',
    Nat.mod_eq_of_lt (show 32-r < 32 by omega),Nat.sub_sub_self (by omega : r ≤ 32)]
  exact BitVec.or_comm _ _

theorem linear_eq (x : BitVec 32) :
    x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 ^^^ x.rotateRight 8 =
      Spec.Sm4.linear x := by
  rw [show 30 = 32-2 by rfl,rotate_complement x 2 (by decide) (by decide),
    show 22 = 32-10 by rfl,rotate_complement x 10 (by decide) (by decide),
    show 14 = 32-18 by rfl,rotate_complement x 18 (by decide) (by decide),
    show 8 = 32-24 by rfl,rotate_complement x 24 (by decide) (by decide)]
  rfl

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      t.gpr .x11 = (Spec.Sm4.linear ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ≠ .x11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let x := (s.gpr .x10).setWidth 32
  let a := s.write .w .x11 (x ^^^ x.rotateRight 30)
  let b := a.write .w .x11 ((a.read .w .x11) ^^^ x.rotateRight 22)
  let c := b.write .w .x11 ((b.read .w .x11) ^^^ x.rotateRight 14)
  let d := c.write .w .x11 ((c.read .w .x11) ^^^ x.rotateRight 8)
  refine ⟨d,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [linear,runBlock_cons,exec_logicRor (sz := .w) (sh := 30) (by decide),
      exec_logicRor (sz := .w) (sh := 22) (by decide),
      exec_logicRor (sz := .w) (sh := 14) (by decide),
      exec_logicRor (sz := .w) (sh := 8) (by decide),runStep_some,runBlock_nil]
    rfl
  · simp only [d,c,b,a,gpr_write_self,State.read,Size.bits]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rw [linear_eq]
  · intro r hr
    simp only [d,c,b,a,gpr_write_of_ne _ _ _ hr]

end VG.Proof.Sm4.AArch64.Serial
