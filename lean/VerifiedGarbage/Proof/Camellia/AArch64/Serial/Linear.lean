module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Pure
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Scalar execution of Camellia's byte diffusion -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      t.gpr .x10 = linearWord (s.gpr .x10) ∧
      (∀ r, r ∉ [.x10,.x11,.x12,.x16,.x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .x .x11 (s.read .x .x10 >>> 32)
  let b := a.write .w .x12 (a.read .w .x10 + (0 : BitVec 32))
  let c := b.write .w .x16 (b.read .w .x11 ^^^ (b.read .w .x11).rotateRight 8)
  let d := c.write .w .x16 (c.read .w .x16 ^^^ (c.read .w .x11).rotateRight 16)
  let e := d.write .w .x17 ((d.read .w .x12 ++ d.read .w .x12).extractLsb' 8 32)
  let f := e.write .w .x17 (e.read .w .x17 ^^^ (e.read .w .x12).rotateRight 16)
  let g := f.write .w .x17 (f.read .w .x17 ^^^ (f.read .w .x12).rotateRight 24)
  let h := g.write .w .x16 (g.read .w .x16 ^^^ g.read .w .x17)
  let i := h.write .w .x12 (h.read .w .x11 ^^^ (h.read .w .x11).rotateRight 24)
  let j := i.write .w .x12 (i.read .w .x12 ^^^ i.read .w .x17)
  let k := j.write .x .x10 (j.read .x .x16 <<< 32)
  let t := k.write .x .x10 (k.read .x .x10 ||| k.read .x .x12)
  refine ⟨t,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · rfl
  · simp only [t,k,j,i,h,g,f,e,d,c,b,a,State.read,Size.bits,gpr_write,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,
      ↓reduceIte,reduceCtorEq]
    simp only [extract_self _ 8 (by decide)]
    rw [← BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    simp only [BitVec.setWidth_eq]
    simp only [show ∀ x : BitVec 32, x + (0 : BitVec 32) = x from
      fun x => BitVec.add_zero x,linearWord]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [t,k,j,i,h,g,f,e,d,c,b,a,gpr_write_of_ne _ _ _ hr.1,
      gpr_write_of_ne _ _ _ hr.2.1,gpr_write_of_ne _ _ _ hr.2.2.1,
      gpr_write_of_ne _ _ _ hr.2.2.2.1,gpr_write_of_ne _ _ _ hr.2.2.2.2]

end VG.Proof.Camellia.AArch64.Serial
