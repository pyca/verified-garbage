module

public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Division loop arguments depend only on the public header -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont
open VG.Proof.X25519.Arm

theorem quotientArgs_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.block quotientArgs) s fun t =>
      t.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 0) ∧
      t.gpr .lr = BitVec.ofNat 32 g.n ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Context g t ∧ Rest [.r0, .lr, .r11] s t := by
  unfold quotientArgs
  refine h.loadPtr 0 (by decide) fun s1 u1 h1 => ?_
  refine h1.loadCount (by decide) fun s2 u2 h2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
  exact ⟨(u3.other .r0 (by decide)).trans ((u2.other .r0 (by decide)).trans u1.gpr),
    (u3.other .lr (by decide)).trans u2.gpr, u3.gpr,
    u3.mem.trans (u2.mem.trans u1.mem), h2.of_update u3 (by decide),
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))⟩

theorem remainderArgs_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.block remainderArgs) s fun t =>
      t.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (g.n + 1) ∧
      t.mem = s.mem ∧ Context g t ∧ Rest [.r0, .lr] s t := by
  unfold remainderArgs
  refine h.loadPtr 1 (by decide) fun s1 u1 h1 => ?_
  refine h1.loadCount (by decide) fun s2 u2 h2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
  refine ⟨(u3.other .r0 (by decide)).trans ((u2.other .r0 (by decide)).trans u1.gpr), ?_,
    u3.mem.trans (u2.mem.trans u1.mem), h2.of_update u3 (by decide),
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))⟩
  rw [u3.gpr, dpVal, u2.gpr, BitVec.ofNat_add]
  rfl

theorem subtractArgs_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.block subtractArgs) s fun t =>
      t.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 3) ∧
      t.gpr .r10 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
      t.gpr .r12 = g.base + BitVec.ofNat 32 (g.offsets 2) ∧
      t.gpr .r9 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
      t.gpr .r7 = BitVec.ofNat 32 (g.n + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (g.n + 1) ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Context g t ∧ Rest [.r0, .r7, .r9, .r10, .r11, .r12, .lr] s t := by
  unfold subtractArgs
  refine h.loadPtr 3 (by decide) fun s1 u1 h1 => ?_
  refine h1.loadPtr 1 (by decide) fun s2 u2 h2 => ?_
  refine h2.loadPtr 2 (by decide) fun s3 u3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine (h3.of_update u4 (by decide)).loadCount (by decide) fun s5 u5 h5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_mov (op2_reg _ _) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u8 => WP.block_nil ?_
  have cnt : s6.gpr .r7 = BitVec.ofNat 32 (g.n + 1) := by
    rw [u6.gpr, dpVal, u5.gpr, BitVec.ofNat_add]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, u8.gpr, ?_, ?_, ?_⟩
  · rw [u8.other .r0 (by decide), u7.other .r0 (by decide), u6.other .r0 (by decide),
      u5.other .r0 (by decide), u4.other .r0 (by decide), u3.other .r0 (by decide),
      u2.other .r0 (by decide), u1.gpr]
  · rw [u8.other .r10 (by decide), u7.other .r10 (by decide), u6.other .r10 (by decide),
      u5.other .r10 (by decide), u4.other .r10 (by decide), u3.other .r10 (by decide), u2.gpr]
  · rw [u8.other .r12 (by decide), u7.other .r12 (by decide), u6.other .r12 (by decide),
      u5.other .r12 (by decide), u4.other .r12 (by decide), u3.gpr]
  · rw [u8.other .r9 (by decide), u7.other .r9 (by decide), u6.other .r9 (by decide),
      u5.other .r9 (by decide), u4.gpr, u3.other .r10 (by decide), u2.gpr]
  · rw [u8.other .r7 (by decide), u7.other .r7 (by decide), cnt]
  · rw [u8.other .lr (by decide), u7.gpr, cnt]
  · exact u8.mem.trans (u7.mem.trans (u6.mem.trans (u5.mem.trans
      (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem))))))
  · exact ((h5.of_update u6 (by decide)).of_update u7 (by decide)).of_update u8 (by decide)
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans
        ((u7.rest (by simp)).trans (u8.rest (by simp))))))))

end VG.Proof.Rsa.Arm.Div
