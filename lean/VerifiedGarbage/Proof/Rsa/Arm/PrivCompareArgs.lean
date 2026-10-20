module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.Rsa.SuccessBits32
public import Batteries.Logic
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Set up the private fault comparison and accumulate the three call-status bits -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_reg op2_imm dpVal)

abbrev successBits := VG.Proof.Rsa.successBits

theorem successBits_cases (r2 r1 r3 : BitVec 32) : successBits r2 r1 r3 = 0 ∨ successBits r2 r1 r3 = 1 :=
  VG.Proof.Rsa.successBits_cases r2 r1 r3

theorem cmpArgs_ok (s : State) (ws : Workspace s s.sp frameBytes) :
    WP isa (.block cmpArgs) s fun t =>
      t.gpr .r0 = s.mem.readW (off (State.addr s.sp) oOut) 32 ∧
      t.gpr .r1 = s.mem.readW (off (State.addr s.sp) oIn) 32 ∧
      t.gpr .lr = s.mem.readW (off (State.addr s.sp) oK) 32 ∧ t.gpr .r2 = 0 ∧
      t.gpr .r4 = successBits (s.gpr .r0) (s.mem.readW (off (State.addr s.sp) oR1) 32)
        (s.mem.readW (off (State.addr s.sp) oR3) 32) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .lr] s t := by
  have fit := ws.nowrap
  unfold cmpArgs
  refine wp_loadStack (a := off (State.addr s.sp) oR1) (by decide)
    (addr_add (by simp only [oR1, frameBytes] at *; omega)) (ws.read (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oR3) (by decide)
    (by rw [u2.sp, u1.sp]; exact addr_add (by simp only [oR3, frameBytes] at *; omega))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  have status : s5.gpr .r4 = successBits (s.gpr .r0) (s.mem.readW (off (State.addr s.sp) oR1) 32)
      (s.mem.readW (off (State.addr s.sp) oR3) 32) := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, u3.other .r4 (by decide), u2.gpr, dpVal,
      u1.gpr, u1.other .r0 (by decide), u3.gpr, u2.mem, u1.mem]
    rfl
  have keep5 : Rest [.r3, .r4] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  have mem5 : s5.mem = s.mem := u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))
  refine wp_loadStack (a := off (State.addr s.sp) oOut) (by decide)
    (by rw [keep5.sp]; exact addr_add (by simp only [oOut, frameBytes] at *; omega))
    (by rw [keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s6 u6 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oIn) (by decide)
    (by rw [u6.sp, keep5.sp]; exact addr_add (by simp only [oIn, frameBytes] at *; omega))
    (by rw [u6.rd, u6.wr, keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s7 u7 => ?_
  refine wp_loadStack (a := off (State.addr s.sp) oK) (by decide)
    (by rw [u7.sp, u6.sp, keep5.sp]; exact addr_add (by simp only [oK, frameBytes] at *; omega))
    (by rw [u7.rd, u7.wr, u6.rd, u6.wr, keep5.rd, keep5.wr]; exact ws.read (by decide)) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u9 => WP.block_nil ?_
  exact ⟨by rw [u9.other .r0 (by decide), u8.other .r0 (by decide), u7.other .r0 (by decide), u6.gpr, mem5],
    by rw [u9.other .r1 (by decide), u8.other .r1 (by decide), u7.gpr, u6.mem, mem5],
    by rw [u9.other .lr (by decide), u8.gpr, u7.mem, u6.mem, mem5], u9.gpr,
    by rw [u9.other .r4 (by decide), u8.other .r4 (by decide), u7.other .r4 (by decide), u6.other .r4 (by decide), status],
    u9.mem.trans (u8.mem.trans (u7.mem.trans (u6.mem.trans mem5))),
    (keep5.mono (by simp)).trans ((u6.rest (by simp)).trans
      ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))⟩
end VG.Proof.Rsa.Arm
