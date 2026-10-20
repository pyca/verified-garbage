module

public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The low Montgomery word cancels without being stored or shifted. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp wp_subs op2_reg op2_imm dpVal)

theorem first_ok (s : State) {base : BitVec 32} {size acc mod n : Nat}
    (ws : Workspace s base size) (accFit : acc+4≤size) (modFit : mod+4≤size)
    (positive : 0<n) (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carry : s.gpr .r11=0)
    (cancel : ((s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc)%2^32=0) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.first s fun t =>
      t.gpr .r0=base+BitVec.ofNat 32 acc ∧
      t.gpr .r12=base+BitVec.ofNat 32 (mod+4) ∧
      t.gpr .lr=BitVec.ofNat 32 (n-1) ∧ t.gpr .r1=s.gpr .r1 ∧
      2^32*(t.gpr .r11).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
        w32 s.mem (State.addr base) acc ∧
      t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.first, WP.seq_iff]
  have args : WP isa (.block VG.Impl.Bignum.Arm.FusedReduction.firstArgs) s fun u =>
      u.gpr .r2=s.mem.readW (off (State.addr base) mod) 32 ∧
      u.gpr .r10=s.mem.readW (off (State.addr base) acc) 32 ∧
      u.mem=s.mem ∧ Rest [.r2,.r10] s u := by
    unfold VG.Impl.Bignum.Arm.FusedReduction.firstArgs
    refine wp_ldr (a:=off (State.addr base) mod) (by decide)
      (by simpa only [Nat.add_zero] using ws.ea source (imm:=0) (by omega)) (ws.read modFit) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) acc) (by decide)
      (by rw [h.other .r0 (by decide)]; simpa only [Nat.add_zero] using ws.ea ptr (imm:=0) (by omega))
      (by rw [h.rd,h.wr]; exact ws.read accFit) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r2 (by decide)).trans h.gpr,
      by rw [k.gpr,h.mem],k.mem.trans h.mem,(h.rest (by simp)).trans (k.rest (by simp))⟩
  refine WP.mono args ?_
  rintro u ⟨input,accumulator,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (mac_ok u) ?_
  rintro v ⟨value,frame⟩
  have r0 : v.gpr .r0=base+BitVec.ofNat 32 acc :=
    (frame.regs .r0 (by simp [clobbers])).trans ((restU.gpr .r0 (by simp)).trans ptr)
  have r1 : v.gpr .r1=s.gpr .r1 :=
    (frame.regs .r1 (by simp [clobbers])).trans (restU.gpr .r1 (by simp))
  have r12 : v.gpr .r12=base+BitVec.ofNat 32 mod :=
    (frame.regs .r12 (by simp [clobbers])).trans ((restU.gpr .r12 (by simp)).trans source)
  have lr : v.gpr .lr=BitVec.ofNat 32 n :=
    (frame.regs .lr (by simp [clobbers])).trans ((restU.gpr .lr (by simp)).trans count)
  rw [restU.gpr .r1 (by simp),input,accumulator,restU.gpr .r11 (by simp),carry] at value
  simp only [show (0:BitVec 32).toNat=0 from rfl,Nat.add_zero] at value
  have high : 2^32*(v.gpr .r4).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc := by
    change (v.gpr .r3).toNat+(v.gpr .r4).toNat*2^32=_ at value
    have low := (v.gpr .r3).isLt
    dsimp only [w32] at cancel ⊢
    omega
  have kept : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    ((show Rest clobbers u v from ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩).mono
      (by simp [clobbers,roundClobbers]))
  unfold VG.Impl.Bignum.Arm.FusedReduction.firstNext
  refine wp_mov (op2_reg _ _) fun a ha => ?_
  refine wp_dp (op2_imm (by decide)) fun b hb => ?_
  refine wp_subs (op2_imm (by decide)) fun t ht _zero => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r0 (by decide),hb.other .r0 (by decide),ha.other .r0 (by decide)]; exact r0
  · rw [ht.other .r12 (by decide),hb.gpr,dpVal,ha.other .r12 (by decide),r12]
    exact Offset.add_add _ _ _
  · rw [ht.gpr,hb.other .lr (by decide),ha.other .lr (by decide),lr]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) positive
  · rw [ht.other .r1 (by decide),hb.other .r1 (by decide),ha.other .r1 (by decide)]; exact r1
  · rw [ht.other .r11 (by decide),hb.other .r11 (by decide),ha.gpr]; exact high
  · rw [ht.mem,hb.mem,ha.mem,frame.mem,memU]
  · exact kept.trans ((ha.rest (by simp [roundClobbers])).trans
      ((hb.rest (by simp [roundClobbers])).trans (ht.rest (by simp [roundClobbers]))))

end VG.Proof.Bignum.Arm.FusedReduction
