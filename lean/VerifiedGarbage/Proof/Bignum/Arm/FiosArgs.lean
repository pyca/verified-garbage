module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! Load both operands, inverse and independent carries for an integrated row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm)

theorem args_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n i inv) (hi : i<n)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios.args) s fun t =>
      t.gpr .r1=s.mem.readW (off (State.addr base) (a+4*i)) 32 ∧
      t.gpr .r0=base+BitVec.ofNat 32 acc ∧ t.gpr .r12=base+BitVec.ofNat 32 b ∧
      t.gpr .r4=base+BitVec.ofNat 32 mod ∧ t.gpr .r2=inv ∧
      t.gpr .lr=BitVec.ofNat 32 n ∧ t.gpr .r7=0 ∧ t.gpr .r8=0 ∧ t.mem=s.mem ∧
      Rest [.r0,.r1,.r2,.r4,.r7,.r8,.r12,.lr] s t := by
  have ws := ctx.workspace
  have ht := ctx.tmpFits
  have ha := ctx.aFits
  have haf : a+4*i+4≤size := by omega
  unfold VG.Impl.Bignum.Arm.Fios.args
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have w1 := ws.congr u1.wr
  refine wp_ldr (a:=off (State.addr base) (a+4*i)) (by decide)
    (w1.ea (off:=a+4*i) (imm:=0) (u1.gpr.trans hdr.aPtr) (by omega))
    (w1.read haf) fun s2 u2 => ?_
  have k2 : Rest [.r1] s s2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  have p2 : s2.gpr .r0=base+BitVec.ofNat 32 tmp := (k2.gpr .r0 (by simp)).trans ptr
  have w2 := ws.congr k2.wr
  refine wp_ldr (a:=off (State.addr base) tmp) (by decide) (w2.ea p2 (by omega))
    (w2.read (by omega)) fun s3 u3 => ?_
  have k3 : Rest [.r1,.lr] s s3 := (k2.mono (by simp_all)).trans (u3.rest (by simp))
  have p3 : s3.gpr .r0=base+BitVec.ofNat 32 tmp := (k3.gpr .r0 (by simp)).trans ptr
  have w3 := ws.congr k3.wr
  refine wp_ldr (by decide) (w3.ea p3 (by omega)) (w3.read (by omega)) fun s4 u4 => ?_
  have k4 : Rest [.r1,.lr,.r12] s s4 := (k3.mono (by simp_all)).trans (u4.rest (by simp))
  have p4 : s4.gpr .r0=base+BitVec.ofNat 32 tmp := (k4.gpr .r0 (by simp)).trans ptr
  have w4 := ws.congr k4.wr
  refine wp_ldr (by decide) (w4.ea p4 (by omega)) (w4.read (by omega)) fun s5 u5 => ?_
  have k5 : Rest [.r1,.lr,.r12,.r4] s s5 := (k4.mono (by simp_all)).trans (u5.rest (by simp))
  have p5 : s5.gpr .r0=base+BitVec.ofNat 32 tmp := (k5.gpr .r0 (by simp)).trans ptr
  have w5 := ws.congr k5.wr
  refine wp_ldr (by decide) (w5.ea p5 (by omega)) (w5.read (by omega)) fun s6 u6 => ?_
  have k6 : Rest [.r1,.lr,.r12,.r4,.r2] s s6 := (k5.mono (by simp_all)).trans (u6.rest (by simp))
  have p6 : s6.gpr .r0=base+BitVec.ofNat 32 tmp := (k6.gpr .r0 (by simp)).trans ptr
  have w6 := ws.congr k6.wr
  refine wp_ldr (by decide) (w6.ea p6 (by omega)) (w6.read (by omega)) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u9 => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,u9.gpr,?_,?_⟩
  · rw [u9.other .r1 (by decide),u8.other .r1 (by decide),u7.other .r1 (by decide),
      u6.other .r1 (by decide),u5.other .r1 (by decide),u4.other .r1 (by decide),
      u3.other .r1 (by decide),u2.gpr,u1.mem]
  · rw [u9.other .r0 (by decide),u8.other .r0 (by decide),u7.gpr,
      u6.mem,u5.mem,u4.mem,u3.mem,u2.mem,u1.mem,hdr.accPtr]
  · rw [u9.other .r12 (by decide),u8.other .r12 (by decide),u7.other .r12 (by decide),
      u6.other .r12 (by decide),u5.other .r12 (by decide),u4.gpr,
      u3.mem,u2.mem,u1.mem,hdr.bPtr]
  · rw [u9.other .r4 (by decide),u8.other .r4 (by decide),u7.other .r4 (by decide),
      u6.other .r4 (by decide),u5.gpr,u4.mem,u3.mem,u2.mem,u1.mem,hdr.mPtr]
  · rw [u9.other .r2 (by decide),u8.other .r2 (by decide),u7.other .r2 (by decide),
      u6.gpr,u5.mem,u4.mem,u3.mem,u2.mem,u1.mem,hdr.inverse]
  · rw [u9.other .lr (by decide),u8.other .lr (by decide),u7.other .lr (by decide),
      u6.other .lr (by decide),u5.other .lr (by decide),u4.other .lr (by decide),
      u3.gpr,u2.mem,u1.mem,hdr.count]
  · rw [u9.other .r7 (by decide),u8.gpr]
  · rw [u9.mem,u8.mem,u7.mem,u6.mem,u5.mem,u4.mem,u3.mem,u2.mem,u1.mem]
  · exact (k6.mono (by simp_all)).trans ((u7.rest (by simp)).trans
      ((u8.rest (by simp)).trans (u9.rest (by simp))))

end VG.Proof.Bignum.Arm.Fios
