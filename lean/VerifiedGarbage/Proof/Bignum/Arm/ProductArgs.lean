module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Load a Montgomery product row's arguments from its temporary state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm)

theorem productArgs_ok (s : State) {base : BitVec 32} {size tmp a b acc n : Nat}
    (ws : Workspace s base size) (ht : tmp + 32 ≤ size) (ha : a + 4 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (ma : s.mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 a)
    (mn : s.mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n)
    (mb : s.mem.readW (off (State.addr base) (tmp + 4)) 32 = base + BitVec.ofNat 32 b)
    (macc : s.mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc) :
    WP isa (.block productArgs) s fun t =>
      t.gpr .r1 = s.mem.readW (off (State.addr base) a) 32 ∧
      t.gpr .r0 = base + BitVec.ofNat 32 acc ∧ t.gpr .r12 = base + BitVec.ofNat 32 b ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r11, .r12, .lr] s t := by
  unfold productArgs
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have w1 := ws.congr u1.wr
  refine wp_ldr (a := off (State.addr base) a) (by decide)
    (w1.ea (u1.gpr.trans ma) (by omega)) (w1.read ha) fun s2 u2 => ?_
  have k2 : Rest [.r1] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have p2 : s2.gpr .r0 = base + BitVec.ofNat 32 tmp := (k2.gpr .r0 (by decide)).trans ptr
  have w2 := ws.congr k2.wr
  refine wp_ldr (a := off (State.addr base) tmp) (by decide) (w2.ea p2 (by omega))
    (w2.read (by omega)) fun s3 u3 => ?_
  have k3 : Rest [.r1, .lr] s s3 := (k2.mono (by simp_all)).trans (u3.rest (by decide))
  have p3 : s3.gpr .r0 = base + BitVec.ofNat 32 tmp := (k3.gpr .r0 (by decide)).trans ptr
  have w3 := ws.congr k3.wr
  refine wp_ldr (by decide) (w3.ea p3 (by omega)) (w3.read (by omega)) fun s4 u4 => ?_
  have k4 : Rest [.r1, .lr, .r12] s s4 := (k3.mono (by simp_all)).trans (u4.rest (by decide))
  have p4 : s4.gpr .r0 = base + BitVec.ofNat 32 tmp := (k4.gpr .r0 (by decide)).trans ptr
  have w4 := ws.congr k4.wr
  refine wp_ldr (by decide) (w4.ea p4 (by omega)) (w4.read (by omega)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, u6.gpr, ?_, ?_⟩
  · rw [u6.other .r1 (by decide), u5.other .r1 (by decide), u4.other .r1 (by decide),
      u3.other .r1 (by decide), u2.gpr, u1.mem]
  · rw [u6.other .r0 (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, macc]
  · rw [u6.other .r12 (by decide), u5.other .r12 (by decide), u4.gpr, u3.mem, u2.mem, u1.mem, mb]
  · rw [u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.gpr, u2.mem, u1.mem, mn]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (k4.mono (by simp_all)).trans ((u5.rest (by decide)).trans (u6.rest (by decide)))

end VG.Proof.Bignum.Arm
