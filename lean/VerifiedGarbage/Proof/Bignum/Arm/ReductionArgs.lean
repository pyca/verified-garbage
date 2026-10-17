module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Load the reduction coefficient, modulus pointer, and packed-word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_mul op2_imm)

theorem reductionArgs_ok (s : State) {base : BitVec 32} {size top acc mod n : Nat}
    (inv : BitVec 32) (ws : Workspace s base size) (ht : top + 48 ≤ size) (ha : acc + 4 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top)
    (mn : s.mem.readW (off (State.addr base) (top + 16)) 32 = BitVec.ofNat 32 n)
    (mm : s.mem.readW (off (State.addr base) (top + 24)) 32 = base + BitVec.ofNat 32 mod)
    (mi : s.mem.readW (off (State.addr base) (top + 28)) 32 = inv)
    (ma : s.mem.readW (off (State.addr base) (top + 44)) 32 = base + BitVec.ofNat 32 acc) :
    WP isa (.block reductionArgs) s fun t =>
      t.gpr .r1 = inv * s.mem.readW (off (State.addr base) acc) 32 ∧
      t.gpr .r0 = base + BitVec.ofNat 32 acc ∧ t.gpr .r12 = base + BitVec.ofNat 32 mod ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r2, .r11, .r12, .lr] s t := by
  unfold reductionArgs
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have w1 := ws.congr u1.wr
  have p1 := (u1.other .r0 (by decide)).trans ptr
  refine wp_ldr (by decide) (w1.ea p1 (by omega)) (w1.read (by omega)) fun s2 u2 => ?_
  have k2 : Rest [.lr, .r12] s s2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  have w2 := ws.congr k2.wr
  have p2 := (k2.gpr .r0 (by simp)).trans ptr
  refine wp_ldr (by decide) (w2.ea p2 (by omega)) (w2.read (by omega)) fun s3 u3 => ?_
  have k3 : Rest [.lr, .r12, .r1] s s3 := (k2.mono (by simp_all)).trans (u3.rest (by simp))
  have w3 := ws.congr k3.wr
  have p3 := (k3.gpr .r0 (by simp)).trans ptr
  refine wp_ldr (by decide) (w3.ea p3 (by omega)) (w3.read (by omega)) fun s4 u4 => ?_
  have w4 := w3.congr u4.wr
  have p4 : s4.gpr .r0 = base + BitVec.ofNat 32 acc := by
    rw [u4.gpr, u3.mem, u2.mem, u1.mem, ma]
  refine wp_ldr (a := off (State.addr base) acc) (by decide) (w4.ea p4 (by omega))
    (w4.read ha) fun s5 u5 => ?_
  refine wp_mul fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u7 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, u7.gpr, ?_, ?_⟩
  · rw [u7.other .r1 (by decide), u6.gpr, u5.other .r1 (by decide), u4.other .r1 (by decide),
      u3.gpr, u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, mi]
  · rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.other .r0 (by decide), p4]
  · rw [u7.other .r12 (by decide), u6.other .r12 (by decide), u5.other .r12 (by decide),
      u4.other .r12 (by decide), u3.other .r12 (by decide), u2.gpr, u1.mem, mm]
  · rw [u7.other .lr (by decide), u6.other .lr (by decide), u5.other .lr (by decide),
      u4.other .lr (by decide), u3.other .lr (by decide), u2.other .lr (by decide), u1.gpr, mn]
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (k3.mono (by simp_all)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
      ((u6.rest (by simp)).trans (u7.rest (by simp)))))

end VG.Proof.Bignum.Arm
