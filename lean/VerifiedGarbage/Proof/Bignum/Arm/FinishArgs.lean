module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFinish
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Recover final subtraction arguments before overwriting the temporary -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm op2_reg)

theorem finishArgs_ok (s : State) {base : BitVec 32} {size tmp out acc mod n : Nat}
    (ws : Workspace s base size) (ht : tmp + 32 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (mn : s.mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n)
    (mo : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out)
    (ma : s.mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc)
    (mm : s.mem.readW (off (State.addr base) (tmp + 8)) 32 = base + BitVec.ofNat 32 mod) :
    WP isa (.block finishArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧ t.gpr .r9 = base + BitVec.ofNat 32 out ∧
      t.gpr .r10 = base + BitVec.ofNat 32 acc ∧ t.gpr .r12 = base + BitVec.ofNat 32 mod ∧
      t.gpr .r7 = BitVec.ofNat 32 n ∧ t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Rest [.r7, .r9, .r10, .r11, .r12, .lr] s t := by
  unfold finishArgs
  refine wp_ldr (a := off (State.addr base) tmp) (by decide)
    (ws.ea ptr (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans ptr
  have w1 := ws.congr u1.wr
  refine wp_ldr (by decide) (w1.ea p1 (by omega)) (w1.read (by omega)) fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  have w2 := w1.congr u2.wr
  refine wp_ldr (by decide) (w2.ea p2 (by omega)) (w2.read (by omega)) fun s3 u3 => ?_
  have p3 := (u3.other .r0 (by decide)).trans p2
  have w3 := w2.congr u3.wr
  refine wp_ldr (by decide) (w3.ea p3 (by omega)) (w3.read (by omega)) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, u6.gpr, ?_, ?_⟩
  · exact (u6.other .r0 (by decide)).trans ((u5.other .r0 (by decide)).trans
      ((u4.other .r0 (by decide)).trans p3))
  · rw [u6.other .r9 (by decide), u5.other .r9 (by decide), u4.other .r9 (by decide),
      u3.other .r9 (by decide), u2.gpr, u1.mem, mo]
  · rw [u6.other .r10 (by decide), u5.other .r10 (by decide), u4.other .r10 (by decide),
      u3.gpr, u2.mem, u1.mem, ma]
  · rw [u6.other .r12 (by decide), u5.other .r12 (by decide), u4.gpr, u3.mem, u2.mem, u1.mem, mm]
  · rw [u6.other .r7 (by decide), u5.other .r7 (by decide), u4.other .r7 (by decide),
      u3.other .r7 (by decide), u2.other .r7 (by decide), u1.gpr, mn]
  · rw [u6.other .lr (by decide), u5.gpr, u4.other .r7 (by decide),
      u3.other .r7 (by decide), u2.other .r7 (by decide), u1.gpr, mn]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))

end VG.Proof.Bignum.Arm
