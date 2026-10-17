module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Recover Montgomery's fixed pointers and double the RSA word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_reg dpVal)

theorem basesTail_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc w : Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 92 ≤ size) (ptr : s.gpr .r0 = base)
    (pa : s.gpr .r8 = base + BitVec.ofNat 32 a) (pb : s.gpr .r9 = base + BitVec.ofNat 32 b)
    (po : s.gpr .r10 = base + BitVec.ofNat 32 out)
    (mt : s.mem.readW (off (State.addr base) 88) 32 = base + BitVec.ofNat 32 tmp)
    (mc : s.mem.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 acc)
    (mw : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (mm : s.mem.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod)
    (mi : s.mem.readW (off (State.addr base) 56) 32 = inv) :
    WP isa (.block MontFn.basesTail) s fun t =>
      InitRegs t base out tmp a b mod acc (2 * w) inv ∧ t.mem = s.mem ∧
      Rest [.r5, .r6, .r7, .r11, .r12] s t := by
  have p0 : s.gpr .r0 = base + BitVec.ofNat 32 0 := by simpa using ptr
  unfold MontFn.basesTail
  refine wp_ldr (by decide) (ws.ea p0 (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  have w1 := ws.congr u1.wr
  refine wp_ldr (by decide) (w1.ea p1 (by omega)) (w1.read (by omega)) fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  have w2 := w1.congr u2.wr
  refine wp_ldr (by decide) (w2.ea p2 (by omega)) (w2.read (by omega)) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have p4 := (u4.other .r0 (by decide)).trans ((u3.other .r0 (by decide)).trans p2)
  have w4 := (w2.congr u3.wr).congr u4.wr
  refine wp_ldr (by decide) (w4.ea p4 (by omega)) (w4.read (by omega)) fun s5 u5 => ?_
  have p5 := (u5.other .r0 (by decide)).trans p4
  have w5 := w4.congr u5.wr
  refine wp_ldr (by decide) (w5.ea p5 (by omega)) (w5.read (by omega)) fun t u6 => WP.block_nil ?_
  have keep : Rest [.r5, .r6, .r7, .r11, .r12] s t :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))
  refine ⟨⟨?_, ?_, ?_, (keep.gpr .r8 (by simp)).trans pa, (keep.gpr .r9 (by simp)).trans pb,
    (keep.gpr .r10 (by simp)).trans po, ?_, ?_⟩, ?_, keep⟩
  · rw [u6.other .r5 (by decide), u5.other .r5 (by decide), u4.other .r5 (by decide),
      u3.other .r5 (by decide), u2.other .r5 (by decide), u1.gpr, mt]
  · rw [u6.other .r6 (by decide), u5.other .r6 (by decide), u4.other .r6 (by decide),
      u3.other .r6 (by decide), u2.gpr, u1.mem, mc]
  · rw [u6.other .r7 (by decide), u5.other .r7 (by decide), u4.gpr, dpVal, u3.gpr, u2.mem, u1.mem, mw]
    rw [← BitVec.ofNat_add, show w + w = 2 * w by omega]
  · rw [u6.other .r11 (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, mm]
  · rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mi]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.Bignum.Arm
