module

public import VerifiedGarbage.Proof.Mont.Arm.PackedProduct
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! A packed multiply-add at fixed workspace offsets. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov op2_reg)

abbrev stepClob : List Reg := [.r3, .r5, .r6, .r7, .r8]

 theorem step_ok {s : State} {base : Addr} {size acc src K d j : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src)
    (ha : acc + 4 * j + 4 ≤ size) (hb : src + 4 * j + 4 ≤ size)
    (x : BitVec 32) (lo : (s.gpr .r2).toNat = x.toNat % 65536)
    (hi : (s.gpr .r0).toNat = x.toNat / 65536) :
    WP isa (.block (step acc rb d j)) s fun t =>
      t.mem = s.mem.writeW (off base (acc + 4 * j)) (t.gpr .r5) ∧
      (t.gpr .r5).toNat + (t.gpr .r3).toNat * 2 ^ 32 =
        w32 s.mem base (acc + 4 * j) + x.toNat * w32 s.mem base (src + 4 * j) + (s.gpr .r3).toNat ∧
      Rest stepClob s t := by
  have hn := hs.nowrap
  simp only [step, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldr (hs.off_lt (by omega))
    (by rw [hs.ea_off hp (by omega)]; congr 1; omega) (hs.read hb) fun s1 u1 => ?_
  have hs1 := hs.of_rest (u1.rest (ws := stepClob) (by simp)) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (product_ok s1 x
    (by rw [u1.other _ (by decide)]; exact lo) (by rw [u1.other _ (by decide)]; exact hi))
    fun s2 ⟨prod, k2, m2⟩ => ?_
  have k12 : Rest [.r5, .r6, .r7, .r8] s s2 := (u1.rest (by simp)).trans (k2.mono (by simp))
  have hs2 := hs.of_rest k12 (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs2.ea (by omega)) (hs2.read ha) fun s3 u3 => ?_
  have m3 : s3.mem = s.mem := by rw [u3.mem, m2, u1.mem]
  have prod3 : (s3.gpr .r5).toNat + (s3.gpr .r6).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem base (src + 4 * j) := by
    rw [u3.other _ (by decide), u3.other _ (by decide), prod, u1.gpr]
  have acc3 : (s3.gpr .r7).toNat = w32 s.mem base (acc + 4 * j) := by rw [u3.gpr, m2, u1.mem]
  have carry3 : s3.gpr .r3 = s.gpr .r3 := (u3.other _ (by decide)).trans (k12.gpr _ (by decide))
  have bound := mac_bound x (s.mem.readW (off base (src + 4 * j)) 32)
    (s.mem.readW (off base (acc + 4 * j)) 32) (s.gpr .r3)
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s3 .r7 (by rw [prod3, acc3]; dsimp only [w32] at *; omega))
    fun s4 ⟨v4, f4⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s4 .r3 (by
    rw [v4, prod3, acc3, f4.regs .r3 (by simp), carry3]
    exact bound)) fun s5 ⟨v5, f5⟩ => ?_
  have k35 : Rest stepClob s3 s5 := (frame_rest f4).mono (by simp) |>.trans ((frame_rest f5).mono (by simp))
  have k5 : Rest stepClob s s5 := (k12.mono (by simp)).trans ((u3.rest (by simp)).trans k35)
  have hs5 := hs.of_rest k5 (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs5.ea (by omega)) (hs5.write ha) fun s6 u6 => ?_
  refine wp_mov (op2_reg _ _) fun t u7 => WP.block_nil ?_
  have k : Rest stepClob s t := k5.trans ((u6.rest _).trans (u7.rest (by simp)))
  refine ⟨?_, ?_, k⟩
  · rw [u7.mem, u6.mem, f5.mem, f4.mem, m3, u7.other .r5 (by decide), u6.gpr]
  · rw [u7.other .r5 (by decide), u6.gpr, u7.gpr, u6.gpr, v5,
      v4, prod3, acc3, f4.regs .r3 (by simp), carry3]
    omega

end VG.Proof.Mont.Arm.Packed
