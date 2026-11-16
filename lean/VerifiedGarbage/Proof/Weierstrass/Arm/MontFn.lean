module

public import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
public import VerifiedGarbage.Proof.Mont.Arm.Ops
public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.PackedProduct
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
public import VerifiedGarbage.TCB.Arm.Target

/-! ### `Mont.Arm.PackedOps`, which only this module used -/

section

/-! ### `Mont.Arm.PackedLoop`, which only this module used -/

section

/-! ### `Mont.Arm.PackedRound`, which only this module used -/

section

/-! ### `Mont.Arm.PackedShift`, which only this module used -/

section

/-! Fixed-offset quotient shift, with overlapping source and destination. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov op2_imm)

def shiftWords (acc k : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .r5 .r12 (acc + 4 * j + 4), .str .r5 .r12 (acc + 4 * j)]

 theorem shiftWords_ok {s : State} {base : Addr} {size acc : Nat} (hs : Scr s base size) :
    ∀ k, acc + 4 * (k + 1) ≤ size →
    WP isa (.block (shiftWords acc k)) s fun t =>
      Outside base acc (4 * k) s.mem t.mem ∧
      val32 t.mem base acc k = val32 s.mem base (acc + 4) k ∧ Rest [.r5] s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, rfl, Rest.refl _ _⟩
  | k + 1, fit => by
    have hn := hs.nowrap
    obtain eq : shiftWords acc (k + 1) = shiftWords acc k ++
        [.ldr .r5 .r12 (acc + 4 * k + 4), .str .r5 .r12 (acc + 4 * k)] := by
      simp only [shiftWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (shiftWords_ok hs k (by omega_using [fit])) fun u ⟨out, val, rest⟩ => ?_
    obtain hu := hs.of_rest rest (by decide)
    refine wp_ldr (hu.off_lt (by omega_using [fit])) (hu.ea (by omega_using [fit])) (hu.read (by omega_using [fit])) fun v uv => ?_
    obtain hv := hu.of_rest (uv.rest (ws := [.r5]) (by simp)) (by decide)
    refine wp_str (hv.off_lt (by omega_using [fit])) (hv.ea (by omega_using [fit])) (hv.write (by omega_using [fit])) fun t vt => WP.block_nil ?_
    obtain mem : t.mem = u.mem.writeW (off base (acc + 4 * k)) (u.mem.readW (off base (acc + 4 * k + 4)) 32) := by
      rw [vt.mem, uv.mem, uv.gpr]
    obtain wr := writeW32_outside u.mem base (d := acc + 4 * k)
      (u.mem.readW (off base (acc + 4 * k + 4)) 32) (by omega_using [fit, hn])
    rw [← mem] at wr
    obtain low := wr.val32 (d := acc) (k := k) (by omega_using []) (by omega_using [fit, hn])
    obtain source := out.w32 (d := acc + 4 * k + 4) (by omega_using []) (by omega_using [fit, hn])
    obtain top : w32 t.mem base (acc + 4 * k) = w32 u.mem base (acc + 4 * k + 4) := by
      rw [mem, w32_write_self]
    refine ⟨(out.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using [])), ?_,
      rest.trans ((uv.rest (by simp)).trans (vt.rest _))⟩
    rw [val32_succ, val32_succ, low, top, source, val]
    rw [show acc + 4 * k + 4 = acc + 4 + 4 * k by omega_using []]

 theorem shift_ok {s : State} {base : Addr} {size acc n : Nat}
    (hs : Scr s base size) (fit : acc + 4 * (n + 2) ≤ size) :
    WP isa (.block (shift acc n)) s fun t =>
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧
      val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) / 2 ^ 32 ∧ Rest [.r5] s t := by
  change WP isa (.block (shiftWords acc (n + 1) ++ _)) s _
  refine VG.Proof.X25519.Arm.WP.append (shiftWords_ok hs (n + 1) fit) fun u ⟨out, val, rest⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun v uv => ?_
  obtain k : Rest [.r5] s v := rest.trans (uv.rest (by simp))
  obtain hv := hs.of_rest k (by decide)
  refine wp_str (hv.off_lt (by omega_using [fit])) (hv.ea (by omega_using [fit])) (hv.write (by omega_using [fit])) fun t vt => WP.block_nil ?_
  obtain mem : t.mem = u.mem.writeW (off base (acc + 4 * (n + 1))) (0 : BitVec 32) := by rw [vt.mem, uv.mem, uv.gpr]
  have hn := hs.nowrap
  obtain wr := writeW32_outside u.mem base (d := acc + 4 * (n + 1)) 0 (by omega_using [fit, hn])
  rw [← mem] at wr
  obtain low := wr.val32 (d := acc) (k := n + 1) (by omega_using []) (by omega_using [fit, hn])
  obtain top : w32 t.mem base (acc + 4 * (n + 1)) = 0 := by rw [mem, w32_write_self]; rfl
  refine ⟨(out.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using [])), ?_,
    k.trans (vt.rest _)⟩
  rw [show n + 2 = (n + 1) + 1 by omega_using [], val32_succ, top, Nat.mul_zero, Nat.add_zero, low, val]
  rw [val32]
  obtain h := (s.mem.readW (off base acc) 32).isLt
  change val32 s.mem base (acc + 4) (n + 1) =
    (w32 s.mem base acc + 2 ^ 32 * val32 s.mem base (acc + 4) (n + 1)) / 2 ^ 32
  dsimp only [w32] at *
  omega_using []

end VG.Proof.Mont.Arm.Packed

end

end

/-! ### `Mont.Arm.PackedRow`, which only this module used -/

section

/-! ### `Mont.Arm.PackedStep`, which only this module used -/

section

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
  refine wp_ldr (hs.off_lt (by omega_using [hd, hb]))
    (by rw [hs.ea_off hp (by omega_using [hd, hb])]; congr 1; omega_using [hd]) (hs.read hb) fun s1 u1 => ?_
  obtain hs1 := hs.of_rest (u1.rest (ws := stepClob) (by simp)) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (product_ok s1 x
    (by rw [u1.other _ (by decide)]; exact lo) (by rw [u1.other _ (by decide)]; exact hi))
    fun s2 ⟨prod, k2, m2⟩ => ?_
  obtain k12 : Rest [.r5, .r6, .r7, .r8] s s2 := (u1.rest (by simp)).trans (k2.mono (by simp))
  obtain hs2 := hs.of_rest k12 (by decide)
  refine wp_ldr (hs.off_lt (by omega_using [ha])) (hs2.ea (by omega_using [ha])) (hs2.read ha) fun s3 u3 => ?_
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, m2, u1.mem]
  obtain prod3 : (s3.gpr .r5).toNat + (s3.gpr .r6).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem base (src + 4 * j) := by
    rw [u3.other _ (by decide), u3.other _ (by decide), prod, u1.gpr]
  obtain acc3 : (s3.gpr .r7).toNat = w32 s.mem base (acc + 4 * j) := by rw [u3.gpr, m2, u1.mem]
  obtain carry3 : s3.gpr .r3 = s.gpr .r3 := (u3.other _ (by decide)).trans (k12.gpr _ (by decide))
  obtain bound := mac_bound x (s.mem.readW (off base (src + 4 * j)) 32)
    (s.mem.readW (off base (acc + 4 * j)) 32) (s.gpr .r3)
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s3 .r7 (by rw [prod3, acc3]; dsimp only [w32] at *; omega_using [bound]))
    fun s4 ⟨v4, f4⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s4 .r3 (by
    rw [v4, prod3, acc3, f4.regs .r3 (by simp), carry3]
    exact bound)) fun s5 ⟨v5, f5⟩ => ?_
  obtain k35 : Rest stepClob s3 s5 := (frame_rest f4).mono (by simp) |>.trans ((frame_rest f5).mono (by simp))
  obtain k5 : Rest stepClob s s5 := (k12.mono (by simp)).trans ((u3.rest (by simp)).trans k35)
  obtain hs5 := hs.of_rest k5 (by decide)
  refine wp_str (hs.off_lt (by omega_using [ha])) (hs5.ea (by omega_using [ha])) (hs5.write ha) fun s6 u6 => ?_
  refine wp_mov (op2_reg _ _) fun t u7 => WP.block_nil ?_
  obtain k : Rest stepClob s t := k5.trans ((u6.rest _).trans (u7.rest (by simp)))
  refine ⟨?_, ?_, k⟩
  · rw [u7.mem, u6.mem, f5.mem, f4.mem, m3, u7.other .r5 (by decide), u6.gpr]
  · rw [u7.other .r5 (by decide), u6.gpr, u7.gpr, u6.gpr, v5,
      v4, prod3, acc3, f4.regs .r3 (by simp), carry3]
    omega_using []

/-- `step_ok` for the step with `umaal`, whose scalar is r2. -/
theorem stepU_ok {s : State} {base : Addr} {size acc src K d j : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src)
    (ha : acc + 4 * j + 4 ≤ size) (hb : src + 4 * j + 4 ≤ size) :
    WP isa (.block (stepU acc rb d j)) s fun t =>
      t.mem = s.mem.writeW (off base (acc + 4 * j)) (t.gpr .r5) ∧
      (t.gpr .r5).toNat + (t.gpr .r3).toNat * 2 ^ 32 =
        w32 s.mem base (acc + 4 * j) + (s.gpr .r2).toNat * w32 s.mem base (src + 4 * j) + (s.gpr .r3).toNat ∧
      Rest stepClob s t := by
  have hn := hs.nowrap
  simp only [stepU]
  refine wp_ldr (hs.off_lt (by omega_using [hd, hb]))
    (by rw [hs.ea_off hp (by omega_using [hd, hb])]; congr 1; omega_using [hd]) (hs.read hb) fun s1 u1 => ?_
  obtain hs1 := hs.of_rest (u1.rest (ws := stepClob) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega_using [ha])) (hs1.ea (by omega_using [ha])) (hs1.read ha) fun s2 u2 => ?_
  obtain y2 : (s2.gpr .r7).toNat = w32 s.mem base (src + 4 * j) := by rw [u2.other _ (by decide), u1.gpr]
  obtain a2 : (s2.gpr .r5).toNat = w32 s.mem base (acc + 4 * j) := by rw [u2.gpr, u1.mem]
  obtain x2 : s2.gpr .r2 = s.gpr .r2 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain c2 : s2.gpr .r3 = s.gpr .r3 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  rw [show ([.umaal .r5 .r3 .r2 .r7, .str .r5 .r12 (acc + 4 * j)] : List Instr) =
    [.umaal .r5 .r3 .r2 .r7] ++ [.str .r5 .r12 (acc + 4 * j)] from rfl]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Bignum.Arm.Fios.umaal_ok s2 .r5 .r3 .r2 .r7 (by decide))
    fun s3 ⟨v3, f3⟩ => ?_
  obtain k3 : Rest stepClob s s3 :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((frame_rest f3).mono (by simp)))
  obtain hs3 := hs.of_rest k3 (by decide)
  refine wp_str (hs.off_lt (by omega_using [ha])) (hs3.ea (by omega_using [ha])) (hs3.write ha) fun t u4 => WP.block_nil ?_
  have g : t.gpr = s3.gpr := u4.gpr
  refine ⟨?_, ?_, k3.trans (u4.rest _)⟩
  · rw [u4.mem, g, f3.mem, u2.mem, u1.mem]
  · rw [g, Nat.mul_comm _ (2 ^ 32), v3, y2, a2, x2, c2]
    omega_using []

end VG.Proof.Mont.Arm.Packed

end

end


/-! A full packed-word row with no pointer spills. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm wp_ldr wp_str op2_lsl op2_lsr)

def steps (acc : Nat) (rb : Reg) (d k : Nat) : List Instr :=
  (List.range k).flatMap (step acc rb d)

 theorem steps_ok {s : State} {base : Addr} {size acc src K d n : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src) (hrb : rb ∉ stepClob)
    (ha : acc + 4 * n ≤ size) (hb : src + 4 * n ≤ size)
    (sep : acc + 4 * n ≤ src ∨ src + 4 * n ≤ acc)
    (x : BitVec 32) (lo : (s.gpr .r2).toNat = x.toNat % 65536)
    (hi : (s.gpr .r0).toNat = x.toNat / 65536) :
    ∀ k, k ≤ n → WP isa (.block (steps acc rb d k)) s fun t =>
      Outside base acc (4 * k) s.mem t.mem ∧
      val32 t.mem base acc k + 2 ^ (32 * k) * (t.gpr .r3).toNat =
        val32 s.mem base acc k + x.toNat * val32 s.mem base src k + (s.gpr .r3).toNat ∧
      Rest stepClob s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32], Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    obtain eq : steps acc rb d (k + 1) = steps acc rb d k ++ step acc rb d k := by
      simp only [steps, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (steps_ok hs hp hd hrb ha hb sep x lo hi k (by omega_arith))
      fun u ⟨out, val, rest⟩ => ?_
    obtain hu := hs.of_rest rest (by decide)
    obtain pu : u.gpr rb = u.gpr .r12 + BitVec.ofNat 32 K := by
      rw [rest.gpr _ hrb, rest.gpr _ (by decide)]; exact hp
    refine WP.mono (step_ok hu pu hd (by omega_arith) (by omega_arith) x
      (by rw [rest.gpr _ (by decide)]; exact lo)
      (by rw [rest.gpr _ (by decide)]; exact hi)) fun t ⟨mem, value, keep⟩ => ?_
    obtain oldA := out.w32 (d := acc + 4 * k) (by omega_arith) (by omega_arith)
    obtain oldB := out.w32 (d := src + 4 * k) (by omega_arith) (by omega_arith)
    rw [oldA, oldB] at value
    obtain wr := writeW32_outside u.mem base (d := acc + 4 * k) (t.gpr .r5) (by omega_arith)
    rw [← mem] at wr
    obtain low := wr.val32 (d := acc) (k := k) (by omega_arith) (by omega_arith)
    obtain top : w32 t.mem base (acc + 4 * k) = (t.gpr .r5).toNat := by rw [mem, w32_write_self]
    refine ⟨(out.mono (Nat.le_refl _) (by omega_arith)).trans (wr.mono (by omega_arith) (by omega_arith)), ?_, rest.trans keep⟩
    rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
    generalize 2 ^ (32 * k) = P at *
    grind

 theorem carry_ok {s : State} {base : Addr} {size acc n : Nat}
    (hs : Scr s base size) (ha : acc + 4 * (n + 2) ≤ size)
    (fit : val32 s.mem base (acc + 4 * n) 2 + (s.gpr .r3).toNat < 2 ^ 64) :
    WP isa (.block (carry acc n)) s fun t =>
      Outside base (acc + 4 * n) 8 s.mem t.mem ∧
      val32 t.mem base acc (n + 2) = val32 s.mem base acc n +
        2 ^ (32 * n) * (val32 s.mem base (acc + 4 * n) 2 + (s.gpr .r3).toNat) ∧
      Rest [.r5, .r6] s t := by
  have hn := hs.nowrap
  simp only [carry, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea (by omega_arith)) (hs.read (by omega_arith)) fun s1 u1 => ?_
  obtain hs1 := hs.of_rest (u1.rest (ws := [.r5, .r6]) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs1.ea (by omega_arith)) (hs1.read (by omega_arith)) fun s2 u2 => ?_
  obtain a5 : s2.gpr .r5 = s.mem.readW (off base (acc + 4 * n)) 32 := by rw [u2.other _ (by decide), u1.gpr]
  obtain a6 : s2.gpr .r6 = s.mem.readW (off base (acc + 4 * n + 4)) 32 := by rw [u2.gpr, u1.mem]
  obtain a3 : s2.gpr .r3 = s.gpr .r3 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain k2 : Rest [.r5, .r6] s s2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s2 .r3 (by
    rw [a5, a6, a3]; simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using fit))
    fun s3 ⟨value, frame⟩ => ?_
  obtain k3 := k2.trans (frame_rest frame)
  obtain hs3 := hs.of_rest k3 (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs3.ea (by omega_arith)) (hs3.write (by omega_arith)) fun s4 u4 => ?_
  obtain hs4 := hs3.of_rest (u4.rest []) (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs4.ea (by omega_arith)) (hs4.write (by omega_arith)) fun t u5 => WP.block_nil ?_
  obtain mem : t.mem = (s.mem.writeW (off base (acc + 4 * n)) (s3.gpr .r5)).writeW
      (off base (acc + 4 * n + 4)) (s3.gpr .r6) := by
    rw [u5.mem, u4.mem, u4.gpr, frame.mem, u2.mem, u1.mem]
  obtain w1 := writeW32_outside s.mem base (d := acc + 4 * n) (s3.gpr .r5) (by omega_arith)
  obtain w2 := writeW32_outside (s.mem.writeW (off base (acc + 4 * n)) (s3.gpr .r5)) base
    (d := acc + 4 * n + 4) (s3.gpr .r6) (by omega_arith)
  rw [← mem] at w2
  obtain outside : Outside base (acc + 4 * n) 8 s.mem t.mem :=
    (w1.mono (by omega_arith) (by omega_arith)).trans (w2.mono (by omega_arith) (by omega_arith))
  obtain low := outside.val32 (d := acc) (k := n) (by omega_arith) (by omega_arith)
  obtain top0 : w32 t.mem base (acc + 4 * n) = (s3.gpr .r5).toNat := by
    rw [mem, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self]
  obtain top1 : w32 t.mem base (acc + 4 * n + 4) = (s3.gpr .r6).toNat := by rw [mem, w32_write_self]
  obtain vtop : (s3.gpr .r5).toNat + 2 ^ 32 * (s3.gpr .r6).toNat =
      val32 s.mem base (acc + 4 * n) 2 + (s.gpr .r3).toNat := by
    rw [Nat.mul_comm (2 ^ 32), value, a5, a6, a3]
    simp only [val32, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32]
  refine ⟨outside, ?_, k3.trans ((u4.rest _).trans (u5.rest _))⟩
  rw [val32_append t.mem base acc n 2, low, val32, val32, val32, top0, top1,
    Nat.mul_zero, Nat.add_zero, vtop]


abbrev rowClob : List Reg := [.r0, .r2, .r3, .r5, .r6, .r7, .r8]

 theorem row_ok {s : State} {base : Addr} {size acc src K d n : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src) (hrb : rb ∉ rowClob)
    (ha : acc + 4 * (n + 2) ≤ size) (hb : src + 4 * n ≤ size)
    (sep : acc + 4 * (n + 2) ≤ src ∨ src + 4 * n ≤ acc)
    (fit : val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n < 2 ^ (32 * (n + 2))) :
    WP isa (.block (row acc rb d n)) s fun t =>
      val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
        (s.gpr .r2).toNat * val32 s.mem base src n ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest rowClob s t := by
  have hn := hs.nowrap
  simp only [row, split, List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain k4 : Rest rowClob s s4 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans (u4.rest (by simp))))
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  obtain p4 : s4.gpr rb = s4.gpr .r12 + BitVec.ofNat 32 K := by
    rw [k4.gpr _ hrb, k4.gpr _ (by decide)]; exact hp
  obtain lo : (s4.gpr .r2).toNat = (s.gpr .r2).toNat % 65536 := by
    rw [u4.other _ (by decide), u3.gpr, u2.gpr, u1.other _ (by decide), low_half]
  obtain hi : (s4.gpr .r0).toNat = (s.gpr .r2).toNat / 65536 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, VG.Proof.X25519.Arm.toNat_shr]
  change WP isa (.block (steps acc rb d n ++ carry acc n)) s4 _
  refine VG.Proof.X25519.Arm.WP.append (steps_ok (hs.of_rest k4 (by decide)) p4 hd
    (fun h => hrb ((by decide : ∀ r ∈ stepClob, r ∈ rowClob) rb h)) (by omega_arith) hb (by omega_arith)
    (s.gpr .r2) lo hi n (Nat.le_refl _)) fun u ⟨outside, value, rest⟩ => ?_
  obtain tops := outside.val32 (d := acc + 4 * n) (k := 2) (by omega_arith) (by omega_arith)
  rw [u4.gpr, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, m4] at value
  obtain total : val32 u.mem base acc n + 2 ^ (32 * n) *
      (val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat) =
      val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n := by
    rw [tops, m4, val32_append s.mem base acc n 2]
    generalize 2 ^ (32 * n) = P at *
    grind
  obtain topfit : val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat < 2 ^ 64 := by
    rw [← total, VG.Proof.Bignum.Arm.pow32_addtwo] at fit
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) fit)
  obtain k : Rest rowClob s u := k4.trans (rest.mono (by simp))
  refine WP.mono (carry_ok (hs.of_rest k (by decide)) ha topfit) fun t ⟨out, val, keep⟩ => ?_
  refine ⟨by rw [val]; exact total, ?_, k.trans (keep.mono (by simp))⟩
  rw [m4] at outside
  exact (outside.mono (Nat.le_refl _) (by omega_arith)).trans (out.mono (by omega_arith) (by omega_arith))

def stepsU (acc : Nat) (rb : Reg) (d k : Nat) : List Instr :=
  (List.range k).flatMap (stepU acc rb d)

/-- `steps_ok` for the steps with `umaal`, whose scalar is r2. -/
theorem stepsU_ok {s : State} {base : Addr} {size acc src K d n : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src) (hrb : rb ∉ stepClob)
    (ha : acc + 4 * n ≤ size) (hb : src + 4 * n ≤ size)
    (sep : acc + 4 * n ≤ src ∨ src + 4 * n ≤ acc) :
    ∀ k, k ≤ n → WP isa (.block (stepsU acc rb d k)) s fun t =>
      Outside base acc (4 * k) s.mem t.mem ∧
      val32 t.mem base acc k + 2 ^ (32 * k) * (t.gpr .r3).toNat =
        val32 s.mem base acc k + (s.gpr .r2).toNat * val32 s.mem base src k + (s.gpr .r3).toNat ∧
      Rest stepClob s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32], Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    obtain eq : stepsU acc rb d (k + 1) = stepsU acc rb d k ++ stepU acc rb d k := by
      simp only [stepsU, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (stepsU_ok hs hp hd hrb ha hb sep k (by omega_arith))
      fun u ⟨out, val, rest⟩ => ?_
    obtain hu := hs.of_rest rest (by decide)
    obtain pu : u.gpr rb = u.gpr .r12 + BitVec.ofNat 32 K := by
      rw [rest.gpr _ hrb, rest.gpr _ (by decide)]; exact hp
    obtain x2 : u.gpr .r2 = s.gpr .r2 := rest.gpr _ (by decide)
    refine WP.mono (stepU_ok hu pu hd (by omega_arith) (by omega_arith)) fun t ⟨mem, value, keep⟩ => ?_
    obtain oldA := out.w32 (d := acc + 4 * k) (by omega_arith) (by omega_arith)
    obtain oldB := out.w32 (d := src + 4 * k) (by omega_arith) (by omega_arith)
    rw [oldA, oldB, x2] at value
    obtain wr := writeW32_outside u.mem base (d := acc + 4 * k) (t.gpr .r5) (by omega_arith)
    rw [← mem] at wr
    obtain low := wr.val32 (d := acc) (k := k) (by omega_arith) (by omega_arith)
    obtain top : w32 t.mem base (acc + 4 * k) = (t.gpr .r5).toNat := by rw [mem, w32_write_self]
    refine ⟨(out.mono (Nat.le_refl _) (by omega_arith)).trans (wr.mono (by omega_arith) (by omega_arith)), ?_, rest.trans keep⟩
    rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
    generalize 2 ^ (32 * k) = P at *
    grind

/-- `row_ok` for the row with `umaal`. -/
theorem rowU_ok {s : State} {base : Addr} {size acc src K d n : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src) (hrb : rb ∉ rowClob)
    (ha : acc + 4 * (n + 2) ≤ size) (hb : src + 4 * n ≤ size)
    (sep : acc + 4 * (n + 2) ≤ src ∨ src + 4 * n ≤ acc)
    (fit : val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n < 2 ^ (32 * (n + 2))) :
    WP isa (.block (rowU acc rb d n)) s fun t =>
      val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
        (s.gpr .r2).toNat * val32 s.mem base src n ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest rowClob s t := by
  have hn := hs.nowrap
  simp only [rowU, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain k4 : Rest rowClob s s4 := u4.rest (by simp)
  have m4 : s4.mem = s.mem := u4.mem
  obtain p4 : s4.gpr rb = s4.gpr .r12 + BitVec.ofNat 32 K := by
    rw [k4.gpr _ hrb, k4.gpr _ (by decide)]; exact hp
  obtain x4 : s4.gpr .r2 = s.gpr .r2 := u4.other _ (by decide)
  change WP isa (.block (stepsU acc rb d n ++ carry acc n)) s4 _
  refine VG.Proof.X25519.Arm.WP.append (stepsU_ok (hs.of_rest k4 (by decide)) p4 hd
    (fun h => hrb ((by decide : ∀ r ∈ stepClob, r ∈ rowClob) rb h)) (by omega_arith) hb (by omega_arith)
    n (Nat.le_refl _)) fun u ⟨outside, value, rest⟩ => ?_
  obtain tops := outside.val32 (d := acc + 4 * n) (k := 2) (by omega_arith) (by omega_arith)
  rw [u4.gpr, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, m4, x4] at value
  obtain total : val32 u.mem base acc n + 2 ^ (32 * n) *
      (val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat) =
      val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n := by
    rw [tops, m4, val32_append s.mem base acc n 2]
    generalize 2 ^ (32 * n) = P at *
    grind
  obtain topfit : val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat < 2 ^ 64 := by
    rw [← total, VG.Proof.Bignum.Arm.pow32_addtwo] at fit
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) fit)
  obtain k : Rest rowClob s u := k4.trans (rest.mono (by simp))
  refine WP.mono (carry_ok (hs.of_rest k (by decide)) ha topfit) fun t ⟨out, val, keep⟩ => ?_
  refine ⟨by rw [val]; exact total, ?_, k.trans (keep.mono (by simp))⟩
  rw [m4] at outside
  exact (outside.mono (Nat.le_refl _) (by omega_arith)).trans (out.mono (by omega_arith) (by omega_arith))

/-- `row_ok` for the row of either kind. -/
theorem rowWith_ok (u : Bool) {s : State} {base : Addr} {size acc src K d n : Nat} {rb : Reg}
    (hs : Scr s base size) (hp : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K)
    (hd : K + d = src) (hrb : rb ∉ rowClob)
    (ha : acc + 4 * (n + 2) ≤ size) (hb : src + 4 * n ≤ size)
    (sep : acc + 4 * (n + 2) ≤ src ∨ src + 4 * n ≤ acc)
    (fit : val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n < 2 ^ (32 * (n + 2))) :
    WP isa (.block (rowWith u acc rb d n)) s fun t =>
      val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
        (s.gpr .r2).toNat * val32 s.mem base src n ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest rowClob s t := by
  cases u
  · exact row_ok hs hp hd hrb ha hb sep fit
  · exact rowU_ok hs hp hd hrb ha hb sep fit

end VG.Proof.Mont.Arm.Packed

end

end


/-! One packed Montgomery round in the curve workspace. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont
open VG.Impl.Mont.Arm.Packed VG.Proof.Bignum.Arm
open VG.Proof.Weierstrass.Arm (wp_movt movImm_val)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_movw wp_mul wp_dp wp_subs op2_reg op2_imm dpVal)

abbrev roundClob : List Reg := [.r0, .r1, .r2, .r3, .r5, .r6, .r7, .r8, .r9]

 theorem round_ok (u : Bool) {s : State} {base : Addr} {size acc a b i n m : Nat} {M : Mod}
    (hs : Scr s base size) (hMn : 2 * M.n = n)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * i))
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (fa : a + 4 * (i + 1) ≤ size) (fb : b + 4 * n ≤ size)
    (fm : M.mo + 4 * n ≤ size) (ft : acc + 4 * (n + 2) ≤ size)
    (sb : acc + 4 * (n + 2) ≤ b ∨ b + 4 * n ≤ acc)
    (sm : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc)
    (modulus : val32 s.mem base M.mo n = m)
    (inverse : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (operand : val32 s.mem base b n < m) (bound : val32 s.mem base acc (n + 2) < 2 * m)
    :
    WP isa (.block (round M acc u)) s fun t =>
      (∃ q < 2 ^ 32, 2 ^ 32 * val32 t.mem base acc (n + 2) =
        val32 s.mem base acc (n + 2) + w32 s.mem base (a + 4 * i) * val32 s.mem base b n + q * m) ∧
      val32 t.mem base acc (n + 2) < 2 * m ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t ∧
      t.gpr .r1 = s.gpr .r1 + 4 ∧ t.gpr .r9 = s.gpr .r9 - 1 ∧ t.z = (s.gpr .r9 - 1 == 0) := by
  have hn := hs.nowrap
  obtain mlt : m < 2 ^ (32 * n) := by rw [← modulus]; exact val32_lt _ _ _ _
  simp only [round, hMn, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using hs.ea_off (d := 0) pa (by omega_using [fa]))
    (hs.read (d := a + 4 * i) (by omega_using [fa])) fun s1 u1 => ?_
  let x := s.mem.readW (off base (a + 4 * i)) 32
  have scalar : s1.gpr .r2 = x := u1.gpr
  obtain k1 : Rest rowClob s s1 := u1.rest (by simp)
  obtain h1 := hs.of_rest k1 (by decide)
  obtain pb1 : s1.gpr .r4 = s1.gpr .r12 + BitVec.ofNat 32 b := by rw [u1.other _ (by decide), u1.other _ (by decide)]; exact pb
  obtain fits1 : val32 s1.mem base acc (n + 2) + (s1.gpr .r2).toNat * val32 s1.mem base b n < 2 ^ (32 * (n + 2)) := by
    rw [u1.mem, scalar]
    obtain f := round_fit bound x.isLt operand (by decide : 0 < 2 ^ 32) mlt
    simpa only [Nat.zero_mul, Nat.add_zero] using f
  refine VG.Proof.X25519.Arm.WP.append (rowWith_ok u h1 pb1 (Nat.add_zero _) (by decide) ft fb sb fits1)
    fun s2 ⟨v2, o2, k2⟩ => ?_
  obtain k12 : Rest rowClob s s2 := k1.trans (k2.mono (by simp))
  obtain h2 := hs.of_rest k12 (by decide)
  obtain v2' : val32 s2.mem base acc (n + 2) = val32 s.mem base acc (n + 2) + x.toNat * val32 s.mem base b n := by
    rw [v2, u1.mem, scalar]
  obtain mo2 : val32 s2.mem base M.mo n = m := by rw [o2.val32 (by omega_using [sm]) (by omega_using [fm, hn]), u1.mem]; exact modulus
  refine wp_ldr (h2.off_lt (by omega_using [ft])) (h2.ea (by omega_using [ft])) (h2.read (by omega_using [ft])) fun s3 u3 => ?_
  refine wp_movw fun s4 u4 => wp_movt fun s5 u5 => wp_mul fun s6 u6 => ?_
  obtain k6 : Rest rowClob s s6 := k12.trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp)))))
  obtain h6 := hs.of_rest k6 (by decide)
  obtain mem6 : s6.mem = s2.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem]
  obtain inv7 : s5.gpr .r7 = BitVec.ofNat 32 M.minv.toNat := by rw [u5.gpr, u4.gpr, movImm_val]
  obtain coeff : (s6.gpr .r2).toNat = val32 s2.mem base acc (n + 2) * (BitVec.ofNat 32 M.minv.toNat).toNat % 2 ^ 32 := by
    rw [u6.gpr, inv7, u5.other _ (by decide), u4.other _ (by decide), u3.gpr, BitVec.mul_comm]
    exact coefficient_value _ _ _ _ (n + 1)
  obtain fits2 : val32 s6.mem base acc (n + 2) + (s6.gpr .r2).toNat * val32 s6.mem base M.mo n < 2 ^ (32 * (n + 2)) := by
    rw [mem6, mo2, v2']
    exact round_fit bound x.isLt operand (s6.gpr .r2).isLt mlt
  refine VG.Proof.X25519.Arm.WP.append (rowWith_ok u h6 (K := 0) (by simp) (Nat.zero_add _) (by decide) ft fm sm fits2)
    fun s7 ⟨v7, o7, k7⟩ => ?_
  obtain sum : val32 s7.mem base acc (n + 2) = val32 s2.mem base acc (n + 2) + (s6.gpr .r2).toNat * m := by
    rw [v7, mem6, mo2]
  obtain cancel : val32 s7.mem base acc (n + 2) % 2 ^ 32 = 0 :=
    round_cancel (inverse32 inverse) coeff sum
  obtain k : Rest rowClob s s7 := k6.trans (k7.mono (by simp))
  refine VG.Proof.X25519.Arm.WP.append (shift_ok (hs.of_rest k (by decide)) ft) fun s8 ⟨o8, v8, k8⟩ => ?_
  obtain k' : Rest rowClob s s8 := k.trans (k8.mono (by simp))
  refine wp_dp (op2_imm (by decide)) fun s9 u9 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u10 z10 => WP.block_nil ?_
  obtain mem : t.mem = s8.mem := by rw [u10.mem, u9.mem]
  obtain exactValue : 2 ^ 32 * val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
      x.toNat * val32 s.mem base b n + (s6.gpr .r2).toNat * m := by
    rw [mem, v8, round_div_exact cancel, sum, v2']
  refine ⟨⟨(s6.gpr .r2).toNat, (s6.gpr .r2).isLt, exactValue⟩,
    round_lt exactValue bound x.isLt operand (s6.gpr .r2).isLt, ?_,
    (k'.mono (by simp)).trans ((u9.rest (by simp)).trans (u10.rest (by simp))), ?_, ?_, ?_⟩
  · rw [mem, u1.mem] at *
    exact o2.trans (by rw [mem6] at o7; exact o7.trans o8)
  · rw [u10.other _ (by decide), u9.gpr, dpVal, k'.gpr .r1 (by decide)]
  · rw [u10.gpr, u9.other _ (by decide), k'.gpr .r9 (by decide)]
  · rw [z10, u9.other _ (by decide), k'.gpr .r9 (by decide)]

end VG.Proof.Mont.Arm.Packed

end

end


/-! Induction over packed Montgomery rounds. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Bignum.Arm (round_step)

structure LoopInv (s0 : State) (base : Addr) (acc a b n m i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r1 = s0.gpr .r12 + BitVec.ofNat 32 (a + 4 * i)
  count : s.gpr .r9 = BitVec.ofNat 32 (n - i)
  outside : Outside base acc (4 * (n + 2)) s0.mem s.mem
  bound : val32 s.mem base acc (n + 2) < 2 * m
  value : 2 ^ (32 * i) * val32 s.mem base acc (n + 2) % m =
    val32 s0.mem base a i * val32 s0.mem base b n % m
  rest : Rest roundClob s0 s

 theorem loop_ok (u : Bool) {s : State} {base : Addr} {size acc a b n m : Nat} {M : Mod}
    (hs : Scr s base size) (hMn : 2 * M.n = n) (hn : 0 < n) (hn32 : n < 2 ^ 32)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 a)
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (pc : s.gpr .r9 = BitVec.ofNat 32 n)
    (fa : a + 4 * n ≤ size) (fb : b + 4 * n ≤ size)
    (fm : M.mo + 4 * n ≤ size) (ft : acc + 4 * (n + 2) ≤ size)
    (sa : acc + 4 * (n + 2) ≤ a ∨ a + 4 * n ≤ acc)
    (sb : acc + 4 * (n + 2) ≤ b ∨ b + 4 * n ≤ acc)
    (sm : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc)
    (modulus : val32 s.mem base M.mo n = m)
    (inverse : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (operand : val32 s.mem base b n < m) (zero : val32 s.mem base acc (n + 2) = 0) :
    WP isa (.loop (.block (round M acc u)) .ne) s fun t =>
      val32 t.mem base acc (n + 2) < 2 * m ∧
      2 ^ (32 * n) * val32 t.mem base acc (n + 2) % m = val32 s.mem base a n * val32 s.mem base b n % m ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t := by
  have nowrap := hs.nowrap
  obtain mpos : 0 < m := by omega_using [operand]
  let I := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ LoopInv s base acc a b n m i t
  have step (k : Nat) (w : State) (h : I k w) :
      WP isa (.block (round M acc u)) w fun t =>
        (isa.eval .ne t = some false ∧ (val32 t.mem base acc (n + 2) < 2 * m ∧
          2 ^ (32 * n) * val32 t.mem base acc (n + 2) % m = val32 s.mem base a n * val32 s.mem base b n % m ∧
          Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t)) ∨
        (isa.eval .ne t = some true ∧ ∃ j < k, I j t) := by
    obtain ⟨i, hik, hk, inv⟩ := h
    obtain hi : i < n := by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, nowrap, hik, hk]
    obtain hu := hs.of_rest inv.rest (by decide)
    obtain pu : w.gpr .r1 = w.gpr .r12 + BitVec.ofNat 32 (a + 4 * i) := by
      rw [inv.ptr, inv.rest.gpr .r12 (by decide)]
    obtain bu : w.gpr .r4 = w.gpr .r12 + BitVec.ofNat 32 b := by
      rw [inv.rest.gpr .r4 (by decide), inv.rest.gpr .r12 (by decide)]; exact pb
    obtain oldM := inv.outside.val32 (d := M.mo) (k := n) (by omega_using [sm]) (by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, nowrap, hik, hk, hi])
    obtain oldB := inv.outside.val32 (d := b) (k := n) (by omega_using [sb]) (by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, nowrap, hik, hk, hi])
    obtain oldA := inv.outside.w32 (d := a + 4 * i) (by omega_using [sa, hi]) (by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, nowrap, hik, hk, hi])
    refine WP.mono (round_ok u hu hMn pu bu (by omega_using [fa, hi]) fb fm ft sb sm
      (oldM.trans modulus) inverse (by rw [oldB]; exact operand) inv.bound) fun t post => ?_
    obtain ⟨⟨q, hq, value⟩, bound, out, rest, ptr, count, zeroFlag⟩ := post
    rw [oldA, oldB] at value
    obtain vnext : 2 ^ (32 * (i + 1)) * val32 t.mem base acc (n + 2) % m =
        val32 s.mem base a (i + 1) * val32 s.mem base b n % m := by
      rw [pow32_succ, Nat.mul_comm (2 ^ 32) (2 ^ (32 * i)), val32_succ s.mem base a i]
      exact round_step value inv.value
    obtain cnext : t.gpr .r9 = BitVec.ofNat 32 (n - (i + 1)) := by
      rw [count, inv.count]
      change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
      congr 1
    obtain znext : t.z = decide (i + 1 = n) := by
      rw [zeroFlag, inv.count]
      change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]),
        ofNat_beq_zero (by omega_using [hn32])]
      simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]
    obtain pnext : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * (i + 1)) := by
      rw [ptr, inv.ptr, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
      congr 1
    obtain next : LoopInv s base acc a b n m (i + 1) t :=
      ⟨by omega_using [hi], pnext, cnext, inv.outside.trans out, bound, vnext, inv.rest.trans rest⟩
    by_cases last : i + 1 = n
    · left
      refine ⟨?_, bound, ?_, next.outside, next.rest⟩
      · change some (!t.z) = some false
        simp only [znext, last, decide_true, Bool.not_true]
      · simpa only [last] using vnext
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, hik, hk, hi, last], by omega_using [hMn, hn, hn32, fa, fb, fm, ft, sa, sb, sm, hik, hk, hi, last], next⟩
      change some (!t.z) = some true
      simp only [znext, last, decide_false, Bool.not_false]
  refine WP.loop (M := isa) I step n s ?_
  refine ⟨0, by omega_using [], hn, ⟨by omega_using [], ?_, ?_, Outside.refl _ _ _ _, ?_, ?_, Rest.refl _ _⟩⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using pa
  · simpa only [Nat.sub_zero] using pc
  · rw [zero]; omega_using [operand]
  · rw [zero]; simp only [Nat.mul_zero, Nat.zero_mod, val32, Nat.zero_mul]

end VG.Proof.Mont.Arm.Packed

end

end

/-! ### `Mont.Arm.PackedExpand`, which only this module used -/

section

/-! Convert the packed accumulator to the existing reducer's digit format. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_str wp_movw mask16)

def expandSteps (acc dst k : Nat) : List Instr :=
  (List.range k).flatMap fun j => digitAt .r12 acc j ++ [.str .r7 .r12 (dst + 4 * j)]

 theorem expandSteps_ok {s : State} {base : Addr} {size acc dst n : Nat}
    (hs : Scr s base size) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (src : acc + 4 * ((n + 1) / 2) ≤ dst) (fit : dst + 4 * n ≤ size) :
    ∀ k, k ≤ n → WP isa (.block (expandSteps acc dst k)) s fun t =>
      Outside base dst (4 * k) s.mem t.mem ∧ Digs t.mem base dst k ∧
      dval t.mem base dst k = pval s.mem base acc k ∧ Rest [.r7] s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), rfl, Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    obtain eq : expandSteps acc dst (k + 1) = expandSteps acc dst k ++
        (digitAt .r12 acc k ++ [.str .r7 .r12 (dst + 4 * k)]) := by
      simp only [expandSteps, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (expandSteps_ok hs h6 src fit k (by omega_using [hk]))
      fun u ⟨out, digs, val, rest⟩ => ?_
    obtain hu := hs.of_rest rest (by decide)
    refine digitAt_ok hu (K := 0) (by simp) (Nat.zero_add _)
      (by rw [rest.gpr _ (by decide)]; exact h6) (by omega_using [src, fit, hk]) fun v uv => ?_
    obtain hv := hu.of_rest (uv.rest (ws := [.r7]) (by simp)) (by decide)
    refine wp_str (hv.off_lt (by omega_using [fit, hk])) (hv.ea (by omega_using [fit, hk])) (hv.write (by omega_using [fit, hk])) fun t vt => WP.block_nil ?_
    obtain old : pdig u.mem base acc k = pdig s.mem base acc k := by
      unfold pdig hdig
      rw [out.w32 (by omega_using [src, hk]) (by omega_using [src, fit, hk, hn])]
    obtain pdlt : pdig s.mem base acc k < 2 ^ 16 := hdig_lt _ _
    obtain mem : t.mem = u.mem.writeW (off base (dst + 4 * k)) (BitVec.ofNat 32 (pdig s.mem base acc k)) := by
      rw [vt.mem, uv.mem, uv.gpr, old]
    obtain wr := writeW32_outside u.mem base (d := dst + 4 * k)
      (BitVec.ofNat 32 (pdig s.mem base acc k)) (by omega_using [fit, hk, hn])
    rw [← mem] at wr
    obtain low := wr.dval (d := dst) (k := k) (by omega_using []) (by omega_using [fit, hk, hn])
    obtain top : w32 t.mem base (dst + 4 * k) = pdig s.mem base acc k := by
      rw [mem, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [pdlt])]
    refine ⟨(out.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using [])), ?_, ?_,
      rest.trans ((uv.rest (by simp)).trans (vt.rest _))⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wr.w32 (by omega_using [hj]) (by omega_arith)]; exact digs j hj
      · rw [top]; exact pdlt
    · rw [dval, low, top, val, pval]

 theorem expand_ok {s : State} {base : Addr} {size acc dst n : Nat}
    (hs : Scr s base size) (src : acc + 4 * ((n + 1) / 2) ≤ dst) (fit : dst + 4 * n ≤ size) :
    WP isa (.block (expand acc dst n)) s fun t =>
      Outside base dst (4 * n) s.mem t.mem ∧ Digs t.mem base dst n ∧
      dval t.mem base dst n = pval s.mem base acc n ∧ Rest [.r6, .r7] s t := by
  simp only [expand, List.cons_append, List.nil_append]
  refine wp_movw fun u uu => ?_
  refine WP.mono (expandSteps_ok (hs.of_rest (uu.rest (ws := [.r6, .r7]) (by simp)) (by decide))
    uu.gpr src fit n (Nat.le_refl _)) fun t ⟨out, digs, val, keep⟩ => ?_
  rw [uu.mem] at out val
  exact ⟨out, digs, val, (uu.rest (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Mont.Arm.Packed

end

end


/-! Packed Montgomery multiplication under the existing curve operation contract. -/

set_option exponentiation.threshold 1024

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

 theorem pval_extended {mem : Mem} {base : Addr} {acc n : Nat}
    (bound : val32 mem base acc (n + 2) < 2 ^ (32 * n) * 2) :
    pval mem base acc (2 * n + 1) = val32 mem base acc (n + 2) := by
  obtain whole := val32_append mem base acc n 2
  obtain top : val32 mem base (acc + 4 * n) 2 < 2 := by
    rw [whole] at bound
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bound)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at top
  obtain hzero : w32 mem base (acc + 4 * n + 4) = 0 := by omega_arith
  obtain hlo : w32 mem base (acc + 4 * n) < 65536 := by omega_arith
  rw [pval, pval_words, whole]
  simp only [pdig, hdig, show (2 * n) / 2 = n by omega_arith, show (2 * n) % 2 = 0 by omega_arith,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlo,
    show 16 * (2 * n) = 32 * n by omega_arith, val32, hzero, Nat.add_zero]
  rw [Nat.mul_comm]

 theorem val32_zeros {mem : Mem} {base : Addr} {acc : Nat} :
    ∀ k, (∀ j < k, w32 mem base (acc + 4 * j) = 0) → val32 mem base acc k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zeros k (fun j hj => h j (by omega_arith)), h k (by omega_arith), Nat.mul_zero, Nat.add_zero]

/-- Packed rows and the expanded half-word reducer fit inside the original
`32 * n + 8` byte accumulator. The word count must be a baseline immediate. -/
theorem mulR_ok (u : Bool) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m n : Nat}
    (hM : ModOkW M size m s.mem base) (hMn : M.n = n) (hn : 0 < n) (hn128 : n < 128)
    {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 a)
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (po : s.gpr .lr = s.gpr .r12 + BitVec.ofNat 32 o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (Impl.Mont.Arm.Packed.mulR M acc u) s fun t => OpKeep M base acc o s t ∧
      wordsVal t.mem base o M.n < m ∧
      wordsVal t.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have nowrap := hs.nowrap
  obtain hacc : accLen M = 32 * n + 8 := by
    simp only [accLen, Impl.Mont.Arm.digits, hMn]; omega_arith
  obtain facc := hL.acc_le; have fo := hL.o_le; have fa := hL.a_le; have fb := hL.b_le
  obtain sa := hL.acc_a; have sb := hL.acc_b; have sm := hL.acc_mo; have st := hL.acc_tmp; have so := hL.acc_o
  obtain fm := hM.mo; have ftmp := hM.tmp; have smt := hM.sep
  rw [hacc] at facc sa sb sm st so
  rw [hMn] at fo fa fb sa sb so fm ftmp smt
  obtain modval : val32 s.mem base M.mo (2 * n) = m := by
    have hv := hM.val
    rw [hMn, wordsVal_eq_val32] at hv
    exact hv
  obtain bval : val32 s.mem base b (2 * n) < m := by simpa only [wordsVal_eq_val32, hMn] using hB
  obtain mpos : 0 < m := by omega_arith
  unfold Impl.Mont.Arm.Packed.mulR
  simp only [hMn]
  refine WP.seq (zeros_ok hs (k := 2 * n + 2) (by omega_arith) fun s1 out1 zero1 keep1 => ?_)
  refine wp_mov (op2_imm (by
    simpa only [Impl.Mont.Arm.words, hMn] using words_encodable (M := M) (by omega_arith)))
    fun s2 u2 => WP.block_nil ?_
  obtain keep2 : Rest [.r7, .r9] s s2 := (keep1.mono (by simp)).trans (u2.rest (by simp))
  have mem2 : s2.mem = s1.mem := u2.mem
  obtain out2 : Outside base acc (8 * n + 8) s.mem s2.mem := by
    rw [mem2]; simpa [Nat.mul_add, ← Nat.mul_assoc] using out1
  obtain ctx2 := hs.of_rest keep2 (by decide)
  obtain pa2 : s2.gpr .r1 = s2.gpr .r12 + BitVec.ofNat 32 a := by
    rw [keep2.gpr .r1 (by decide), keep2.gpr .r12 (by decide)]; exact pa
  obtain pb2 : s2.gpr .r4 = s2.gpr .r12 + BitVec.ofNat 32 b := by
    rw [keep2.gpr .r4 (by decide), keep2.gpr .r12 (by decide)]; exact pb
  obtain mod2 : val32 s2.mem base M.mo (2 * n) = m := by rw [out2.val32 (by omega_arith) (by omega_arith)]; exact modval
  obtain b2 : val32 s2.mem base b (2 * n) < m := by rw [out2.val32 (by omega_arith) (by omega_arith)]; exact bval
  obtain z2 : val32 s2.mem base acc (2 * n + 2) = 0 := by
    rw [mem2]
    exact val32_zeros (2 * n + 2) zero1
  refine WP.seq (WP.mono (loop_ok u ctx2 (M := M) (n := 2 * n) (by rw [hMn]) (by omega_arith) (by omega_arith)
    pa2 pb2 u2.gpr (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) mod2 hM.inv b2 z2)
    fun s3 ⟨bound, value, out3, keep3⟩ => ?_)
  obtain keep : Rest roundClob s s3 := (keep2.mono (by simp)).trans keep3
  obtain out : Outside base acc (8 * n + 8) s.mem s3.mem :=
    out2.trans (by simpa [Nat.mul_add, ← Nat.mul_assoc] using out3)
  obtain oldA := out2.val32 (d := a) (k := 2 * n) (by omega_arith) (by omega_arith)
  obtain oldB := out2.val32 (d := b) (k := 2 * n) (by omega_arith) (by omega_arith)
  rw [oldA, oldB] at value
  obtain h3 := hs.of_rest keep (by decide)
  obtain mod3 : val32 s3.mem base M.mo (2 * n) = m := by rw [out.val32 (by omega_arith) (by omega_arith)]; exact modval
  obtain modBound : m < 2 ^ (32 * (2 * n)) := by rw [← modval]; exact val32_lt _ _ _ _
  obtain lowDigits : pval s3.mem base acc (4 * n + 1) = val32 s3.mem base acc (2 * n + 2) := by
    simpa [← Nat.mul_assoc] using
      pval_extended (mem := s3.mem) (base := base) (acc := acc) (n := 2 * n) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (expand_ok h3 (n := 4 * n + 1) (dst := acc + (8 * n + 8)) (by omega_arith) (by omega_arith))
    fun s4 ⟨out4, digs, digitsVal, keep4⟩ => ?_
  rw [lowDigits] at digitsVal
  obtain keep14 : Rest clob s s4 := keep.mono (by simp [clob]) |>.trans (keep4.mono (by simp [clob]))
  obtain h4 := hs.of_rest keep14 (by decide)
  obtain pout : s4.gpr .lr = s4.gpr .r12 + BitVec.ofNat 32 o := by
    rw [keep14.gpr .lr (by decide), keep14.gpr .r12 (by decide)]; exact po
  obtain mod4 : val32 s4.mem base M.mo (2 * n) = m := by rw [out4.val32 (by omega_arith) (by omega_arith)]; exact mod3
  refine WP.mono (csub_ok h4 (K := o) (d := 0) pout (Nat.add_zero _) (by decide)
    (by simp only [Impl.Mont.Arm.words, hMn]) (by simp only [Impl.Mont.Arm.digits, hMn]; omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by simpa [hMn, ← Nat.mul_assoc] using hL.o_tmp) mod4 mpos
    (by simpa [Nat.add_assoc, ← Nat.mul_assoc] using digs)
    (by simpa [Nat.add_assoc, ← Nat.mul_assoc] using digitsVal.symm ▸ bound)) fun t ⟨out5, reduced, keep5⟩ => ?_
  simp only [Nat.add_assoc, ← Nat.mul_assoc] at reduced
  rw [digitsVal] at reduced
  obtain kval : wordsVal t.mem base o n = val32 s3.mem base acc (2 * n + 2) % m := by
    rw [wordsVal_eq_val32]
    exact reduced
  refine ⟨⟨keep14.trans (keep5.mono (by simp [clob])), ?_⟩, ?_, ?_⟩
  · have all : Outside base acc (32 * n + 8) s.mem s4.mem :=
      (out.mono (Nat.le_refl _) (by omega_arith)).trans (out4.mono (by omega_arith) (by omega_arith))
    exact (Outs.of_outside all (by simp [hacc])).trans (out5.mono (by simp [hMn, hacc, ← Nat.mul_assoc]))
  · rw [kval]; exact Nat.mod_lt _ mpos
  · rw [kval, wordsVal_eq_val32, wordsVal_eq_val32]
    rw [Nat.mul_comm, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    simpa [← Nat.mul_assoc] using value

end VG.Proof.Mont.Arm.Packed

end

end


/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on 32-bit ARM

`fn n m op` (`Impl/Weierstrass/Arm/Mont.lean`), from a state `Pre n m`
(`ws`, `o`, `a` and `b` in `r0`–`r3`, the working space the only region, the
numbers below the own working space and the operands below `m`), runs the
entry (`entry_ok`): `r12 = ws`, the callee-saved registers saved, the
pointers to the numbers in `r1`, `r10` and `r11` (`Ptrs`) and the modulus
stored (`ModOkW`); then the operation, and the registers restored
(`fn_ok`). The function restores the callee-saved registers, keeps `sp` and
`lr` (`abiPreserved`), and changes the memory only at `[o]` and in its own
working space (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_reg dpVal)

/-- What the functions need of the modulus `m` of `n` words. -/
structure ModOk (n m : Nat) : Prop where
  n3 : 3 ≤ n
  n9 : n ≤ 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true

/-- The precondition, on the registers. -/
structure Pre (n m : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨State.addr (s.gpr .r0), 8192⟩]
  fit : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32
  o : (s.gpr .r1).toNat + 8 * n ≤ own n
  a : (s.gpr .r2).toNat + 8 * n ≤ own n
  b : (s.gpr .r3).toNat + 8 * n ≤ own n

/-- The memory changes only at `[o]` and in the own working space. -/
def Kept (n : Nat) (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  Outs base [(o, 8 * n), (own n, 64 * n)] m m'

theorem own_le (n : Nat) (h : n ≤ 9) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_using [h]

theorem saves_off (n : Nat) : ∀ p ∈ saves n, saveAt n ≤ p.2 ∧ p.2 + 4 ≤ saveAt n + 32 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have : q.2 + 4 ≤ 32 := (by decide : ∀ q ∈ savedRegs, q.2 + 4 ≤ 32) q hq
  dsimp only; omega_using [this]

theorem saves_pairwise (n : Nat) : (saves n).Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  rw [saves, List.pairwise_map]
  exact List.Pairwise.imp (fun h => by dsimp only; omega_using [h])
    (by decide : savedRegs.Pairwise fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2)

theorem saves_regs (n : Nat) : (saves n).map Prod.fst = savedRegs.map Prod.fst := by
  rw [saves, List.map_map]; rfl

theorem saves_mem (n : Nat) {r : Reg} {d : Nat} (h : (r, d) ∈ savedRegs) : (r, saveAt n + d) ∈ saves n :=
  List.mem_map_of_mem (f := fun p : Reg × Nat => (p.1, saveAt n + p.2)) h

theorem saves_nodup (n : Nat) : ((saves n).map Prod.fst).Nodup := by rw [saves_regs]; decide

theorem saves_r12 (n : Nat) : ∀ p ∈ saves n, p.1 ≠ .r12 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (by decide : ∀ q ∈ savedRegs, q.1 ≠ .r12) q hq

/-- What the entry leaves, with `[b]` at `rb`: the working space, the
modulus, the pointers to the numbers, the registers saved, `r10` and `r11`
as they were, and the memory but the own working space unchanged. -/
structure Entered (n m : Nat) (rb : Reg) (s s₁ : State) : Prop where
  scr : Scr s₁ (State.addr (s.gpr .r0)) 4096
  mod : ModOkW (mod n m) 4096 m s₁.mem (State.addr (s.gpr .r0))
  r12 : s₁.gpr .r12 = s.gpr .r0
  ra : s₁.gpr .r1 = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r2).toNat
  rb : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r3).toNat
  ro : s₁.gpr .lr = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r1).toNat
  keep : ∀ r ∈ [Reg.r10, .r11], s₁.gpr r = s.gpr r
  saved : ∀ p ∈ saves n, s₁.mem.readW (off (State.addr (s.gpr .r0)) p.2) 32 = s.gpr p.1
  mem : Outs (State.addr (s.gpr .r0)) [(own n, 64 * n)] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

end VG.Proof.Weierstrass.Arm.Mont

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_reg dpVal)

/-- Changes within ranges are within any ranges that contain them. -/
theorem Outs.sub {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega_using [h1, h2, this]

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem sum_reg (x y : BitVec 32) : x + y = x + BitVec.ofNat 32 y.toNat := by simp

theorem entry_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s) {rb : Reg}
    (hrb : rb ∉ [.r1, .r3, .r10, .r11, .r12, .lr]) :
    WP isa (.block (entry n m rb)) s (Entered n m rb s) := by
  have hn3 := hM.n3
  have hn9 := hM.n9
  obtain hown := own_le n hn9
  have hfit := hp.fit
  simp only [entry, List.cons_append, List.append_assoc]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  obtain hs₁ : Scr s₁ (State.addr (s.gpr .r0)) 4096 := ⟨by rw [u₁.gpr], ⟨8192, by decide, by decide,
    by rw [u₁.wr, hp.wr]; simp⟩, by rw [VG.Proof.X25519.Arm.addr_toNat]; omega_using [hfit], by decide⟩
  -- The saves.
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ (saves n) (fun p hp' => by
    have := saves_off n p hp'; simp only [saveAt, moAt, tmpAt] at this; omega_using [hn3, hown, this]) (saves_pairwise n))
    fun s₂ ⟨K₂, O₂, V₂⟩ => ?_
  obtain hs₂ := hs₁.of_rest K₂ (by decide)
  -- The modulus.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₂ (o := moAt n) (n := n) (by
    simp only [moAt, tmpAt]; omega_using [hn3, hown]) hM.m_lt) fun s₃ ⟨V₃, K₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_rest K₃ (by decide)
  -- The pointers.
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  obtain hrb' : ∀ r ∈ [Reg.r1, .r3, .r10, .r11, .r12, .lr], rb ≠ r := fun r hr h => hrb (h ▸ hr)
  obtain hb1 : rb ≠ .r1 := hrb' .r1 (by simp)
  obtain hb10 : rb ≠ .r10 := hrb' .r10 (by simp)
  obtain hb11 : rb ≠ .r11 := hrb' .r11 (by simp)
  obtain hb12 : rb ≠ .r12 := hrb' .r12 (by simp)
  obtain hblr : rb ≠ .lr := hrb' .lr (by simp)
  obtain K₆ : Rest [.lr, .r1, rb] s₃ s₆ :=
    (u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  obtain g₃ : ∀ r, r ≠ .r12 → r ≠ .r4 → s₃.gpr r = s.gpr r := fun r h12 h4 => by
    rw [K₃.gpr _ (by simp [h4]), K₂.gpr _ (by simp), u₁.other _ h12]
  obtain w₃ : s₃.gpr .r12 = s.gpr .r0 := by rw [K₃.gpr _ (by decide), K₂.gpr _ (by simp), u₁.gpr]
  obtain w₆ : s₆.gpr .r12 = s.gpr .r0 := by rw [K₆.gpr _ (by simp [Ne.symm hb12]), w₃]
  obtain m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  refine ⟨hs₃.of_rest K₆ (by simp [Ne.symm hb12]), ⟨by simp only [mod]; omega_using [hn3],
    by simp only [mod, moAt, tmpAt]; omega_using [hn3, hown], by simp only [mod, tmpAt]; omega_using [hn3, hown],
    .inr (by simp only [mod, moAt]; omega_using []), by rw [m₆]; exact V₃,
    by rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv, hM.red⟩, w₆, ?_, ?_, ?_, fun r hr => ?_, fun p hp' => ?_, ?_,
    by rw [u₆.rd, u₅.rd, u₄.rd, K₃.rd, K₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, K₃.wr, K₂.wr, u₁.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, K₃.sp, K₂.sp, u₁.sp]⟩
  · rw [u₆.other _ hb1.symm, u₅.gpr, dpVal, w₆, u₄.other _ (by decide), w₃,
      u₄.other _ (by decide), g₃ _ (by decide) (by decide), sum_reg]
  · rw [u₆.gpr, dpVal, w₆, u₅.other _ (by decide), u₄.other _ (by decide), w₃, u₅.other _ (by decide),
      u₄.other _ (by decide), g₃ _ (by decide) (by decide), sum_reg]
  · rw [u₆.other _ hblr.symm, u₅.other _ (by decide), u₄.gpr, dpVal, w₆, w₃,
      g₃ _ (by decide) (by decide), sum_reg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [u₆.other _ hb10.symm, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide)]
    · rw [u₆.other _ hb11.symm, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide)]
  · have := saves_off n p hp'
    rw [← u₁.other p.1 (saves_r12 n p hp'), ← V₂ p hp', m₆]
    refine Mem.readW_congr fun i hi => O₃ _ ?_
    simp only [moAt, saveAt, tmpAt] at this ⊢
    rw [ofs_off _ (by omega_using [hown, this, hi])]
    omega_using [this]
  · have hsv : ∀ p ∈ saves n, own n ≤ p.2 ∧ p.2 + 4 ≤ own n + 64 * n := fun p hp' => by
      have := saves_off n p hp'; simp only [saveAt, moAt, tmpAt] at this; omega_using [hn3, this]
    rw [m₆]
    refine (Outs.sub (rs := (saves n).map fun p => (p.2, 4)) (m' := s₂.mem) ?_ ?_).trans
      (Outs.sub (rs := [(moAt n, 8 * n)]) ?_ ?_)
    · rw [← u₁.mem]; exact O₂
    · intro r hr
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_singleton_self _, (hsv p hp').1, (hsv p hp').2⟩
    · exact Outs.of_outside O₃ (List.mem_singleton_self _)
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, by simp only [moAt, tmpAt]; omega_using [], by simp only [moAt, tmpAt]; omega_using [hn3]⟩

/-- The function of an operation that, from the entry's state, keeps what
an operation keeps (`OpKeep`) and leaves memory satisfying `R`: the
callee-saved registers and `sp` are those of the entry (`r10` and `r11`
never change), `r12` is `ws`, the memory changed only at `[o]` and in the
own working space, and `R` holds. -/
theorem fn_ok {n m : Nat} (hM : ModOk n m) {rb : Reg} (hrb : rb ∉ [.r1, .r3, .r10, .r11, .r12, .lr])
    {op : Prog isa} {R : Mem → Prop} {s : State} (hp : Pre n m s)
    (hop : ∀ s₁, Entered n m rb s s₁ → WP isa op s₁ fun s₂ =>
      OpKeep (mod n m) (State.addr (s.gpr .r0)) (own n) (s.gpr .r1).toNat s₁ s₂ ∧ R s₂.mem) :
    WP isa (fn n m rb op) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧ R s'.mem ∧
      s'.gpr .r12 = s.gpr .r0 := by
  have hn3 := hM.n3
  have hn9 := hM.n9
  obtain hown := own_le n hn9
  have ho := hp.o
  refine WP.seq (WP.mono (entry_ok hM hp hrb) fun s₁ E => ?_)
  refine WP.seq (WP.mono (hop s₁ E) fun s₂ ⟨K, hR⟩ => ?_)
  obtain hs₂ := E.scr.of_rest K.rest (by decide)
  obtain hsv : ∀ p ∈ saves n, saveAt n ≤ p.2 ∧ p.2 + 4 ≤ saveAt n + 32 := saves_off n
  obtain hsa : saveAt n + 32 ≤ 4096 := by simp only [saveAt, moAt, tmpAt]; omega_using [hn3, hown]
  refine WP.mono (ldrs_ok hs₂ (saves n) (fun p hp' => by have := hsv p hp'; omega_using [hsa, this]) (saves_nodup n)
    (saves_r12 n)) fun s₃ ⟨M₃, K₃, V₃⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, by rw [M₃]; exact hR, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain hsave : ∀ p ∈ saves n, s₃.gpr p.1 = s.gpr p.1 := fun p hp' => by
      have := hsv p hp'
      rw [V₃ p hp', ← E.saved p hp']
      refine Unch.readW32 (VG.Proof.Weierstrass.Arm.Outs.unch K.mem) (fun w hw => ?_) (by omega_using [hsa, this])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [mod, saveAt, moAt, tmpAt, accLen, digits] at this hw ⊢
      rcases hw with rfl | rfl | rfl <;> dsimp only <;> omega_using [ho, this]
    obtain hkeep : ∀ r ∈ [Reg.r10, .r11], s₃.gpr r = s.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.keep _ (by simp)]
      · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.keep _ (by simp)]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (saves_mem n (by decide : (Reg.r4, 0) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r5, 4) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r6, 8) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r7, 12) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r8, 16) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r9, 20) ∈ savedRegs))
    · exact hkeep _ (by decide)
    · exact hkeep _ (by decide)
    · exact hsave _ (saves_mem n (by decide : (Reg.lr, 24) ∈ savedRegs))
  · rw [K₃.sp, K.rest.sp, E.sp]
  · rw [M₃]
    refine (Outs.sub (rs := [(own n, 64 * n)]) E.mem fun r hr => ?_).trans
      (Outs.sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp [mod]⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [mod, tmpAt]; omega_using [],
          by simp only [mod, tmpAt]; omega_using [hn3]⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _,
          by simp only [mod, accLen, digits]; omega_using [hn3]⟩
  · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.r12]

/-- The operations' layout: the numbers below the own working space, its
accumulator, temporary area and modulus apart. -/
theorem opLay {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s) :
    OpLay (mod n m) 4096 (own n) (s.gpr .r1).toNat (s.gpr .r2).toNat (s.gpr .r3).toNat := by
  obtain hown := own_le n hM.n9
  have := hM.n3; have := hp.o; have := hp.a; have := hp.b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mod, accLen, digits, moAt, tmpAt] <;> omega_arith

/-- The entry's numbers are those of `s`. -/
theorem Entered.val {n m : Nat} (hM : ModOk n m) {rb : Reg} {s s₁ : State} (E : Entered n m rb s s₁) {d : Nat}
    (hd : d + 8 * n ≤ own n) : wordsVal s₁.mem (State.addr (s.gpr .r0)) d n =
      wordsVal s.mem (State.addr (s.gpr .r0)) d n :=
  Outs.wordsVal E.mem (fun r hr => by rw [List.mem_singleton] at hr; subst hr; omega_using [hd])
    (by have := own_le n hM.n9; omega_using [hd, this])

/-- The pointers of the entry. -/
def Entered.ptrs {n m : Nat} {rb : Reg} {s s₁ : State} (E : Entered n m rb s s₁) :
    Ptrs s₁ .r1 rb .lr 0 0 0 (s.gpr .r2).toNat (s.gpr .r3).toNat (s.gpr .r1).toNat :=
  ⟨_, _, _, E.ra, E.rb, E.ro, rfl, rfl, rfl⟩

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn16_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (mulFn16 n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      (wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
    wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (mulR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.b]; exact hb)) fun s₂ ⟨K, V, C⟩ => ⟨K, V, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at C
  exact C

set_option exponentiation.threshold 1024 in
theorem mulFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (mulFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      (wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) ∧
      s'.gpr .r12 = s.gpr .r0 := by
  unfold mulFn
  split
  · rename_i hn
    refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m)
      hM (by decide) hp fun s1 e => ?_
    refine WP.mono (Packed.mulR_ok false e.scr e.mod rfl (by change 0 < n; omega_using [hn])
      (by change n < 128; omega_using [hn]) (opLay hM hp) e.ra e.rb e.ro
      (by change wordsVal _ _ _ n < m; rw [e.val hM hp.b]; exact hb)) fun t ⟨keep, bound, value⟩ => ?_
    have eq : (mod n m).n = n := rfl
    rw [eq, e.val hM hp.a, e.val hM hp.b] at value
    exact ⟨keep, bound, value⟩
  · exact mulFn16_ok hM hp hb

set_option exponentiation.threshold 1024 in
/-- `mulFn_ok` for `mulFnU`. -/
theorem mulFnU_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (mulFnU n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      (wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
    wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m)
    hM (by decide) hp fun s1 e => ?_
  have := hM.n3; have := hM.n9
  refine WP.mono (Packed.mulR_ok true e.scr e.mod rfl (by change 0 < n; omega_arith)
    (by change n < 128; omega_using [this]) (opLay hM hp) e.ra e.rb e.ro
    (by change wordsVal _ _ _ n < m; rw [e.val hM hp.b]; exact hb)) fun t ⟨keep, bound, value⟩ => ?_
  have eq : (mod n m).n = n := rfl
  rw [eq, e.val hM hp.a, e.val hM hp.b] at value
  exact ⟨keep, bound, value⟩

/-- `mulFn_ok` for `mulFnWith u`. -/
theorem mulFnWith_ok (u : Bool) {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (mulFnWith u n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      (wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) ∧
      s'.gpr .r12 = s.gpr .r0 := by
  cases u
  · exact mulFn_ok hM hp hb
  · exact mulFnU_ok hM hp hb

/-- `vg_<curve>_add_mod_<p|n>`: `[o] = [a] + [b] mod m`. -/
theorem addFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hab : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < 2 * m) :
    WP isa (addFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
        (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
    (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (addR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n + wordsVal _ _ _ n < 2 * m; rw [E.val hM hp.a, E.val hM hp.b]
        exact hab)) fun s₂ ⟨K, V⟩ => ⟨K, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at V
  exact V

/-- `vg_<curve>_sub_mod_<p|n>`: `[o] = [a] - [b] mod m`. -/
theorem subFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (ha : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n < m)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (subFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
        (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n + m -
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
    (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n + m -
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (subR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.a]; exact ha)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.b]; exact hb)) fun s₂ ⟨K, V⟩ => ⟨K, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at V
  exact V

end VG.Proof.Weierstrass.Arm.Mont
