module

public import VerifiedGarbage.Proof.Mont.Arm.PackedStep
import VerifiedGarbage.Proof.Mont.Arm.PackedProduct
import VerifiedGarbage.Proof.Bignum.Arm.RowFull
import VerifiedGarbage.Proof.Framework.PlainSimp

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
    have eq : steps acc rb d (k + 1) = steps acc rb d k ++ step acc rb d k := by
      simp only [steps, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (steps_ok hs hp hd hrb ha hb sep x lo hi k (by omega))
      fun u ⟨out, val, rest⟩ => ?_
    have hu := hs.of_rest rest (by decide)
    have pu : u.gpr rb = u.gpr .r12 + BitVec.ofNat 32 K := by
      rw [rest.gpr _ hrb, rest.gpr _ (by decide)]; exact hp
    refine WP.mono (step_ok hu pu hd (by omega) (by omega) x
      (by rw [rest.gpr _ (by decide)]; exact lo)
      (by rw [rest.gpr _ (by decide)]; exact hi)) fun t ⟨mem, value, keep⟩ => ?_
    have oldA := out.w32 (d := acc + 4 * k) (by omega) (by omega)
    have oldB := out.w32 (d := src + 4 * k) (by omega) (by omega)
    rw [oldA, oldB] at value
    have wr := writeW32_outside u.mem base (d := acc + 4 * k) (t.gpr .r5) (by omega)
    rw [← mem] at wr
    have low := wr.val32 (d := acc) (k := k) (by omega) (by omega)
    have top : w32 t.mem base (acc + 4 * k) = (t.gpr .r5).toNat := by rw [mem, w32_write_self]
    refine ⟨(out.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_, rest.trans keep⟩
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
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (by omega)) fun s1 u1 => ?_
  have hs1 := hs.of_rest (u1.rest (ws := [.r5, .r6]) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs1.ea (by omega)) (hs1.read (by omega)) fun s2 u2 => ?_
  have a5 : s2.gpr .r5 = s.mem.readW (off base (acc + 4 * n)) 32 := by rw [u2.other _ (by decide), u1.gpr]
  have a6 : s2.gpr .r6 = s.mem.readW (off base (acc + 4 * n + 4)) 32 := by rw [u2.gpr, u1.mem]
  have a3 : s2.gpr .r3 = s.gpr .r3 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have k2 : Rest [.r5, .r6] s s2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  refine VG.Proof.X25519.Arm.WP.append (addWord_ok s2 .r3 (by
    rw [a5, a6, a3]; simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using fit))
    fun s3 ⟨value, frame⟩ => ?_
  have k3 := k2.trans (frame_rest frame)
  have hs3 := hs.of_rest k3 (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs3.ea (by omega)) (hs3.write (by omega)) fun s4 u4 => ?_
  have hs4 := hs3.of_rest (u4.rest []) (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs4.ea (by omega)) (hs4.write (by omega)) fun t u5 => WP.block_nil ?_
  have mem : t.mem = (s.mem.writeW (off base (acc + 4 * n)) (s3.gpr .r5)).writeW
      (off base (acc + 4 * n + 4)) (s3.gpr .r6) := by
    rw [u5.mem, u4.mem, u4.gpr, frame.mem, u2.mem, u1.mem]
  have w1 := writeW32_outside s.mem base (d := acc + 4 * n) (s3.gpr .r5) (by omega)
  have w2 := writeW32_outside (s.mem.writeW (off base (acc + 4 * n)) (s3.gpr .r5)) base
    (d := acc + 4 * n + 4) (s3.gpr .r6) (by omega)
  rw [← mem] at w2
  have outside : Outside base (acc + 4 * n) 8 s.mem t.mem :=
    (w1.mono (by omega) (by omega)).trans (w2.mono (by omega) (by omega))
  have low := outside.val32 (d := acc) (k := n) (by omega) (by omega)
  have top0 : w32 t.mem base (acc + 4 * n) = (s3.gpr .r5).toNat := by
    rw [mem, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self]
  have top1 : w32 t.mem base (acc + 4 * n + 4) = (s3.gpr .r6).toNat := by rw [mem, w32_write_self]
  have vtop : (s3.gpr .r5).toNat + 2 ^ 32 * (s3.gpr .r6).toNat =
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
  have k4 : Rest rowClob s s4 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have p4 : s4.gpr rb = s4.gpr .r12 + BitVec.ofNat 32 K := by
    rw [k4.gpr _ hrb, k4.gpr _ (by decide)]; exact hp
  have lo : (s4.gpr .r2).toNat = (s.gpr .r2).toNat % 65536 := by
    rw [u4.other _ (by decide), u3.gpr, u2.gpr, u1.other _ (by decide), low_half]
  have hi : (s4.gpr .r0).toNat = (s.gpr .r2).toNat / 65536 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, VG.Proof.X25519.Arm.toNat_shr]
  change WP isa (.block (steps acc rb d n ++ carry acc n)) s4 _
  refine VG.Proof.X25519.Arm.WP.append (steps_ok (hs.of_rest k4 (by decide)) p4 hd
    (fun h => hrb ((by decide : ∀ r ∈ stepClob, r ∈ rowClob) rb h)) (by omega) hb (by omega)
    (s.gpr .r2) lo hi n (Nat.le_refl _)) fun u ⟨outside, value, rest⟩ => ?_
  have tops := outside.val32 (d := acc + 4 * n) (k := 2) (by omega) (by omega)
  rw [u4.gpr, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, m4] at value
  have total : val32 u.mem base acc n + 2 ^ (32 * n) *
      (val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat) =
      val32 s.mem base acc (n + 2) + (s.gpr .r2).toNat * val32 s.mem base src n := by
    rw [tops, m4, val32_append s.mem base acc n 2]
    generalize 2 ^ (32 * n) = P at *
    grind
  have topfit : val32 u.mem base (acc + 4 * n) 2 + (u.gpr .r3).toNat < 2 ^ 64 := by
    rw [← total, VG.Proof.Bignum.Arm.pow32_addtwo] at fit
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) fit)
  have k : Rest rowClob s u := k4.trans (rest.mono (by simp))
  refine WP.mono (carry_ok (hs.of_rest k (by decide)) ha topfit) fun t ⟨out, val, keep⟩ => ?_
  refine ⟨by rw [val]; exact total, ?_, k.trans (keep.mono (by simp))⟩
  rw [m4] at outside
  exact (outside.mono (Nat.le_refl _) (by omega)).trans (out.mono (by omega) (by omega))

end VG.Proof.Mont.Arm.Packed
