module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps

/-!
# `vg_rsa_crt_values` on PPC64LE: the setup of a valid modulus

`Base.of_keep`: a step that writes only the arrays and the slots after the
header's first 112 bytes keeps `Base`. `setup_ok`: `w = ⌈n_len / 4⌉`
(`n_len` in `r18`) and the stride into `r29` and `r30`, and every array
zeroed: the working space (`Ws`) with all its digits 0.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.CrtValues (setup nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot ranges)

theorem pre_ws {s0 : State} (h : cvP.pre s0) :
    arr (cvW s0) nArr ≤ cvZ s0 ∧ 16 ≤ cvW s0 ∧ cvW s0 ≤ 256 ∧ cvK s0 ≤ 4 * cvW s0 := by
  obtain ⟨-, -, hz, hk, hk'⟩ := pre_scr h
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr, cvW] at hz ⊢
  omega

/-- A step that writes only arrays and slots at 112 or after keeps `Base`. -/
theorem Base.of_keep {s0 s t : State} (h : Base s0 s) {js ds : List Nat}
    (k : KeyWorkspace.Keep (cvB s0) (cvW s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, 112 ≤ d ∧ d + 4 ≤ 160) (sp : t.sp = s.sp) (lr : t.lr = s.lr) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  obtain ⟨-, nw, -, -, -⟩ := pre_scr h.pre
  obtain ⟨fits, -, -, -⟩ := pre_ws h.pre
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]
    exact k.out (Z := cvZ s0) (fun j hj => Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (hjs j hj)) fits)
      (fun d hd => by have := hds d hd; have : 160 ≤ cvZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits; omega) hx
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine k _ fun r hr => ?_
    have h160 : 160 ≤ cvZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega)]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, -, rfl⟩ | ⟨d, hd, rfl⟩
    · left; simp only [arr, VG.Proof.Rsa.KeyWorkspace.hdr]; omega
    · left; have := hds d hd; dsimp only; omega

/-- A step that writes only bytes from 160 on, within the working space, keeps `Base`. -/
theorem Base.of_outside {s0 s t : State} (h : Base s0 s) {n : Nat}
    (o : Outside (cvB s0) 160 n s.mem t.mem) (hn : 160 + n ≤ cvZ s0) (sp : t.sp = s.sp) (lr : t.lr = s.lr)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  obtain ⟨-, nw, -, -, -⟩ := pre_scr h.pre
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]; exact o x (Or.inr (by omega))
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine o _ (Or.inl ?_)
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega)]
    omega

theorem ofNat_add3_shr2 (x : BitVec 64) (hx : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 3) >>> 2 = BitVec.ofNat 64 ((x.toNat + 3) / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_stride (w : Nat) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 2 = BitVec.ofNat 64 (S w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [S]
  omega

theorem ofNat_digits (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 25 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (25 * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S]
  rw [Nat.mod_eq_of_lt (show 25 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 25 * (w + 2) < 2 ^ 64 by omega)]
  omega

/-- `setup`: `w` and the stride, and every digit of the arrays 0. -/
theorem setup_ok {s0 s : State} (h : Base s0 s) (h18 : s.gpr .r18 = s0.gpr .r10) :
    WP isa setup s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      (∀ j < nArr, ∀ i < cvW s0 + 2, w32 t.mem (cvB s0) (arr (cvW s0) j + 4 * i) = 0) ∧
      Keep (.r29 :: .r30 :: opRegs) s t := by
  obtain ⟨hm, nw, hz, hk, hk'⟩ := pre_scr h.pre
  obtain ⟨fits, hw16, hw, -⟩ := pre_ws h.pre
  have hs : Scr s (cvB s0) (cvZ s0) := Scr.of_mem (by rw [h.wr]; exact hm) nw
  have hkv : (s0.gpr .r10).toNat ≤ 1024 := hk'
  rw [setup, WP.seq_iff]
  have hb : WP isa (.block ([.addi .r29 .r18 3, .lsr .d .r29 .r29 2] ++
      VG.Impl.Rsa.PPC64LE.Keys.stride ++ [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])) s fun u =>
        (u.gpr .r29 = BitVec.ofNat 64 (cvW s0) ∧ u.gpr .r30 = BitVec.ofNat 64 (S (cvW s0)) ∧
          u.gpr .r8 = BitVec.ofNat 64 (nArr * (cvW s0 + 2)) ∧ u.mem = s.mem) ∧ Keep [.r8, .r29, .r30] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [VG.Impl.Rsa.PPC64LE.Keys.stride, h18, ofNat_add3_shr2 _ hkv, ofNat_stride, ofNat_digits _ hw, nArr]
  refine WP.mono hb fun u ⟨⟨u29, u30, u8, um⟩, ku⟩ => ?_
  have hu : Ws u (cvB s0) (cvZ s0) (cvW s0) nArr :=
    ⟨hs.congr ku.wr, fits, by omega, hw, u29, u30, (ku.gpr _ (by decide)).trans h.r31⟩
  have hn : 160 + 4 * (nArr * (cvW s0 + 2)) ≤ cvZ s0 := by
    simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr] at fits ⊢; omega
  refine WP.mono (zeroArrays_ok hu u8 (by simp only [nArr]; omega) (by simp only [nArr]; omega) hn)
    fun t ⟨ht, z, out, kt⟩ => ⟨?_, ht, fun j hj i hi => ?_, (ku.trans kt).mono⟩
  · have kk := ku.trans kt
    exact Base.of_outside h (by rw [← um]; exact out) hn kk.sp kk.lr kk.rd kk.wr (kk.gpr _ (by decide))
  · have hb : j * (cvW s0 + 2) + i < nArr * (cvW s0 + 2) := by
      have := Nat.mul_le_mul_right (cvW s0 + 2) (show j + 1 ≤ nArr by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have := z (j * (cvW s0 + 2) + i) hb
    rw [show 160 + 4 * (j * (cvW s0 + 2) + i) = arr (cvW s0) j + 4 * i by
      simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
    exact this

end VG.Proof.Rsa.PPC64LE.CrtValues
