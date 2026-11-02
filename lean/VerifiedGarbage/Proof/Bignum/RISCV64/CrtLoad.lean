module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: loading `X`

* `onesWords_ok`: `w` words := all ones, so array 0 holds `M = 2^(64 w) - 1`.
* `loadArr_ok`: a number's bytes, most significant first, into array `j`
  (`Precompute.loadN`), its word `w` zero, and `a7` back to array 0.
* `loadX_ok`: `X`'s arrays from the header's pointers and lengths: `M` (0),
  `n` (1), `p` (4), `q` (5), the input (6) and `qInv` (7).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays)

/-! ## All ones -/

/-- `w` words all ones are `2^(64 w) - 1`. -/
theorem wordsVal_ones (m : Mem) (B : Addr) (d : Nat) :
    ∀ w, (∀ i < w, Mont.word m B (d + 8 * i) = BitVec.allOnes 64) → wordsVal m B d w = 2 ^ (64 * w) - 1
  | 0, _ => by simp [wordsVal]
  | w + 1, h => by
    rw [Mont.wordsVal_succ_top, wordsVal_ones m B d w fun i hi => h i (by omega_arith), h w (by omega_arith),
      BitVec.toNat_allOnes, Mont.pow64_succ]
    have := Nat.one_le_two_pow (n := 64 * w)
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    omega_arith

/-- `onesWords`, at `d` of `P` (`t3`) with `w` in `t0`: the `w` words := all
ones. -/
theorem onesWords_ok {s : State} {P : Addr} {Z d w : Nat} (hs : Scr s P Z)
    (h3 : s.gpr .t3 = Mont.off P d) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd8 : d % 8 = 0) (hZ : d + 8 * w ≤ Z) :
    WP isa onesWords s fun s' =>
      (wordsVal s'.mem P d w = 2 ^ (64 * w) - 1 ∧ Mont.Outside P d (8 * w) s.mem s'.mem) ∧
        Keep [.s0, .t3, .t5] s s' := by
  have hnw := hs.nowrap
  unfold onesWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0, .li .s0 (-1)]) s fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s0 = BitVec.allOnes 64 ∧ s₁.gpr .t3 = Mont.off P d ∧
        s₁.mem = s.mem) ∧ Keep [.s0, .t5] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, add_ofNat_zero, h0, h3, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i5, i0, i3, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = Mont.off P (d + 8 * i) ∧ t.gpr .s0 = BitVec.allOnes 64 ∧ Mont.Outside P d (8 * i) s.mem t.mem ∧
      (∀ k < i, Mont.word t.mem P (d + 8 * k) = BitVec.allOnes 64) ∧ Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .s0 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i0, by rw [← im]; exact Mont.Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono (by decide)⟩ i5) fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨wordsVal_ones _ _ _ w tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (Mont.off P (d + 8 * i)) (BitVec.allOnes 64) } : State).write
        .t3 (Mont.off P (d + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [add_ofNat_zero, j3, j0, (hs.congr jk.2.2).st (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show d + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := Mont.writeW_outside t.mem P (d := d + 8 * i) (BitVec.allOnes 64) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · exact Mont.word_writeW_self _ _ _ _
  · exact Keep.trans' jk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## A number into an array -/

/-- A byte buffer of `len` bytes at `X`: readable, apart from the working
space's `Z` bytes at `S`. -/
structure Buf (s : State) (S X : Addr) (Z len : Nat) : Prop where
  rd : ∀ i < len, InRegions (s.rd ++ s.wr) (Mont.off X i) 1
  sep : ∀ i < len, ∀ x, ofs S x < Z → Mont.off X i ≠ x

theorem Buf.congr {s t : State} {S X : Addr} {Z len : Nat} (h : Buf s S X Z len) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Buf t S X Z len := ⟨by rw [hrd, hwr]; exact h.rd, h.sep⟩

/-- `loadArr j`: the `k` bytes at `s7` (`k` in `s8`) into array `j`,
its Mont.word `w` := 0; `a7` back to array 0 (`ra`). -/
theorem loadArr_ok {s : State} {B X : Addr} {Z w k j : Nat} (hs : Scr s B Z) (hj8 : j < 8)
    (h7 : s.gpr .a7 = Mont.off B (slot w 0)) (hra : s.gpr .ra = Mont.off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hs7 : s.gpr .s7 = Mont.off X 0) (hs8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (hX : Buf s B X Z k) :
    WP isa (loadArr j) s fun t =>
      (wordsVal t.mem B (slot w j) w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X k) ∧
        Mont.word t.mem B (slot w j + 8 * w) = 0 ∧ Mont.Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .a7 = Mont.off B (slot w 0)) ∧
      Keep [.a0, .a7, .s0, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have ej := e j; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hj8' : slot w j + 8 * (w + 2) ≤ slot w 8 := VG.Proof.Bignum.slot_le hj8
  have alj : slot w j % 8 = 0 := slot_al w j
  unfold loadArr
  refine WP.seq (WP.mono (Pub.base_ok (rd := .a7) (by decide) h7 h5 j) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k1.2.2) a7'
    ((k1.gpr (by decide)).trans hs7) ((k1.gpr (by decide)).trans hs8) ((k1.gpr (by decide)).trans h0) hk hkw hw'
    (by omega_arith) alj (by omega_arith) (by rw [k1.2.1, k1.2.2]; exact hX.rd) hX.sep)
    fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m1] at hv out₃
  have k13 := k1.trans k3
  have a7'' : s₃.gpr .a7 = Mont.off B (slot w j) := (k3.gpr (by decide)).trans a7'
  have e16 : Mont.off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = Mont.off B (slot w j + 8 * w) := by
    rw [off_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith),
      show slot w j + 8 * (w + 2) - 16 = slot w j + 8 * w by omega_arith]
  refine WP.mono (WP.keep [.t3, .s0, .a7] (Q := fun t =>
    t.mem = s₃.mem.writeW (Mont.off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ t.gpr .a7 = Mont.off B (slot w 0))
    ?_ (by rfl) (by rfl)) fun t ⟨⟨tm, t7⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t7⟩, (k13.trans k4).mono (by decide)⟩
  · brun [a7'', (k13.gpr (r := .s5) (by decide)).trans h5, (k13.gpr (r := .ra) (by decide)).trans hra, off_add,
      e16, exec_li, add_ofNat_zero, (hs.congr k13.2.2).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith),
      (hs.congr k13.2.2).al8 (show slot w j + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  · rw [tm, Mont.Outside.wordsVal (fun x hx => Mont.writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact Mont.word_writeW_self _ _ _ _
  · rw [tm]
    exact (Mont.Outside.mono out₃ (Nat.le_refl _) (by omega_arith)).trans
      (Mont.Outside.mono (Mont.writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith)) (by omega_arith)
        (by omega_arith))

end VG.Proof.Bignum.RISCV64.Crt
