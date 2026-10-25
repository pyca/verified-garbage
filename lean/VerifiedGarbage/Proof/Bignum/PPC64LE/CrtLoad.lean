module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: loading

`onesWords_ok`: `w` words of all ones (`M = 2^(64 w) - 1`). `loadArr_ok`: a
buffer's bytes, most significant first, into array `j`, its word `w` zeroed.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `w` words of all ones are `2^(64 w) - 1`. -/
theorem wv_ones {m : Mem} {p : Addr} {d : Nat} : ∀ {n : Nat},
    (∀ i < n, word m p (d + 8 * i) = BitVec.allOnes 64) → wv m p d n = 2 ^ (64 * n) - 1
  | 0, _ => rfl
  | n + 1, h => by
    rw [wv, wv_ones fun i hi => h i (by omega_arith), h n (by omega_arith), BitVec.toNat_allOnes, pow64_succ]
    have := Nat.one_le_two_pow (n := 64 * n)
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega_arith

/-- `onesWords`, `r14` at offset `d` of `B`: the `w` words there := all ones. -/
theorem onesWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B d) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa onesWords s fun s' =>
      ((∀ i < w, word s'.mem B (d + 8 * i) = BitVec.allOnes 64) ∧ Outside B d (8 * w) s.mem s'.mem) ∧
        Keep [.r0, .r3, .r14, .r17] s s' := by
  have hnw := hs.nowrap
  unfold onesWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1, .li .r0 0, .li .r3 1, .sub .r0 .r0 .r3]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.gpr .r0 = BitVec.allOnes 64 ∧ s₁.gpr .r14 = off B d ∧
        s₁.mem = s.mem) ∧ Keep [.r0, .r3, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11, h14]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i17, i0, i14, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (d + 8 * i) ∧ t.gpr .r0 = BitVec.allOnes 64 ∧ Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (d + 8 * k) = BitVec.allOnes 64) ∧ Keep [.r0, .r3, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁.mono⟩ i17) fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (d + 8 * i)) (BitVec.allOnes 64) } : State).write
        .r14 (off B (d + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [j14, j0, (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := d + 8 * i) (BitVec.allOnes 64) (by omega_arith)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · exact word_writeW_self _ _ _ _
  · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)

/-- `loadArr j`: the `k` bytes at `X` (`r12`, `r6`), most significant first,
into array `j`, and its word `w` := 0; `r10` back to array 0 (`r21`). -/
theorem loadArr_ok {s : State} {B X : Addr} {Z w k j : Nat} (hs : Scr s B Z) (hj : j < 8)
    (h12 : s.gpr .r12 = off X 0) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off X i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) :
    WP isa (loadArr j) s fun t =>
      (Mont.val32 t.mem B (slot w j) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem X k) ∧
        word t.mem B (slot w j + 8 * w) = 0 ∧ Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r10, .r14, .r15, .r16, .r17] s t := by
  have hnw := hs.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le hj) hZ
  have hh : hdrBytes = 256 := rfl
  have h1 : 256 ≤ slot w j := by unfold slot; omega_arith
  unfold loadArr
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) h10 h29 j)
    fun s₁ ⟨⟨a10, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k1.wr) a10
    ((k1.gpr _ (by decide)).trans h12) ((k1.gpr _ (by decide)).trans h6) ((k1.gpr _ (by decide)).trans h11)
    hk hkw hw' (by omega_arith) (by omega_arith) (by rw [k1.rd, k1.wr]; exact hrd)
    (by intro i hi x hx; exact hsep i hi x hx)) fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m1] at hv out₃
  have k13 := k1.trans k3
  refine WP.mono (WP.keep [.r14, .r0, .r10] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ t.gpr .r10 = off B (slot w 0))
    ?_ (by decide)) fun t ⟨⟨tm, t10⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t10⟩, (k13.trans k4).mono⟩
  · have a10' : s₃.gpr .r10 = off B (slot w j) := (k3.gpr _ (by decide)).trans a10
    have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith)]; congr 2
    prun [a10', (k13.gpr .r29 (by decide)).trans h29, (k13.gpr .r21 (by decide)).trans h21, off_add, e16,
      BitVec.add_zero, (hs.congr k13.wr).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith)]
    rfl
  · rw [tm, Mont.Outside.val32 (fun x hx => writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (out₃.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.Crt
