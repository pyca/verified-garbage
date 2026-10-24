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
    rw [wv, wv_ones fun i hi => h i (by omega), h n (by omega), BitVec.toNat_allOnes, pow64_succ]
    have := Nat.one_le_two_pow (n := 64 * n)
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega

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
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, i0, i14, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (d + 8 * i) ∧ t.gpr .r0 = BitVec.allOnes 64 ∧ Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (d + 8 * k) = BitVec.allOnes 64) ∧ Keep [.r0, .r3, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      k₁.mono⟩ i17) fun t ⟨_, _, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (d + 8 * i)) (BitVec.allOnes 64) } : State).write
        .r14 (off B (d + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [j14, j0, (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := d + 8 * i) (BitVec.allOnes 64) (by omega)
  refine ⟨⟨by gsimp; rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jz k hk
    · exact word_writeW_self _ _ _ _
  · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)

end VG.Proof.Bignum.PPC64LE.Crt
