module

public import VerifiedGarbage.Proof.Rsa.Arm.KdRun
public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Proof.Framework.Arm.Keep
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Bignum.WordStep32

/-! # The reciprocal of the key checks' division on ARMv7 (`KeyDiv.recip`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv
open VG.Proof.X25519.Arm (Rest)

theorem or_bits (c g : Bool) :
    ((0 : BitVec 32) + 0 + bif c then 1 else 0) ||| ((0 : BitVec 32) + 0 + bif g then 1 else 0) =
      bif c || g then 1 else 0 := by
  cases c <;> cases g <;> decide

theorem neg_bit_and (b : Bool) (x : BitVec 32) :
    (0 - bif b then (1 : BitVec 32) else 0) &&& x = bif b then x else 0 := by
  cases b
  · simp
  · show (0 - 1 : BitVec 32) &&& x = x
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]; exact BitVec.allOnes_and

theorem divBit_ok {s : State} {r d q n : Nat} (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 r) (h3 : s.gpr .r3 = BitVec.ofNat 32 q)
    (hl : s.gpr .lr = BitVec.ofNat 32 (n + 1)) (hr : r < d) (hd : d < 2 ^ 32) (hn : n + 1 < 2 ^ 32) :
    WP isa (.block divBit) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) ∧
      t.gpr .r3 = BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.z = (n == 0) ∧ t.gpr .r1 = s.gpr .r1 ∧ t.mem = s.mem := by
  krun [divBit, h1, h2, h3, hl]
  have er : (BitVec.ofNat 32 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega
  have ed : (BitVec.ofNat 32 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have eR : (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat = (2 * r + 1) % 2 ^ 32 := by
    simp only [BitVec.toNat_add, er, e1]; omega
  have hb : (decide (2 ^ 32 ≤ (BitVec.ofNat 32 r).toNat + (BitVec.ofNat 32 r).toNat) ||
      decide ((BitVec.ofNat 32 d).toNat ≤ (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat)) =
      decide (d ≤ 2 * r + 1) := by
    rw [er, ed, eR]
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.or_eq_true, decide_eq_true_eq]; omega
    · simp only [h, decide_false, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [or_bits, hb, neg_bit_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_sub, eR, ed, BitVec.toNat_ofNat]; omega
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_sub, eR, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat, e1]; omega
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · have : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [this]
    by_cases h : n = 0
    · subst h; rfl
    · have : (BitVec.ofNat 32 n == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e
        have := congrArg BitVec.toNat e; simp at this; omega
      rw [this]; simp [h]

def rdiv (d j : Nat) : Nat := (2 ^ 32 - 1 - d) * 2 ^ j + (2 ^ j - 1)

theorem rdiv_succ (d j : Nat) : rdiv d (j + 1) = 2 * rdiv d j + 1 := by
  unfold rdiv
  generalize 2 ^ 32 - 1 - d = K
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_assoc]
  have := Nat.one_le_two_pow (n := j)
  omega

/-- The loop of `recip`: from `r = 2^32 - 1 - d`, `q = 0` and the count 32,
`q = ⌊rdiv d 32 / d⌋`. -/
theorem recipLoop_ok {s : State} {d : Nat} (hd' : d < 2 ^ 32) (hd0 : 2 ^ 31 ≤ d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d)) (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 0) (hl : s.gpr .lr = BitVec.ofNat 32 32) :
    WP isa (.loop (.block divBit) .ne) s fun t => t.gpr .r3 = BitVec.ofNat 32 (rdiv d 32 / d) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ j q r, n = 32 - j ∧ j < 32 ∧ t.gpr .r2 = BitVec.ofNat 32 r ∧
      t.gpr .r3 = BitVec.ofNat 32 q ∧ t.gpr .r1 = BitVec.ofNat 32 d ∧ t.gpr .lr = BitVec.ofNat 32 (32 - j) ∧
      r < d ∧ rdiv d j = q * d + r ∧ t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t) ?_ _ s
    ⟨0, 0, 2 ^ 32 - 1 - d, rfl, by decide, h2, h3, h1, hl, by omega, by simp [rdiv], rfl,
      VG.Proof.X25519.Arm.Rest.refl _ _⟩
  rintro n t ⟨j, q, r, rfl, hj, h2', h3', h1', hl', hr, hP, hm, k⟩
  refine WP.mono (WP.keep [.r2, .r3, .r4, .r5, .lr]
    (divBit_ok (n := 31 - j) h1' h2' h3' (by rw [hl']; congr 1; omega) hr hd' (by omega)) (by decide))
    fun t' ⟨⟨e2, e3, el, ez, e1, hm'⟩, k'⟩ => ?_
  obtain ⟨hP', hr'⟩ := VG.Proof.Bignum.WordStep32.divBit_inv hP hr (show 1 < 2 by decide)
  rw [← rdiv_succ] at hP'
  have K := k.trans k'
  by_cases e : j + 1 = 32
  · refine .inl ⟨by simp only [eval, ez, show 31 - j = 0 by omega]; rfl, ?_, hm'.trans hm, K⟩
    have e32 : rdiv d 32 = (2 * q + if d ≤ 2 * r + 1 then 1 else 0) * d +
        (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by rw [show (32 : Nat) = j + 1 by omega]; exact hP'
    have key : ∀ Q R, R < d → (Q * d + R) / d = Q := fun Q R h' => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h', Nat.zero_add]
    rw [e3, e32, key _ _ hr']
  · refine .inr ⟨by simp only [eval, ez]; simp; omega, 32 - (j + 1), by omega,
      j + 1, _, _, rfl, by omega, e2, e3, by rw [e1]; exact h1', by rw [el]; congr 1; omega, hr', hP',
      hm'.trans hm, K⟩

open VG.Proof.Rsa.Arm.Keys VG.Proof.Mont in
/-- `recip`: `v = ⌊(2^64 - 1) / d⌋ - 2^32` at 144, for `d ≥ 2^31` at 140. -/
theorem recip_ok {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N)
    (hD : slot s.mem B sD = d) (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) :
    WP isa recip s fun t => slot t.mem B sV = (2 ^ 64 - 1) / d - 2 ^ 32 ∧ Keep B w [] [sV] s.mem t.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r5, .lr] s t := by
  have hz := h.hdr_le
  have aD := h.addr (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have rD := h.read (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have aV := h.addr (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have wV := h.write (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have vD : s.mem.readW (off (State.addr B) sD) 32 = BitVec.ofNat 32 d := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD
  have mvn : ~~~(BitVec.ofNat 32 d) = BitVec.ofNat 32 (2 ^ 32 - 1 - d) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [recip]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r1, .r2, .r3, .lr] (Q := fun u => u.gpr .r1 = BitVec.ofNat 32 d ∧
      u.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d) ∧ u.gpr .r3 = BitVec.ofNat 32 0 ∧
      u.gpr .lr = BitVec.ofNat 32 32 ∧ u.mem = s.mem) (by
    krun [h.r8, aD, rD, vD, mvn]
    exact ⟨rfl, rfl⟩) (by decide)) fun u ⟨⟨u1, u2, u3, ul, um⟩, ku⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (recipLoop_ok hd2 hd1 u2 u1 u3 ul) fun t ⟨t3, tm, kt⟩ => ?_
  have r8t : t.gpr .r8 = B := by rw [kt.gpr _ (by decide), ku.gpr _ (by decide), h.r8]
  have wt : InRegions t.wr (off (State.addr B) sV) 4 := by rw [kt.wr, ku.wr]; exact wV
  have hq : rdiv d 32 / d = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [← VG.Proof.Bignum.WordStep32.recip_eq hd2 (by omega)]; rfl
  have hv32 : (2 ^ 64 - 1) / d - 2 ^ 32 < 2 ^ 32 := by
    have : (2 ^ 64 - 1) / d < 2 ^ 33 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  refine WP.mono (WP.keep [] (Q := fun v => v.mem = t.mem.writeW (off (State.addr B) sV) (t.gpr .r3)) (by
    krun [r8t, aV, wt]) (by decide)) fun v ⟨vm, kv⟩ => ⟨?_, ?_, ?_⟩
  · rw [vm, slot_write_self, t3, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
  · rw [vm, tm, um]; exact keep_write _ _ (by simp) (by simp only [sV]; omega)
  · exact ((ku.mono (ws' := [.r1, .r2, .r3, .r4, .r5, .lr]) (by decide)).trans
      (kt.mono (by decide))).trans (kv.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv
