module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: `(c − 1) mod e`

The 64 bits of a word, from the top, into `r = r3 < e = r21`: `modBits_ok`,
`r := (r 2^64 + x) mod e` (by `modBit_ok` and `shift_step`); the words of a
number from the top, `r14` walking down and `r17` counting
(`modWords_ok`): the number mod `e`. As AArch64's
(`Proof/RsaKeyGen/AArch64/ModE.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate

theorem self_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- A word shifted left `i` bits, `y = (x mod 2^(k + 1)) 2^i` for `k + i = 63`:
its top bit, and itself doubled modulo `2^64`. -/
theorem shift1 (x k i : Nat) (hki : k + i = 63) :
    (x % 2 ^ (k + 1)) * 2 ^ i / 2 ^ 63 = x / 2 ^ k % 2 ∧
    2 * ((x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 64 = (x % 2 ^ k) * 2 ^ (i + 1) := by
  obtain ⟨hy, hb, hsh, -⟩ := VG.Proof.RsaKeyGen.shift_step x k i hki
  generalize (x % 2 ^ (k + 1)) * 2 ^ i = y at hy hb hsh ⊢
  refine ⟨?_, by rw [Nat.two_mul]; exact hsh⟩
  rw [← hb]
  by_cases h : 2 ^ 64 ≤ y + y
  · rw [decide_eq_true h]; show _ = 1; omega
  · rw [decide_eq_false h]; show _ = 0; omega

/-- The registers `modBits` writes. -/
def mbRegs : List Reg := [.r0, .r3, .r4, .r6, .r7, .r8, .r9, .r15, .r16]

/-- The 64 bits of the word `x` in `r7` into `r = r3 < e` (`r21`):
`(r 2^64 + x) mod e`. -/
theorem modBits_ok {s : State} (h6 : s.gpr .r6 = BitVec.ofNat 64 64)
    (hre : (s.gpr .r3).toNat < (s.gpr .r21).toNat) :
    WP isa (Impl.Bignum.PPC64LE.Precompute.countLoop .r6 modBit) s fun t =>
      (t.gpr .r3).toNat = ((s.gpr .r3).toNat * 2 ^ 64 + (s.gpr .r7).toNat) % (s.gpr .r21).toNat ∧
      t.mem = s.mem ∧ Keep mbRegs s t := by
  have he0 : 0 < (s.gpr .r21).toNat := by omega_using [hre]
  have hX := (s.gpr .r7).isLt
  have hE := (s.gpr .r21).isLt
  refine WP.mono (wp_countdown (cnt := .r6) (N := 64) (by decide) (by decide)
    (fun i t => (t.gpr .r3).toNat = ((s.gpr .r3).toNat * 2 ^ i + (s.gpr .r7).toNat / 2 ^ (64 - i)) %
        (s.gpr .r21).toNat ∧
      (t.gpr .r7).toNat = ((s.gpr .r7).toNat % 2 ^ (64 - i)) * 2 ^ i ∧ t.mem = s.mem ∧
      Keep mbRegs s t) ?_ ⟨?_, ?_, rfl, Keep.refl _ _⟩ h6) fun t ⟨hr, _, hm, k⟩ => ?_
  · intro i hi t ⟨hr, hd, hm, k⟩ _
    have h21 : t.gpr .r21 = s.gpr .r21 := k.gpr .r21 (by decide)
    have hacc : (t.gpr .r3).toNat < (t.gpr .r21).toNat := by rw [h21, hr]; exact Nat.mod_lt _ he0
    refine WP.block_append_iff.mpr (WP.mono (modBit_ok (acc := (t.gpr .r3).toNat) (x := (t.gpr .r7).toNat)
      (e := (t.gpr .r21).toNat) (self_ofNat _) (self_ofNat _) (self_ofNat _) hacc (t.gpr .r21).isLt (t.gpr .r7).isLt)
      fun t₁ ⟨⟨h1, h2, h21₁, m₁⟩, k₁⟩ => ?_)
    have hsub : WP isa (.block [.subi .r6 .r6 1]) t₁ fun t' =>
        (t'.gpr .r6 = t₁.gpr .r6 - BitVec.ofNat 64 1 ∧ t'.mem = t₁.mem) ∧ Keep [.r6] t₁ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h6', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
    · obtain ⟨_, _, _, hdiv⟩ := shift_step (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      obtain ⟨hbit, _⟩ := shift1 (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      rw [show 63 - i + 1 = 64 - i by omega_using [hi]] at hbit hdiv
      rw [k'.gpr .r3 (by decide), h1, h21, BitVec.toNat_ofNat, hd, hbit, hr,
        show 64 - (i + 1) = 63 - i by omega_using [], Nat.pow_succ,
        Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ he0) hE)]
      conv_rhs => rw [← hdiv]
      have hm2 : ∀ V b E : Nat, (2 * (V % E) + b) % E = (2 * V + b) % E := fun V b E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [hm2]
      congr 1
      have hb2 : (s.gpr .r7).toNat / 2 ^ (63 - i) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (s.gpr .r3).toNat = R
      generalize (s.gpr .r7).toNat / 2 ^ (64 - i) = Q
      generalize (s.gpr .r7).toNat / 2 ^ (63 - i) % 2 = b at hb2 ⊢
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm 2 (R * 2 ^ i), Nat.mul_assoc, Nat.mul_comm 2 Q]
      omega_using [hb2]
    · obtain ⟨_, hsh⟩ := shift1 (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      rw [show 63 - i + 1 = 64 - i by omega_using [hi]] at hsh
      rw [k'.gpr .r7 (by decide), h2, BitVec.toNat_ofNat, hd, show 64 - (i + 1) = 63 - i by omega_using [], hsh]
      exact Nat.mod_eq_of_lt (by rw [← hsh]; exact Nat.mod_lt _ (by decide))
    · exact ((k.trans k₁).trans k').mono (by decide)
    · rw [h6', k₁.gpr .r6 (by decide)]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hX, Nat.add_zero, Nat.mod_eq_of_lt hre]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hX]
  · refine ⟨?_, hm, k⟩
    rw [hr, Nat.sub_self, Nat.pow_zero, Nat.div_one]


/-- The words `m` to `w − 1` of the number at `d`. -/
abbrev hiw (mem : Mem) (B : Addr) (d w m : Nat) : Nat := wv mem B (d + 8 * m) (w - m)

theorem hiw_step (mem : Mem) (B : Addr) (d w m : Nat) (hm : m < w) :
    hiw mem B d w m = (word mem B (d + 8 * m)).toNat + 2 ^ 64 * hiw mem B d w (m + 1) := by
  unfold hiw
  rw [show w - m = 1 + (w - (m + 1)) by omega_using [hm], wv_add,
    show d + 8 * m + 8 * 1 = d + 8 * (m + 1) by omega_using []]
  simp [wv]

/-- One word: `r14` down a word, the word into `r7`, `r6 := 64`. -/
theorem modWordHead_ok {s : State} {B : Addr} {Z d k : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B (d + 8 * (k + 1))) (hd : d + 8 * (k + 1) ≤ Z) :
    WP isa (.block [.subi .r14 .r14 8, .load .d .r7 .r14 0, .li .r6 64]) s fun t =>
      (t.gpr .r14 = off B (d + 8 * k) ∧ t.gpr .r7 = word s.mem B (d + 8 * k) ∧
        t.gpr .r6 = BitVec.ofNat 64 64 ∧ t.mem = s.mem) ∧ Keep [.r14, .r7, .r6] s t := by
  have hn := hs.nowrap
  have ha : off B (d + 8 * (k + 1)) - BitVec.ofNat 64 8 = off B (d + 8 * k) := by
    rw [show d + 8 * (k + 1) = d + 8 * k + 8 by omega_using []]
    show B + BitVec.ofNat 64 (d + 8 * k + 8) - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 (d + 8 * k)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.keep _ ?_ (by decide)
  prun [h14, ha, hs.ld (d := d + 8 * k) (n := 8) (by omega_using [hd])]

/-- The registers `modWords` writes. -/
def mwRegs : List Reg := [.r0, .r3, .r4, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17]

/-- After `j` words of the loop from the top. -/
structure ModInv (s₀ : State) (B : Addr) (d w : Nat) (j : Nat) (t : State) : Prop where
  val : (t.gpr .r3).toNat = hiw s₀.mem B d w (w - j) % (s₀.gpr .r21).toNat
  r14 : t.gpr .r14 = off B (d + 8 * (w - j))
  mem : t.mem = s₀.mem
  keep : Keep mwRegs s₀ t

/-- The words of the number at `d`, from the top, into `r = r3 = 0` modulo
the `e > 1` in `r21`. -/
theorem modWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B (d + 8 * w))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z)
    (h3 : s.gpr .r3 = 0) (he : 1 < (s.gpr .r21).toNat) :
    WP isa (.loop (.seq (.block [.subi .r14 .r14 8, .load .d .r7 .r14 0, .li .r6 64])
      (.seq (Impl.Bignum.PPC64LE.Precompute.countLoop .r6 modBit) (.block [.subi .r17 .r17 1])))
      (.nonzero .d .r17)) s fun t =>
      (t.gpr .r3).toNat = wv s.mem B d w % (s.gpr .r21).toNat ∧ t.mem = s.mem ∧ Keep mwRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega_using [hw']) (by omega_using [hw]) (ModInv s B d w) ?_
    ⟨by rw [h3, Nat.sub_zero]; unfold hiw; rw [Nat.sub_self]; simp [wv], by rw [h14, Nat.sub_zero], rfl,
      Keep.refl _ _⟩ h17) fun t hI => ⟨?_, hI.mem, hI.keep⟩
  · intro j hj t hI _
    have t21 : t.gpr .r21 = s.gpr .r21 := hI.keep.gpr .r21 (by decide)
    refine WP.seq (WP.mono (modWordHead_ok (B := B) (Z := Z) (d := d) (k := w - (j + 1)) (hs.congr hI.keep.wr)
      (by rw [hI.r14, show w - (j + 1) + 1 = w - j by omega_using [hj]]) (by omega_using [hd, hj]))
      fun t₁ ⟨⟨h14₁, h7₁, h6₁, m₁⟩, k₁⟩ => ?_)
    have k01 := hI.keep.trans k₁
    have r21 : t₁.gpr .r21 = s.gpr .r21 := k01.gpr .r21 (by decide)
    have r3 : t₁.gpr .r3 = t.gpr .r3 := k₁.gpr .r3 (by decide)
    refine WP.seq (WP.mono (modBits_ok h6₁ (by rw [r21, r3, hI.val]; exact Nat.mod_lt _ (by omega_using [he])))
      fun t₂ ⟨h3₂, m₂, k₂⟩ => ?_)
    have hsub : WP isa (.block [.subi .r17 .r17 1]) t₂ fun t' =>
        (t'.gpr .r17 = t₂.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.mem = t₂.mem) ∧ Keep [.r17] t₂ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h17', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₂, m₁, hI.mem], ?_⟩, ?_⟩
    · rw [k'.gpr .r3 (by decide), h3₂, r21, r3, h7₁, hI.val, hI.mem,
        hiw_step s.mem B d w (w - (j + 1)) (by omega_using [hj]), show w - (j + 1) + 1 = w - j by omega_using [hj]]
      have hm2 : ∀ V x E : Nat, ((V % E) * 2 ^ 64 + x) % E = (x + 2 ^ 64 * V) % E := fun V x E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]
      exact hm2 _ _ _
    · rw [k'.gpr .r14 (by decide), k₂.gpr .r14 (by decide), h14₁]
    · exact ((k01.trans k₂).trans k').mono (by decide)
    · rw [h17', k₂.gpr .r17 (by decide), k₁.gpr .r17 (by decide)]
  · rw [hI.val, Nat.sub_self]; unfold hiw; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
