module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA public-key operation on PPC64LE: loading `pre`

`copyIn_ok`: `w` words of a read-only buffer apart from the working space
into it.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- A word of a buffer apart from the working space, unchanged by writes to
it. -/
theorem Outside.word_apart {B P : Addr} {Z Zp o n : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hsep : ∀ x, ofs P x < Zp → Z ≤ ofs B x) (hn : o + n ≤ Z) {d : Nat} (hd : d + 8 ≤ Zp)
    (hP : P.toNat + Zp ≤ 2 ^ 64) : word m' P d = word m P d :=
  Mem.readW_congr fun i hi => h _ (Or.inr (Nat.le_trans hn
    (hsep _ (by rw [ofs_off P (d := d) (i := i) (by omega)]; omega))))

/-- `copyWords`, `w` words from `dS` of `P` (`r15`), readable and apart from
the working space, to `dD` of the working space (`r14`), with `2 w` in `r11`. -/
theorem copyIn_ok {s : State} {B P : Addr} {Z Zp dS dD w : Nat} (hs : Scr s B Z)
    (hP : P.toNat + Zp ≤ 2 ^ 64) (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off P (dS + 8 * i)) 8)
    (h15 : s.gpr .r15 = off P dS) (h14 : s.gpr .r14 = off B dD) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS : dS + 8 * w ≤ Zp) (hD : dD + 8 * w ≤ Z)
    (hsep : ∀ x, ofs P x < Zp → Z ≤ ofs B x) :
    WP isa Precompute.copyWords s fun t =>
      (t.gpr .r14 = off B (dD + 8 * w) ∧ t.gpr .r15 = off P (dS + 8 * w) ∧
        (∀ i < w, word t.mem B (dD + 8 * i) = word s.mem P (dS + 8 * i)) ∧
        Outside B dD (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  unfold Precompute.copyWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dD + 8 * i) ∧ t.gpr .r15 = off P (dS + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dD + 8 * k) = word s.mem P (dS + 8 * k)) ∧ Keep [.r0, .r14, .r15, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8,
      .addi .r15 .r15 8] ++ ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j15, jout, jc, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), h14]; rfl, by rw [k₁.gpr .r15 (by decide), h15]; rfl,
      by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega), k₁.mono⟩ i17)
    fun t ⟨t14, t15, tout, tc, tk⟩ => ⟨⟨t14, t15, tc, tout⟩, tk⟩
  have hsrc : word t.mem P (dS + 8 * i) = word s.mem P (dS + 8 * i) :=
    Outside.word_apart jout hsep (by omega) (by omega) hP
  have hst : WP isa (.block [.load .d .r0 .r15 0, .store .d .r0 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8,
      .subi .r17 .r17 1]) t
      fun t' => t' = ((({ (t.write .r0 (word t.mem P (dS + 8 * i))) with
        mem := t.mem.writeW (off B (dD + 8 * i)) (word t.mem P (dS + 8 * i)) } :
        State).write .r14 (off B (dD + 8 * i + 8))).write .r15
          (off P (dS + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
    prun [j14, j15, (by rw [jk.rd, jk.wr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off P (dS + 8 * i)) 8),
      (hs.congr jk.wr).st (show dD + 8 * i + 8 ≤ Z by omega)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw := writeW_outside t.mem B (d := dD + 8 * i) (word t.mem P (dS + 8 * i)) (by omega)
  refine ⟨⟨by gsimp; rw [show dD + 8 * i + 8 = dD + 8 * (i + 1) by omega],
    by gsimp; rw [show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jc k hk
    · rw [word_writeW_self, hsrc]
  · exact jk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

/-- `copyPre`: `pre`'s `2 w` words (`r5`) into arrays 0 and 1. -/
theorem copyPre_ok {s : State} {B P : Addr} {Z w : Nat} (hs : Scr s B Z) (hP : P.toNat + 16 * w ≤ 2 ^ 64)
    (hrd : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8) (h5 : s.gpr .r5 = off P 0)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hsep : ∀ x, ofs P x < 16 * w → Z ≤ ofs B x) :
    WP isa copyPre s fun t =>
      ((∀ i < w, word t.mem B (slot w 0 + 8 * i) = word s.mem P (8 * i)) ∧
        (∀ i < w, word t.mem B (slot w 1 + 8 * i) = word s.mem P (8 * w + 8 * i)) ∧
        Outside B (slot w 0) (16 * (w + 1)) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  unfold copyPre
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun s₁ => s₁.gpr .r14 = off B (slot w 0) ∧
    s₁.gpr .r15 = off P 0 ∧ s₁.mem = s.mem) (by prun [h10, h5, BitVec.add_zero]) (by decide))
    fun s₁ ⟨⟨a14, a15, m1⟩, k1⟩ => ?_
  refine WP.seq (WP.mono (copyIn_ok (dS := 0) (dD := slot w 0) (hs.congr k1.wr) hP
    (fun i hi => by rw [k1.rd, k1.wr, Nat.zero_add]; exact hrd i (by omega)) a15 a14
    ((k1.gpr _ (by decide)).trans h11) hw hw' (by omega) (by omega) hsep)
    fun s₂ ⟨⟨b14, b15, bw, bout⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₃ => s₃.gpr .r14 = off B (slot w 1) ∧ s₃.mem = s₂.mem)
    (by prun [(k12.gpr .r10 (by decide)).trans h10, (k12.gpr .r29 (by decide)).trans h29, off_add]
        congr 1; omega) (by decide))
    fun s₃ ⟨⟨c14, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (copyIn_ok (dS := 0 + 8 * w) (dD := slot w 1) (hs.congr k13.wr) hP
    (fun i hi => by rw [k13.rd, k13.wr, show 0 + 8 * w + 8 * i = 8 * (w + i) by omega]; exact hrd _ (by omega))
    ((k3.gpr _ (by decide)).trans b15) c14 ((k13.gpr _ (by decide)).trans h11) hw hw' (by omega) (by omega)
    hsep) fun t ⟨⟨_, _, tw, tout⟩, k4⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, (k13.trans k4).mono⟩
  · rw [tout.word (by omega) (by omega), m3, bw i hi, m1, Nat.zero_add]
  · rw [tw i hi, m3, Outside.word_apart bout hsep (by omega) (by omega) hP, m1, Nat.zero_add]
  · rw [m1] at bout
    rw [m3] at tout
    exact (bout.mono (by omega) (by omega)).trans (tout.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE.Pub
